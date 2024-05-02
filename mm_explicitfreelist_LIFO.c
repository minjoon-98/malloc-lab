// 42 (util) + 40 (thru) = 82/100

/*
 * mm-naive.c - The fastest, least memory-efficient malloc package.
 *
 * In this naive approach, a block is allocated by simply incrementing
 * the brk pointer.  A block is pure payload. There are no headers or
 * footers.  Blocks are never coalesced or reused. Realloc is
 * implemented directly using mm_malloc and mm_free.
 *
 * NOTE TO STUDENTS: Replace this header comment with your own header
 * comment that gives a high level description of your solution.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*********************************************************
 * NOTE TO STUDENTS: Before you do anything else, please
 * provide your team information in the following struct.
 ********************************************************/
team_t team = {
    /* Team name */
    "team 3",
    /* First member's full name */
    "Minjoon Kim",
    /* First member's email address */
    "4kmj54321@gmail.com",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/* Basic constants and macros */ /* 기본 상수와 매크로 */
/* 기본 상수 */
#define WSIZE 4 /* Word and header/footer size (bytes) */                                   /* 워드와 헤더/풋터 크기 (바이트) */
#define DSIZE 8 /* Double word size (bytes) */                                              /* 더블 워드 크기 (바이트) */
#define CHUNKSIZE (1 << 12) /* Extend heap by this amount (bytes) */ /* 4096bytes -> 4KB */ // 힙 확장을 위한 기본 크기 (= 초기 빈 블록의 크기)

/* 매크로 */
#define MAX(x, y) ((x) > (y) ? (x) : (y)) // 두 값을 비교하여 더 큰 값을 반환

/* Pack a size and allocated bit into a word */ /* 크기와 할당 비트를 워드에 패킹 */
#define PACK(size, alloc) ((size) | (alloc))    // size와 allocated bit를 통합해서 header와 footer에 저장할 수 있는 값을 리턴한다.

/* Read and write a word at address p */                         /* 주소 p에서 워드를 읽고 쓰기 */
#define GET(p) (*(unsigned int *)(p))                            // p가 (void *) 포인터 일 수 있어서 역참조 불가. 캐스팅을 해줘야한다.
#define PUT(p, val) (*(unsigned int *)(p) = (unsigned int)(val)) // p가 가리키는 워드에 val저장
// p를 unsigned int *로 캐스팅 (unsigned int는 4byte) // int는 만 앞 값이 부호를 결정하는 값인데에 반해
// unsigned int는 양수만 존재. 따라서 맨 앞 정보를 부호의 정보로 사용하지 않고 주소 정보를 int에 비해 2배나 더 사용할 수 있음

/* Read the size and allocated fields from address p */ /* 주소 p에서 크기와 할당된 필드 읽기 */
#define GET_SIZE(p) (GET(p) & ~0x7)                     // 사이즈 (~0x7: ...11111000, '&' 연산으로 뒤에 세자리 없어짐)
#define GET_ALLOC(p) (GET(p) & 0x1)                     // 할당 상태

/* Given block ptr bp, compute address of its header and footer */ /* 블록 포인터 bp가 주어졌을 때, 헤더와 풋터의 주소 계산 */
#define HDRP(bp) ((char *)(bp)-WSIZE)                              // Header 포인터 // 한 byte단위로 조작하기 위해 (char *)로 선언
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE)       // Footer 포인터 (🚨Header의 정보를 참조해서 가져오기 때문에, Header의 정보를 변경했다면 변경된 위치의 Footer가 반환됨에 유의)
// unsigned int는 4byte로 이용할 수 있는데 정책을 바꾸거나 할 때, WSIZE 만 바꿔주면 내가 원하는 만큼 움직일 수 있기에 유지보수적 측면에서 이점이 있음

/* Given block ptr bp, compute address of next and previous blocks */ /* 블록 포인터 bp가 주어졌을 때, 다음과 이전 블록의 주소 계산 */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp)-WSIZE))) // 다음 블록의 포인터
#define PREV_BLKP(bp) ((char *)(bp)-GET_SIZE(((char *)(bp)-DSIZE)))   // 이전 블록의 포인터

/* accessing predecessor and successor pointers in the free list */
#define PRED_FREEP(bp) (*(void **)(bp))         // 가용 리스트에서 이전 블록을 가리키는 포인터
#define SUCC_FREEP(bp) (*(void **)(bp + WSIZE)) // 가용 리스트에서 다음 블록을 가리키는 포인터

/* Global variables */
static char *heap_listp = NULL; // Pointer to first block // 항상 prologue block을 가리키는 정적 전역 변수 설정
static char *free_listp = NULL; // Pointer to the beginning of the free list

int mm_init(void);
void *mm_malloc(size_t size);
void mm_free(void *bp);
void *mm_realloc(void *ptr, size_t size);

/* Function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

/* for explicit free list */
void add_freelist(void *bp);
void remove_freelist(void *bp);

/*
 * mm_init - initialize the malloc package.
   mm_init: creates a heap with an initial free block (최초 가용 블록으로 힙 생성하기)
 */

int mm_init(void)
{
    /* Create the initial empty heap */ /* padding, prol_header, prol_footer, PREC, SUCC, epil_header */
    // 초기 힙 생성 // 💡Explicit allocator의 초기 힙은 6word의 메모리를 가진다.
    if ((heap_listp = mem_sbrk(6 * WSIZE)) == (void *)-1) // /* 메모리에서 6word 가져오고 이걸로 빈 가용 리스트 초기화 */
        return -1;
    PUT(heap_listp, 0); /* Alignment padding */                                                        // 정렬 패딩
    PUT(heap_listp + (1 * WSIZE), PACK(4 * WSIZE, 1)); /* Prologue header */                           /* Initial Prologue block size, header, footer, PREC, SUCC */
    PUT(heap_listp + (2 * WSIZE), NULL); /* Predecessor pointer of the prologue block (set to NULL) */ // 프롤로그 PRED 포인터 NULL로 초기화
    PUT(heap_listp + (3 * WSIZE), NULL); /* Successor pointer of the prologue block (set to NULL) */   // 프롤로그 SUCC 포인터 NULL로 초기화
    PUT(heap_listp + (4 * WSIZE), PACK(4 * WSIZE, 1)); /* Prologue footer */                           // header, footer, PREC, SUCC 총 4워드 사이즈를 가짐
    PUT(heap_listp + (5 * WSIZE), PACK(0, 1)); /* Epilogue header */                                   // 프로그램이 할당한 마지막 블록의 뒤에 위치하며, 블록이 할당되지 않은 상태를 나타냄
    heap_listp += (2 * WSIZE);                                                                         // heap_listp를 프롤로그 블록 Header 다음으로 이동시킵니다.
    // 프롤로그 블록도 하나의 블록으로 간주, 따라서 내가 이해한 바로는 heap_listp는 가장 첫번째 블록 포인터로서 헤더 다음에 위치한다.
    // ex) 이를 통해 뒤에 나오는 first fit을 한다고 해도 프롤로그 블록의 헤더를 참조하여 사이즈를 알아낸다.
    // explicit free list에서는 PRED와 SUCC에 바로 접근 가능

    free_listp = heap_listp; // free_listp를 탐색의 시작점으로 둔다.

    /* Extend the empty heap with a free block of CHUNKSIZE bytes */ /* 빈 힙을 CHUNKSIZE 바이트의 가용 블록으로 확장 */
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;
    return 0;
}

static void *extend_heap(size_t words) /* 힙을 확장하는 함수. 힙 초기화나 mm_malloc이 맞는 적합 지점을 찾지 못했을 때 호출됨 */ // 두가지 경우에 사용. 1. 힙이 초기화될 때 2. mm_malloc이 적당한 맞춤 fit을 찾지 못했을 때
{
    char *bp; // 한 byte단위로 조작하기 위해 (char *)로 선언
    size_t size;
    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words + 1) * WSIZE : words * WSIZE; // 요청된 크기를 가장 가까운 2 워드(8바이트)의 배수로 올림
    // size = ALIGN(words * WSIZE);           // ALIGN 함수 사용
    if ((long)(bp = mem_sbrk(size)) == -1) // 메모리 할당 요청 및 오류 처리
        return NULL;

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0)); /* Free block header */           // 현재 블록의 헤더에 크기와 할당 여부 정보를 설정
    PUT(FTRP(bp), PACK(size, 0)); /* Free block footer */           // 현재 블록의 풋터에도 같은 정보 설정
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */ // 에필로그를 현재 블록 다음 블록의 헤더로 설정

    /* Coalesce if the previous block was free */
    return coalesce(bp); // 앞 블록이 비어 있다면 통합(coalesce) 수행하여 결과 반환
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size)
{
    size_t asize; /* Adjusted block size */                  // 조정된 블록 크기
    size_t extendsize; /* Amount to extend heap if no fit */ // 적합한 블록이 없을 경우 힙을 확장하는 양
    char *bp;                                                // 할당된 블록을 가리키는 포인터

    /* Ignore spurious requests */
    if (size <= 0)
        return NULL; // 크기가 0보다 작은 요청은 무시하고 NULL 반환

    /* Adjust block size to include overhead and alignment reqs. */
    if (size <= DSIZE)
        asize = 2 * DSIZE; // 요청된 크기가 DSIZE 이하인 경우, 최소 블록 크기인 2*DSIZE로 설정
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE); // 그렇지 않은 경우, 요구 크기에 오버헤드와 정렬 요구 사항을 포함하여 조정
    // size = (a * DSIZE) + b 로 표현할 수 있다. asize = DSIZE * ((a * DSIZE) + b + (DSIZE) + (DSIZE - 1)) / DSIZE)라고 식을 표현할 때, 실제로 값에 변동을 주는 값은 b + (DSIZE - 1)가 된다.
    // 만약 나머지 b가 존재하지 않는다면 모든 값이 나누어 떨어지게 되며 나머지는 (DSIZE - 1)가 되고, 이는 사라지는 값이 된다.
    // 하지만 나머지 b가 1이상으로 존재하게 된다면, b + (DSIZE - 1)에서 DSIZE로 나눈 몫이 1이 생기게 되어 1개만큼의 더블 워드 사이즈 칸을 할당하게 된다.

    /* Search the free list for a fit */
    if ((bp = find_fit(asize)) != NULL) // 가용한 블록을 찾음
    {
        place(bp, asize); // 찾은 블록을 할당하고 반환
        return bp;
    }

    /* No fit found. Get more memory and place the block */
    extendsize = MAX(asize, CHUNKSIZE);                 // 필요한 메모리 양 결정
    if ((bp = extend_heap(extendsize / WSIZE)) == NULL) // 힙 확장
        return NULL;                                    // 실패 시 NULL 반환
    place(bp, asize);                                   // 확장된 힙에서 할당된 블록을 찾아 할당하고 반환
    return bp;
}

static void *find_fit(size_t asize)
{
    /* First-fit search */
    void *bp; /* Pointer to the block to be examined */ // 검사할 블록을 가리키는 포인터

    // 가용리스트를 순회하며 맞는 사이즈의 가용 블록을 찾음
    for (bp = free_listp; GET_ALLOC(HDRP(bp)) != 1; bp = SUCC_FREEP(bp))
    {
        //  요청한 크기보다 크거나 같으면
        if (asize <= GET_SIZE(HDRP(bp)))
        {
            return bp; // 해당 블록 포인터 리턴
        }
    }
    return NULL; /* No fit */ // 적합한 블록을 찾지 못한 경우 NULL 반환
}

static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp)); // 현재 블록의 크기를 가져옴 current size

    remove_freelist(bp); // 할당될 블록이므로 free list에서 없애준다.

    // 현재 블록의 크기가 요청한 크기보다 2 * DSIZE보다 큰 경우
    // 분할이 가능한 경우, 앞 블록을 할당된 블록, 뒷 블록을 가용블록으로 분할
    if ((csize - asize) >= (2 * DSIZE))
    {
        PUT(HDRP(bp), PACK(asize, 1));         // 현재 블록 헤더 설정
        PUT(FTRP(bp), PACK(asize, 1));         // 현재 블록 풋터 설정
        bp = NEXT_BLKP(bp);                    // 다음 블록으로 이동
        PUT(HDRP(bp), PACK(csize - asize, 0)); // 남은 부분의 헤더 설정
        PUT(FTRP(bp), PACK(csize - asize, 0)); // 남은 부분의 풋터 설정
        add_freelist(bp);
    }
    else // 현재 블록의 크기가 요청한 크기보다 작은 경우
    {
        PUT(HDRP(bp), PACK(csize, 1)); // 현재 블록 헤더 설정
        PUT(FTRP(bp), PACK(csize, 1)); // 현재 블록 풋터 설정
    }
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp)
{
    if (!bp)
        return;

    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0));
    PUT(FTRP(bp), PACK(size, 0));
    coalesce(bp);
}

/* Coalesce free blocks */
static void *coalesce(void *bp)
{
    // 이전 블록과 다음 블록의 할당 여부 및 크기 가져오기
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    // Case 1: prev and next allocated // 직전 직후 블록이 모두 할당 -> 현재 블록만 free list에 추가

    if (prev_alloc && !next_alloc) // Case 2: prev allocated, next free
    {
        remove_freelist(NEXT_BLKP(bp)); // free 상태였던 직후 블록을 free list에서 제거
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    else if (!prev_alloc && next_alloc) // Case 3: prev free, next allocated
    {
        remove_freelist(PREV_BLKP(bp)); // free 상태였던 직전 블록을 free list에서 제거
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    else if (!prev_alloc && !next_alloc) // Case 4: next and prev free
    {
        remove_freelist(PREV_BLKP(bp));
        remove_freelist(NEXT_BLKP(bp));
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        bp = PREV_BLKP(bp);
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    add_freelist(bp); // 연결된 새 가용 블록을 free list에 추가
    return bp;
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */

void *mm_realloc(void *ptr, size_t size)
{
    // 이전 포인터를 저장할 변수
    void *oldptr = ptr;
    // 새로운 포인터를 저장할 변수
    void *newptr;
    // 복사할 크기를 저장할 변수
    size_t copySize;

    /* 예외 처리 */
    if (ptr == NULL) // 포인터가 NULL인 경우 할당만 수행
    {
        return mm_malloc(size);
    }
    if (size <= 0) // size가 0인 경우 메모리 반환만 수행
    {
        mm_free(oldptr);
        return NULL;
    }
    /* 새 블록에 할당 */
    newptr = mm_malloc(size); // 새로 할당된 메모리 공간을 할당
    if (newptr == NULL)
        return NULL; // 할당에 실패하면 NULL 반환

    /* 데이터 복사 */
    copySize = GET_SIZE(HDRP(oldptr)) - DSIZE; // 이전 메모리 블록(payload)의 크기를 가져옴
    // 복사할 크기가 새로운 크기보다 크다면 새로운 크기로 조정
    if (size < copySize)
        copySize = size; // size로 크기 변경 (기존 메모리 블록보다 작은 크기에 할당하면, 일부 데이터만 복사)
    // 이전 메모리 블록에서 새로운 메모리 블록으로 데이터를 복사
    memcpy(newptr, oldptr, copySize);
    // 이전 메모리 블록 해제
    mm_free(oldptr);
    // 새로운 메모리 블록 포인터 반환
    return newptr;
}

/*
 * add_freelist - 가용 리스트의 시작에 블록을 추가합니다.
 * 매개변수:
 *   - bp: 가용 리스트에 추가할 블록을 가리키는 포인터
 * 설명:
 *   이 함수는 지정된 블록을 가용 리스트의 시작 부분에 추가합니다.
 *   그에 따라 전임자 및 후임자 포인터를 업데이트합니다.
 */

void add_freelist(void *bp)
{
    SUCC_FREEP(bp) = free_listp; // 새 블록의 후임자 포인터를 현재 가용 리스트의 시작으로 설정합니다.
    PRED_FREEP(bp) = NULL;       // 새 블록의 전임자 포인터를 NULL로 설정합니다. 새 블록은 가용 리스트의 새로운 시작이기 때문입니다.
    PRED_FREEP(free_listp) = bp; // 가용 리스트가 비어 있지 않으면, 현재 가용 리스트의 시작의 전임자 포인터를 새 블록으로 설정합니다.
    free_listp = bp;             // 가용 리스트 포인터를 새 블록으로 업데이트합니다.
}

/*
 * remove_freelist - 가용 리스트에서 블록을 제거합니다.
 * 매개변수:
 *   - bp: 가용 리스트에서 제거할 블록을 가리키는 포인터
 * 설명:
 *   이 함수는 지정된 블록을 가용 리스트에서 제거합니다.
 *   그에 따라 전임자 및 후임자 포인터를 업데이트합니다.
 */

void remove_freelist(void *bp)
{
    if (bp == free_listp) // 제거할 블록이 가용 리스트의 헤드인 경우
    {
        PRED_FREEP(SUCC_FREEP(bp)) = NULL; // 현재 헤드의 후임자의 전임자 포인터를 NULL로 설정합니다.
        free_listp = SUCC_FREEP(bp);       // 가용 리스트 포인터를 현재 헤드의 후임자로 업데이트합니다.
    }
    else
    {
        SUCC_FREEP(PRED_FREEP(bp)) = SUCC_FREEP(bp); // 제거할 블록의 전임자의 후임자 포인터를 제거할 블록의 후임자로 설정합니다.
        PRED_FREEP(SUCC_FREEP(bp)) = PRED_FREEP(bp); // 제거할 블록의 후임자의 전임자 포인터를 제거할 블록의 전임자로 설정합니다.
    }
}