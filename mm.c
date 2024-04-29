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
    "team3",
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
#define WSIZE 4 /* Word and header/footer size (bytes) */            /* 워드와 헤더/풋터 크기 (바이트) */
#define DSIZE 8 /* Double word size (bytes) */                       /* 더블 워드 크기 (바이트) */
#define CHUNKSIZE (1 << 12) /* Extend heap by this amount (bytes) */ // 힙 확장을 위한 기본 크기 (= 초기 빈 블록의 크기)

/* 매크로 */
#define MAX(x, y) ((x) > (y) ? (x) : (y)) // 두 값을 비교하여 더 큰 값을 반환

/* Pack a size and allocated bit into a word */ /* 크기와 할당 비트를 워드에 패킹 */
#define PACK(size, alloc) ((size) | (alloc))    // size와 allocated bit를 통합해서 header와 footer에 저장할 수 있는 값을 리턴한다.

/* Read and write a word at address p */           /* 주소 p에서 워드를 읽고 쓰기 */
#define GET(p) (*(unsigned int *)(p))              // p가 (void *) 포인터 일 수 있어서 역참조 불가. 캐스팅을 해줘야한다.
#define PUT(p, val) (*(unsigned int *)(p) = (val)) // p가 가리키는 워드에 val저장
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

/* Global variables */
static char *heap_listp = 0; // Pointer to first block
static char *rover;          // Next fit rover

/* Function prototypes for internal helper routines */
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
static void place(void *bp, size_t asize);

/*
 * mm_init - initialize the malloc package.
   mm_init: creates a heap with an initial free block (최초 가용 블록으로 힙 생성하기)
 */

int mm_init(void)
{
    /* Create the initial empty heap */                   // 초기 힙 생성
    if ((heap_listp = mem_sbrk(4 * WSIZE)) == (void *)-1) // 4워드 크기의 힙 생성, heap_listp에 힙의 시작 주소값 할당
        return -1;
    PUT(heap_listp, 0); /* Alignment padding */                          // 정렬 패딩
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue header */ // 프롤로그 Header
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */ // 프롤로그 Footer
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1)); /* Epilogue header */     // 에필로그 Header: 프로그램이 할당한 마지막 블록의 뒤에 위치하며, 블록이 할당되지 않은 상태를 나타냄
    heap_listp += (2 * WSIZE);                                           // heap_listp를 프롤로그 블록 Footer로 이동시킵니다.

    rover = heap_listp;

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
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); /* New epilogue header */ // 현재 블록 다음 블록의 헤더 설정 (에필로그)

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
    if (size == 0)
        return NULL; // 크기가 0인 요청은 무시하고 NULL 반환

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
    // /* First-fit search */
    // void *bp; /* Pointer to the block to be examined */ // 검사할 블록을 가리키는 포인터

    // // 힙 리스트를 순회하여 적합한 블록을 찾음
    // for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp))
    // {
    //     // 블록이 가용 상태이고, 요청한 크기보다 크거나 같으면
    //     if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp))))
    //     {
    //         return bp; // 해당 블록 포인터 리턴
    //     }
    // }
    // return NULL; /* No fit */ // 적합한 블록을 찾지 못한 경우 NULL 반환

    /* Next-fit search */
    char *oldrover = rover;

    // Search from the rover to the end of list
    for (; GET_SIZE(HDRP(rover)) > 0; rover = NEXT_BLKP(rover))
        if (!GET_ALLOC(HDRP(rover)) && (asize <= GET_SIZE(HDRP(rover))))
            return rover;

    // Search from start of list to old rover
    for (rover = heap_listp; rover < oldrover; rover = NEXT_BLKP(rover))
        if (!GET_ALLOC(HDRP(rover)) && (asize <= GET_SIZE(HDRP(rover))))
            return rover;

    return NULL; // No fit found
}

static void place(void *bp, size_t asize)
{
    size_t csize = GET_SIZE(HDRP(bp)); // 현재 블록의 크기를 가져옴 current size

    // 현재 블록의 크기가 요청한 크기보다 2 * DSIZE보다 큰 경우
    if ((csize - asize) >= (2 * DSIZE))
    {
        PUT(HDRP(bp), PACK(asize, 1));         // 현재 블록 헤더 설정
        PUT(FTRP(bp), PACK(asize, 1));         // 현재 블록 풋터 설정
        bp = NEXT_BLKP(bp);                    // 다음 블록으로 이동
        PUT(HDRP(bp), PACK(csize - asize, 0)); // 남은 부분의 헤더 설정
        PUT(FTRP(bp), PACK(csize - asize, 0)); // 남은 부분의 풋터 설정
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
void mm_free(void *ptr)
{
    if (!ptr)
        return;

    size_t size = GET_SIZE(HDRP(ptr));

    PUT(HDRP(ptr), PACK(size, 0));
    PUT(FTRP(ptr), PACK(size, 0));
    coalesce(ptr);
}

/* Coalesce free blocks */
static void *coalesce(void *bp)
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    if (prev_alloc && next_alloc) // Case 1: prev and next allocated
        return bp;

    else if (prev_alloc && !next_alloc) // Case 2: prev allocated, next free
    {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));
        PUT(HDRP(bp), PACK(size, 0));
        PUT(FTRP(bp), PACK(size, 0));
    }

    else if (!prev_alloc && next_alloc) // Case 3: prev free, next allocated
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp)));
        PUT(FTRP(bp), PACK(size, 0));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    else // Case 4: next and prev free
    {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp)));
        PUT(HDRP(PREV_BLKP(bp)), PACK(size, 0));
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));
        bp = PREV_BLKP(bp);
    }

    // Make sure the rover isn't pointing into the free block that we just coalesced
    if ((rover > (char *)bp) && (rover < NEXT_BLKP(bp)))
        rover = bp;

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

    // 만약 새로운 크기가 0이면, 현재 포인터를 해제하고 NULL을 반환
    if (size == 0)
    {
        mm_free(oldptr);
        return NULL;
    }

    // 새로 할당된 메모리 공간을 할당
    newptr = mm_malloc(size);
    // 할당에 실패하면 NULL 반환
    if (newptr == NULL)
        return NULL;

    // 이전 메모리 블록의 크기를 가져옴
    // copySize = *(size_t *)((char *)oldptr - SIZE_T_SIZE);
    copySize = GET_SIZE(HDRP(oldptr)) - DSIZE;
    // 복사할 크기가 새로운 크기보다 크다면 새로운 크기로 조정
    if (size < copySize)
        copySize = size;
    // 이전 메모리 블록에서 새로운 메모리 블록으로 데이터를 복사
    memcpy(newptr, oldptr, copySize);
    // 이전 메모리 블록 해제
    mm_free(oldptr);
    // 새로운 메모리 블록 포인터 반환
    return newptr;
}
