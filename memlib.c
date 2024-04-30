/*
 * memlib.c - a module that simulates the memory system.  Needed because it
 *            allows us to interleave calls from the student's malloc package
 *            with the system's malloc package in libc.
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <sys/mman.h>
#include <string.h>
#include <errno.h>

#include "memlib.h"
#include "config.h"

/* private variables */
static char *mem_start_brk; /* points to first byte of heap */
static char *mem_brk;       /* points to last byte of heap */
static char *mem_max_addr;  /* largest legal heap address */

/*
 * mem_init - initialize the memory system model
 */
void mem_init(void)
{
    /* allocate the storage we will use to model the available VM */
    // config.h에 정의되어 있음, #define MAX_HEAP (20*(1<<20)) : 20971520bytes == 20 MB
    if ((mem_start_brk = (char *)malloc(MAX_HEAP)) == NULL)
    {
        fprintf(stderr, "mem_init_vm: malloc error\n");
        exit(1);
    }

    mem_max_addr = mem_start_brk + MAX_HEAP; /* max legal heap address */
    mem_brk = mem_start_brk;                 /* heap is empty initially */
}

/*
 * mem_deinit - free the storage used by the memory system model
 */
void mem_deinit(void)
{
    free(mem_start_brk);
}

/*
 * mem_reset_brk - reset the simulated brk pointer to make an empty heap
 */
void mem_reset_brk()
{
    mem_brk = mem_start_brk;
}

/*
 * mem_sbrk - simple model of the sbrk function. Extends the heap
 *    by incr bytes and returns the start address of the new area. In
 *    this model, the heap cannot be shrunk.
 */
void *mem_sbrk(int incr) // 바이트 형태로 입력 받음
{
    char *old_brk = mem_brk; // 힙 늘이기 전 끝 포인터를 저장 (mem_brk는 힙의 끝 가리킴)
                             // 힙이 줄어들거나 최대 힙 사이즈 벗어나면 메모리 부족으로 에러처리 & -1을 리턴
    if ((incr < 0) || ((mem_brk + incr) > mem_max_addr))
    {
        errno = ENOMEM; // 메모리 부족 에러 처리
        fprintf(stderr, "ERROR: mem_sbrk failed. Ran out of memory...\n");
        return (void *)-1; // 리턴 값이 void* 여야 하니 형 변환해줌
    }
    mem_brk += incr;        // mem_brk에 incr만큼 더해서 힙 늘려줌
    return (void *)old_brk; // 이전 brk를 리턴 => 새로운 메모리를 처음부터 사용해야 하니 (위 코드에서 old_brk 뒤로는 여분 공간이 생겨난 상태)
}

/*
 * mem_heap_lo - return address of the first heap byte
 */
void *mem_heap_lo()
{
    return (void *)mem_start_brk;
}

/*
 * mem_heap_hi - return address of last heap byte
 */
void *mem_heap_hi()
{
    return (void *)(mem_brk - 1);
}

/*
 * mem_heapsize() - returns the heap size in bytes
 */
size_t mem_heapsize()
{
    return (size_t)(mem_brk - mem_start_brk);
}

/*
 * mem_pagesize() - returns the page size of the system
 */
size_t mem_pagesize()
{
    return (size_t)getpagesize();
}
