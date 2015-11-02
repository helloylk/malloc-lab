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
 * provide your information in the following struct.
 ********************************************************/
student_t student = {
  /* Your full name */
  "Yeli Kim",
  /* Your student ID */
  "2012-13276",
};

/* DON'T MODIFY THIS VALUE AND LEAVE IT AS IT WAS */
static range_t **gl_ranges;

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

/* Useful macros */
#define WSIZE       4       //header, footer size
#define DSIZE       8       //total overhead size
#define CHUNKSIZE  (1<<12)  //amnt to extend heap by

#define MAX(x, y) ((x) > (y)? (x) : (y))

#define PACK(size, alloc)  ((size) | (alloc)) //puts size and allocated byte into 4 bytes

#define GET(p)       (*(unsigned int *)(p)) //read word at address p
#define PUT(p, val)  (*(unsigned int *)(p) = (val)) //write word at address p

#define GET_SIZE(p)  (GET(p) & ~0x7) //extracts size from 4 byte header/footer
#define GET_ALLOC(p) (GET(p) & 0x1) //extracts allocated byte from 4 byte header/footer

#define NEXT(ptr)  ((char *)(ptr) + GET_SIZE(((char *)(ptr) - WSIZE))) //next block
#define PREV(ptr)  ((char *)(ptr) - GET_SIZE(((char *)(ptr) - DSIZE))) //prev block

#define HDRP(ptr)	((void *)(ptr) -WSIZE) //get ptr's header
#define FTRP(ptr) 	((void *)(ptr) +GET_SIZE(HDRP(ptr)) - DSIZE)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* Useful Functions*/
static void *extend_heap(size_t words);
static void *coalesce(void *bp);
static void *find_fit(size_t asize);
int mm_check(void);
static void *place(void *bp, size_t asize);
//static void remove(void *ptr);

/* Global variables*/
char *heap_listp;

/* 
 * remove_range - manipulate range lists
 * DON'T MODIFY THIS FUNCTION AND LEAVE IT AS IT WAS
 */
static void remove_range(range_t **ranges, char *lo)
{
  range_t *p;
  range_t **prevpp = ranges;
  
  if (!ranges)
    return;

  for (p = *ranges;  p != NULL; p = p->next) {
    if (p->lo == lo) {
      *prevpp = p->next;
      free(p);
      break;
    }
    prevpp = &(p->next);
  }
}

/*
 * handle_double_free - prints an error message and aborts
 *    when your program tries to free an unallocated or freed
 *    memory block.
 * DON'T MODIFY THIS FUNCTION AND LEAVE IT AS IT WAS
 */
void handle_double_free(void) {
  printf("ERROR : Your program tried to unallocated or freed \
    memory block.\n");
  exit(-1);
}



/*
 * mm_init - initialize the malloc package.
 */
int mm_init(range_t **ranges)
{
  /* free array check? */

  // Create the initial empty heap
  if ((heap_listp = mem_sbrk(4*WSIZE)) == -1) return -1;

  PUT(heap_listp, 0); 				// alignment padding
  PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); 	// prologue header
  PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));	// prologue footer
  PUT(heap_listp + (3*WSIZE), PACK(0, 1)); 	// epliogue header
  heap_listp += (2*WSIZE); 			

  // Extend the empty heap with a free block of CHUNKSIZE bytes
  if(extend_heap(CHUNKSIZE) == NULL) return -1;

  /* DON't MODIFY THIS STAGE AND LEAVE IT AS IT WAS */
  gl_ranges = ranges;

  return 0;
}


/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void* mm_malloc(size_t size)
{
  size_t asize; /* Adjusted block size */
  size_t extendsize; /* Amount to extend heap if no fit */
  char *bp;

  /* Ignore spurious requests */
  if (size == 0)
  return NULL;

  /* Adjust block size to include overhead and alignment reqs. */
  if (size <= DSIZE)
   asize = 2*DSIZE;
  else
   asize = DSIZE * ((size + (DSIZE) + (DSIZE-1)) / DSIZE);
  
  /* Search the free list for a fit */
  if ((bp = find_fit(asize)) != NULL) {
   place(bp, asize);
   return bp;
   }

  /* No fit found. Get more memory and place the block */
  extendsize = MAX(asize,CHUNKSIZE);
  if ((bp = extend_heap(extendsize/WSIZE)) == NULL)
    return NULL;
  place(bp, asize);
  return bp;
 
}

/*
 * mm_free - Freeing a block 
 * If the allocation bit of the block that we are trying to free is 0, then call handle_double_free
 * Else, free the block by setting allocation bit to 0 and coalescing the adjacent freed block
 */
void mm_free(void *ptr)
{
  if (!ptr) return;
  size_t size = GET_SIZE(HDRP(ptr));

 //call double_handle_free when try to free the freed block
  if ((GET_ALLOC(HDRP(ptr)))==0)
    handle_double_free();
 
  // set header and footer to unallocated 
  PUT(HDRP(ptr), PACK(size,0));
  PUT(FTRP(ptr), PACK(size,0));
  
  //coalesce the adjacent freed block
  coalesce(ptr);

  /* DON't MODIFY THIS STAGE AND LEAVE IT AS IT WAS */
  if (gl_ranges)
    remove_range(gl_ranges, ptr);
}

/*
 * mm_realloc - empty implementation; YOU DO NOT NEED TO IMPLEMENT THIS
 */
void* mm_realloc(void *ptr, size_t t)
{
  return NULL;
}

/*
 * mm_exit - finalize the malloc package.
 */
void mm_exit(void)
{
  return 0;
}

/*----------------------------------------------------------------------*/
/*
 * mm_check
 * Check the heap for consistency
 * 
 */
int check_block(void *ptr){
  if ((size_t)ptr%8){
      printf("ERROR, %p is not aligned correctly\n", ptr);
      return 1;
  }
  if (GET(HDRP(ptr)) != GET(FTRP(ptr))){
      printf("ERROR, %p has inconsistent header/footer\n", ptr);
      return 2;
  }
  return 0;
}

int mm_check(void){

  char *ptr;
  int cont = 1;
  int size;
  int found = 0;

  size_t* start_heap =  mem_heap_lo();
  size_t* end_heap =  mem_heap_hi();

  size_t* curr_block = start_heap;

  for(ptr = start_heap; GET_SIZE(HDRP(ptr)) > 0; ptr = NEXT(ptr)) {
      printf(check_block(ptr));
      if (ptr > end_heap || ptr < start_heap)
          printf("Error: pointer %p out of heap bounds\n", ptr);
      if (GET_ALLOC(ptr) == 0 && GET_ALLOC(NEXT(ptr))==0)
          printf("ERROR: contiguous free blocks %p and %p not coalesced\n", ptr, NEXT(ptr));
        
  }

  return 0;
}

/* 
 * place - Place block of asize bytes at start of free block bp 
 *         and split if remainder would be at least minimum block size
 */
static void *place(void *bp, size_t asize)
{
  size_t csize = GET_SIZE(HDRP(bp));
   
  if((csize -asize) >= 24) {
    PUT(HDRP(bp), PACK(asize,1));
    PUT(FTRP(bp), PACK(asize,1));
    bp = NEXT(bp);
    PUT(HDRP(bp), PACK(csize-asize,0));
    PUT(FTRP(bp), PACK(csize-asize,0));
  }
  else{
      PUT(HDRP(bp), PACK(csize, 1));
      PUT(FTRP(bp), PACK(csize, 1));
  }
}


/*
 * extend_heap - extends the heap with a new free block.
 */
static void *extend_heap(size_t words) 
{
    char *bp;
    size_t size;
    
    /* Allocate an even number of words to maintain alignment */
    size = (words % 2) ? (words+1) * WSIZE : words * WSIZE;
    if ((int)(bp = mem_sbrk(size)) == -1) 
        return NULL;

    /* Initialize free block header/footer and the epilogue header */
    PUT(HDRP(bp), PACK(size, 0));         /* free block header */
    PUT(FTRP(bp), PACK(size, 0));         /* free block footer */
    PUT(HDRP(NEXT(bp)), PACK(0, 1)); /* new epilogue header */

    /* Coalesce if the previous block was free */
    return coalesce(bp);
}


/*
 * coalesce - boundary tag coalescing. Return ptr to coalesced block
 */
static void *coalesce(void *ptr) 
{
    size_t prev_alloc = GET_ALLOC(FTRP(PREV(ptr)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT(ptr)));
    size_t size = GET_SIZE(HDRP(ptr));

    if (prev_alloc && next_alloc) {            /* Case 1: Neighbors both allocated */
        return ptr;
    }

    else if (prev_alloc && !next_alloc) {      /* Case 2: Only the previous is allocated*/
        size += GET_SIZE(HDRP(NEXT(ptr)));
        PUT(HDRP(ptr), PACK(size,0));
        PUT(FTRP(ptr), PACK(size,0));
        return ptr;
    }

    else if (!prev_alloc && next_alloc) {      /* Case 3: Only the next is allocated */
        size += GET_SIZE(HDRP(PREV(ptr)));
        PUT(FTRP(ptr), PACK(size, 0));
        PUT(HDRP(PREV(ptr)), PACK(size, 0));
        return (PREV(ptr));
    }

    else {                                     /* Case 4: Neither are allocated */
        size += GET_SIZE(HDRP(PREV(ptr))) + 
            GET_SIZE(FTRP(NEXT(ptr)));
        PUT(HDRP(PREV(ptr)), PACK(size, 0));
        PUT(FTRP(NEXT(ptr)), PACK(size, 0));
        return (PREV(ptr));
    }
}

/*
#define PREV_FP(bp)	(*(void **)(bp))
#define NEXT_FP(bp)	(*(void **)(bp+DSIZE))

static void remove(void *ptr)
{
  if(PREV_FP(bp)) NEXT_FP(PREV_FP(ptr)) =NEXT_FP(ptr);
  PREV_FP(NEXT_FP(ptr)) = PREV_FP(ptr);
}
*/

/* 
 * find_fit - Find a fit for a block with asize bytes 
 */
static void *find_fit(size_t asize)
{
    void *ptr;

    /* first fit search */
    for (ptr = heap_listp; GET_SIZE(HDRP(ptr)) > 0; ptr = NEXT(ptr)) {
        if (!GET_ALLOC(HDRP(ptr)) && (asize <= GET_SIZE(HDRP(ptr)))) {
            return ptr;
        }
    }
    return NULL; /* no fit */
}
