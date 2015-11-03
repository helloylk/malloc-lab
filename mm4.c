/*
 * mm-naive.c 
 *
 * In this program, blocks follow the standard 4 byte identical header and footer, 
 * which carries size and 3 bit of allocation tag.
 * Main algorithm to malloc is by using 'segregated free list' method.
 * Free block has pointer of the prodecessor in segregated free list and pointer to the successor.
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

/* Useful macros (some from book) */
#define WSIZE       4       //header, footer size
#define DSIZE       8       //total overhead size
#define CHUNKSIZE  (1<<12)  //amnt to extend heap by
#define INITCHUNKSIZE (1<<6)

#define MAX(x, y) ((x) > (y)? (x) : (y))
#define MIN(x, y) ((x) < (y)? (x) : (y))

#define PACK(size, alloc)  ((size) | (alloc)) //puts size and allocated byte into 4 bytes

#define GET(p)       (*(unsigned int *)(p)) //read word at address p
#define PUT(p, val)  (*(unsigned int *)(p) = (val)) //write word at address p
#define PUT_PTR(p, ptr) (*(unsigned int *)(p) = (unsigned int)(ptr)) // write predecessor or successor pointer  

#define GET_SIZE(p)  (GET(p) & ~0x7) //extracts size from 4 byte header/footer
#define GET_ALLOC(p) (GET(p) & 0x1) //extracts allocated byte from 4 byte header/footer

// get addr of previous & next block
#define NEXT(ptr)  ((char *)(ptr) + GET_SIZE(((char *)(ptr) - WSIZE))) 
#define PREV(ptr)  ((char *)(ptr) - GET_SIZE(((char *)(ptr) - DSIZE)))

// get ptr's header & footer
#define HDRP(ptr)	  ((void *)(ptr) -WSIZE) 
#define FTRP(ptr) 	((void *)(ptr) +GET_SIZE(HDRP(ptr)) - DSIZE)

// get ptr's predecessor and successor entries 
#define PRED_ENT(ptr) ((char *)(ptr))
#define SUCC_ENT(ptr) ((char *)(ptr) + WSIZE)

// get ptr's predecessor and successor on the segregated list 
#define PRED_LIST(ptr) (*(char **)(ptr))
#define SUCC_LIST(ptr) (*(char **)(SUCC_ENT(ptr)))

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8
/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT-1)) & ~0x7)

/*non-static functions */
int mm_init(range_t **ranges);
void* mm_malloc(size_t size);
void mm_free(void *ptr);
void mm_exit(void);

/* Useful Functions*/
static void *extend_heap(size_t words);
static void *coalesce(void *ptr);
static void *place(void *ptr, size_t asize);
static void insert_node(void *ptr, size_t size);
static void delete_node(void *ptr);

/* Global variables*/
void *segregated_free_lists[25]; 
static range_t **gl_ranges;

//--------------------------------------------------------------------------------
/* 
 * remove_range - manipulate range lists
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
 */
void handle_double_free(void) {
  printf("ERROR : Your program tried to unallocated or freed \
    memory block.\n");
  exit(-1);
}


//------------------------------------------------------------------------------
/*
 * mm_init - initialize the malloc package.
 * create the initial, very first empty heap\
 * Initialize the segregated free lists (list max length=25)
 */
int mm_init(range_t **ranges)
{
  int i;
  char *heap_listp;
  
  /* Initialize array of pointers to segregated free lists */
  for (i = 0; i < 25; i++) {
    segregated_free_lists[i] = NULL;
  }

  /* Create the initial empty heap */
  if ((long)(heap_listp = mem_sbrk(4*WSIZE)) == -1) return -1;

  PUT(heap_listp, 0); 			                   	 /* alignment padding */
  PUT(heap_listp + (1*WSIZE), PACK(DSIZE, 1)); 	/* prologue header */
  PUT(heap_listp + (2*WSIZE), PACK(DSIZE, 1));	/* prologue footer */
  PUT(heap_listp + (3*WSIZE), PACK(0, 1)); 	    /* epliogue header */

  /* Extend the empty heap with a free block of CHUNKSIZE bytes */
  if(extend_heap(INITCHUNKSIZE) == NULL) return -1;

  gl_ranges = ranges;
  return 0;
}


void *mm_malloc(size_t size)
{
    size_t asize;      /* Adjusted block size */
    size_t extendsize; /* Amount to extend heap if no fit */
    void *ptr = NULL;  /* Pointer */
    
    // Ignore size 0 cases
    if (size == 0)
        return NULL;
    
    // Align block size
    if (size <= DSIZE) {
        asize = 2 * DSIZE;
    } else {
        asize = ALIGN(size+DSIZE);
    }
    
    int list = 0; 
    size_t searchsize = asize;
    // Search for free block in segregated list
    while (list < 25) {
        if ((list == 25 - 1) || ((searchsize <= 1) && (segregated_free_lists[list] != NULL))) {
            ptr = segregated_free_lists[list];
            // Ignore blocks that are too small or marked with the reallocation bit
            while ((ptr != NULL) && (asize > GET_SIZE(HDRP(ptr))))
            {
                ptr = PRED_LIST(ptr);
            }
            if (ptr != NULL)
                break;
        }
        
        searchsize >>= 1;
        list++;
    }
    
    // if free block is not found, extend the heap
    if (ptr == NULL) {
        extendsize = MAX(asize, CHUNKSIZE);
        
        if ((ptr = extend_heap(extendsize)) == NULL)
            return NULL;
    }
    
    // Place and divide block
    ptr = place(ptr, asize);
    
    
    // Return pointer to newly allocated block 
    return ptr;
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
  //note: put_tag
  
  //coalesce the adjacent freed block
  insert_node(ptr, size);
  coalesce(ptr);
  
  if (gl_ranges)
    remove_range(gl_ranges, ptr);
  return;
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
 * Free all the allocated blocks.
 */
void mm_exit(void)
{
 /*
  char *ptr=heap_listp;
  
  while(ptr!=NULL){
   free(ptr);
   ptr=NEXT(ptr);
  }
  */
  return;
}



//------------------------------------------------------------------------------------------------
/*
 * extend_heap - extends the heap with a new free block.
 */
static void *extend_heap(size_t size)
{
    void *ptr;                   
    size_t asize;                // Adjusted size 
    
    asize = ALIGN(size);
    
    if ((ptr = mem_sbrk(asize)) == (void *)-1)
        return NULL;
    
    // Set headers and footer 
    PUT(HDRP(ptr), PACK(asize, 0));  
    PUT(FTRP(ptr), PACK(asize, 0));   
    PUT(HDRP(NEXT(ptr)), PACK(0, 1)); 
    insert_node(ptr, asize);

    return coalesce(ptr);
}

/* 
 * place - Place block of asize bytes at start of free block bp 
 *         and split if remainder would be at least minimum block size
 */
static void *place(void *ptr, size_t asize)
{
    size_t ptr_size = GET_SIZE(HDRP(ptr));
    size_t remainder = ptr_size - asize;
    
    delete_node(ptr);
    
    
    if (remainder <= DSIZE * 2) {
        // Do not split block 
        PUT(HDRP(ptr), PACK(ptr_size, 1)); 
        PUT(FTRP(ptr), PACK(ptr_size, 1)); 
    }
    
    else if (asize >= 100) {
        // Split block
        PUT(HDRP(ptr), PACK(remainder, 0));
        PUT(FTRP(ptr), PACK(remainder, 0));
        PUT(HDRP(NEXT(ptr)), PACK(asize, 1));
        PUT(FTRP(NEXT(ptr)), PACK(asize, 1));
        insert_node(ptr, remainder);
        return NEXT(ptr);
        
    }
    
    else {
        // Split block
        PUT(HDRP(ptr), PACK(asize, 1)); 
        PUT(FTRP(ptr), PACK(asize, 1)); 
        PUT(HDRP(NEXT(ptr)), PACK(remainder, 0)); 
        PUT(FTRP(NEXT(ptr)), PACK(remainder, 0)); 
        insert_node(NEXT(ptr), remainder);
    }
    return ptr;
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
        delete_node(ptr);
        delete_node(NEXT(ptr));
        size += GET_SIZE(HDRP(NEXT(ptr)));
        PUT(HDRP(ptr), PACK(size,0));
        PUT(FTRP(ptr), PACK(size,0));
        insert_node(ptr, size);
        return ptr;
    }

    else if (!prev_alloc && next_alloc) {      /* Case 3: Only the next is allocated */
        delete_node(ptr);
        delete_node(PREV(ptr));
        size += GET_SIZE(HDRP(PREV(ptr)));
        PUT(FTRP(ptr), PACK(size, 0));
        PUT(HDRP(PREV(ptr)), PACK(size, 0));
        insert_node(PREV(ptr), size);
        return (PREV(ptr));
    }

    else {                                     /* Case 4: Neither are allocated */
        delete_node(ptr);
        delete_node(PREV(ptr));
        delete_node(NEXT(ptr));
        size += GET_SIZE(HDRP(PREV(ptr))) + GET_SIZE(FTRP(NEXT(ptr)));
        PUT(HDRP(PREV(ptr)), PACK(size, 0));
        PUT(FTRP(NEXT(ptr)), PACK(size, 0));
        insert_node(PREV(ptr), size);
        return (PREV(ptr));
    }
}



static void insert_node(void *ptr, size_t size) {
    int i = 0;
    void *search_ptr = ptr;
    void *insert_ptr = NULL;
    
    /* Select segregated list */ 
    while ((i < 24) && (size > 1)) {
        size >>= 1;
        i++;
    }
    
    // Keep size ascending order and search
    search_ptr = segregated_free_lists[i];
    while ((search_ptr != NULL) && (size > GET_SIZE(HDRP(search_ptr)))) {
        insert_ptr = search_ptr;
        search_ptr = PRED_LIST(search_ptr);
    }
    
    // Set predecessor and successor 
    if (search_ptr != NULL) {
        if (insert_ptr != NULL) {
            PUT_PTR(PRED_ENT(ptr), search_ptr);
            PUT_PTR(SUCC_ENT(search_ptr), ptr);
            PUT_PTR(SUCC_ENT(ptr), insert_ptr);
            PUT_PTR(PRED_ENT(insert_ptr), ptr);
        } else {
            PUT_PTR(PRED_ENT(ptr), search_ptr);
            PUT_PTR(SUCC_ENT(search_ptr), ptr);
            PUT_PTR(SUCC_ENT(ptr), NULL);
            segregated_free_lists[i] = ptr;
        }
    } else {
        if (insert_ptr != NULL) {
            PUT_PTR(PRED_ENT(ptr), NULL);
            PUT_PTR(SUCC_ENT(ptr), insert_ptr);
            PUT_PTR(PRED_ENT(insert_ptr), ptr);
        } else {
            PUT_PTR(PRED_ENT(ptr), NULL);
            PUT_PTR(SUCC_ENT(ptr), NULL);
            segregated_free_lists[i] = ptr;
        }
    }
    
    return;
}


static void delete_node(void *ptr) {
    int i = 0;
    size_t size = GET_SIZE(HDRP(ptr));
    
    // Select segregated list 
    while ((i < 24 ) && (size > 1)) {
        size >>= 1;
        i++;
    }
    
    if (PRED_LIST(ptr) != NULL) {
        if (SUCC_LIST(ptr) != NULL) {
            PUT_PTR(SUCC_ENT(PRED_LIST(ptr)), SUCC_LIST(ptr));
            PUT_PTR(PRED_ENT(SUCC_LIST(ptr)), PRED_LIST(ptr));
        } else {
            PUT_PTR(SUCC_ENT(PRED_LIST(ptr)), NULL);
            segregated_free_lists[i] = PRED_LIST(ptr);
        }
    } else {
        if (SUCC_LIST(ptr) != NULL) {
            PUT_PTR(PRED_ENT(SUCC_LIST(ptr)), NULL);
        } else {
            segregated_free_lists[i] = NULL;
        }
    }
    return;
}
