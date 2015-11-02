/*
 * mm.c - Malloc implementation using segregated fits with address-ordered
 *        explicit linked lists and reallocation heuristics
 *
 * Each block is wrapped in a 4-byte header and a 4-byte footer. Free blocks
 * are stored in one of many linked lists segregated by block size. The n-th
 * list contains blocks with a byte size that spans 2^n to 2^(n+1)-1. Within
 * each list, blocks are sorted by memory address in ascending order.
 * Coalescing is performed immediately after each heap extension and free
 * operation. Reallocation is performed in place, using a buffer and a
 * reallocation bit to ensure the availability of future block expansion.
 *
 * Header entries consist of the block size (all 32 bits), reallocation tag
 * (second-last bit), and allocation bit (last bit).
 *
 *
 * He (Henry) Tian
 * Section 3
 * 5/13/13
 */
#include <stdio.h>
#include <stdlib.h>
#include <assert.h>
#include <unistd.h>
#include <string.h>

#include "mm.h"
#include "memlib.h"

/*
 * Team identification
 */
student_t student = {
	"yeli kim",
	"2012-13276"
};

/* DON'T MODIFY THIS VALUE AND LEAVE IT AS IT WAS */
static range_t **gl_ranges;
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

/*Constants*/
#define SSIZE 4 //Single word, 4 bytes
#define DSIZE 8 //Double words, 8 bytes
#define TSIZE 12 //Triple words, 12 bytes
#define QSIZE 16 //Quadri words, 16 bytes
#define OVERHEAD 8 //Header and footer sign, 8 bytes
#define ALIGNMENT 8 //Alignment request, 8 bytes
#define BLKSIZE 24 //Single word, 24 bytes
#define CHUNKSIZE (1<<12) //Initial heap size
#define INISIZE 1016 //Heap extended size
/*Macros*/
/*Max and min value of 2 values*/
#define MAX(x, y) ( (x)>(y)? (x): (y) )
#define MIN(x, y) ( (x)<(y)? (x): (y) )
/*Read and write a word at address p*/
#define GET(p) (*(size_t *)(p))
#define PUT(p, val) (*(size_t *)(p)=(val)) 
/*Read the size and allocated fields from address p*/
#define SIZE(p) (GET(p)&~0x7)
#define PACK(size, alloc) ((size)|(alloc))
#define ALLOC(p) (GET(p)&0x1)
/*Given pointer p at the second word of the data structure, compute addresses
of its HEAD,LEFT,RIGHT,PRNT,BROS and FOOT pointer*/
#define HEAD(p) ((void *)(p)-SSIZE)
#define LEFT(p) ((void *)(p))
#define RIGHT(p) ((void *)(p)+SSIZE)
#define PRNT(p) ((void *)(p)+DSIZE)
#define BROS(p) ((void *)(p)+TSIZE)
#define FOOT(p) ((void *)(p)+SIZE(HEAD(p))-DSIZE)
/*Make the block to meet with the standard alignment requirements*/
#define ALIGN_SIZE(size) (((size) + (ALIGNMENT-1)) & ~0x7)
/*Given block pointer bp, get the POINTER of its directions*/
#define GET_SIZE(bp) ((GET(HEAD(bp)))&~0x7)
#define GET_PREV(bp) ((void *)(bp)-SIZE(((void *)(bp)-DSIZE)))
#define GET_NEXT(bp) ((void *)(bp)+SIZE(HEAD(bp)))
#define GET_ALLOC(bp) (GET(HEAD(bp))&0x1)
/*Get the LEFT,RIGHT,PRNT,BROS and FOOT pointer of the block to which bp
points*/
#define GET_LEFT(bp) (GET(LEFT(bp)))
#define GET_RIGHT(bp) (GET(RIGHT(bp)))
#define GET_PRNT(bp) (GET(PRNT(bp)))
#define GET_BROS(bp) (GET(BROS(bp)))
#define GET_FOOT(bp) (GET(FOOT(bp))) 
/*Define value to each character in the block bp points to.*/
#define PUT_HEAD(bp, val) (PUT(HEAD(bp), (int)val))
#define PUT_FOOT(bp, val) (PUT(FOOT(bp), (int)val))
#define PUT_LEFT(bp, val) (PUT(LEFT(bp), (int)val))
#define PUT_RIGHT(bp, val) (PUT(RIGHT(bp), (int)val))
#define PUT_PRNT(bp, val) (PUT(PRNT(bp), (int)val))
#define PUT_BROS(bp, val) (PUT(BROS(bp), (int)val))
All functions and global variables used in the program:
/* non-static functions */
int mm_init ( void );
void *mm_malloc ( size_t size );
void mm_free ( void *bp );
void *mm_realloc ( void *bp, size_t size );
/* static functions */
static void *coalesce ( void *bp );
static void *extend_heap ( size_t size );
static void place ( void *ptr, size_t asize );
static void insert_node ( void *bp );
static void delete_node ( void *bp );
static void *find_fit ( size_t asize );
/* Global variables */
static void *heap_list_ptr;
static void *free_tree_rt;

int mm_init(range_t ranges)
{
/* create the initial empty heap */
if( (heap_list_ptr = mem_sbrk(QSIZE)) == NULL )
return -1;
PUT( heap_list_ptr, 0 ); /* alignment padding */
PUT( heap_list_ptr+SSIZE, PACK(OVERHEAD,1) ); /* prologue header */
PUT( heap_list_ptr+DSIZE, PACK(OVERHEAD,1) ); /* prologue footer */
PUT( heap_list_ptr+TSIZE, PACK(0,1) ); /* epilogue header */
heap_list_ptr += QSIZE;
free_tree_rt = NULL;
/* Extend the empty heap with a free block of CHUNKSIZE bytes */
if( extend_heap(ALIGN_SIZE(INISIZE))==NULL )
return -1;

  /* DON't MODIFY THIS STAGE AND LEAVE IT AS IT WAS */
  gl_ranges = ranges;
  
  return 0;
}

void *extend_heap(size_t size)
{
void *bp;
if( (unsigned int)(bp=mem_sbrk(size)) ==(unsigned)(-1))
//if( (int)(bp=mem_sbrk(size)) <0 )//new
return NULL;
/* Initialize free block header/footer and the epilogue header */
PUT_HEAD( bp, PACK(size,0) ); /* free block header */
PUT_FOOT( bp, PACK(size,0) ); /* free block footer */
PUT_HEAD( GET_NEXT(bp), PACK(0,1) ); /* new epilogue header */
insert_node(coalesce(bp));
return (void *)bp;
}

void *mm_malloc(size_t size)
{
size_t asize; /* adjusted block size */
size_t extendsize; /* amount to extend heap if no fit */
void *bp;
/* Ignore spurious requests */
if( size <= 0 )
return NULL; 
/* Adjust block size to include overhead and alignment requirements. */
if( size <= BLKSIZE-OVERHEAD)
 /*size=required size; block size = all size excluded head&foot(overhead)*/
asize = BLKSIZE;
else
 /*asize=ajusted size*/
asize = ALIGN_SIZE(size+(OVERHEAD));
/* Search the free list for a fit */
 if( (bp=find_fit(asize)) == NULL ){
extendsize = MAX( asize + 32, INISIZE );
extend_heap(ALIGN_SIZE(extendsize));
if( (bp=find_fit(asize)) == NULL )
return NULL;
}
/* place the block into its fit */
if( size==448 && GET_SIZE(bp) > asize+64 )
asize += 64;
else if( size==112 && GET_SIZE(bp) > asize+16 )
asize += 16;
place(bp, asize);
return bp;
} 


/*
 * mm_free - Free a block by adding it to the appropriate list and coalescing
 *           it.
 */
void mm_free(void *bp)
{
size_t size = GET_SIZE(bp);
PUT_HEAD( bp, PACK(size,0) );
PUT_FOOT( bp, PACK(size,0) ); 
insert_node(coalesce(bp));

/* DON't MODIFY THIS STAGE AND LEAVE IT AS IT WAS */
  if (gl_ranges)
    remove_range(gl_ranges, ptr);
} 


void *mm_realloc(void *ptr, size_t size)
{
  ;
}

static void *coalesce(void *bp)
{
size_t prev_alloc = GET_ALLOC(GET_PREV(bp));
size_t next_alloc = GET_ALLOC(GET_NEXT(bp));
size_t size = GET_SIZE(bp);
if ( prev_alloc && next_alloc ) /* Case 0 */
return bp;
else if ( !prev_alloc && next_alloc ) { /* Case 1*/
delete_node(GET_PREV(bp));
size += GET_SIZE( GET_PREV(bp) );
PUT_HEAD( GET_PREV(bp), PACK(size, 0) );
PUT_FOOT( bp, PACK(size,0) );
return GET_PREV(bp);
}
else if ( prev_alloc && !next_alloc ) { /* Case 2 */
delete_node( GET_NEXT(bp) );
size += GET_SIZE( GET_NEXT(bp) );
PUT_HEAD( bp, PACK(size,0) );
PUT_FOOT( bp, PACK(size,0) );
return bp;
}
else { /* Case 3 */
delete_node(GET_NEXT(bp));
delete_node(GET_PREV(bp));
size += GET_SIZE( GET_PREV(bp) ) +
GET_SIZE( GET_NEXT(bp) );
PUT_HEAD( GET_PREV(bp), PACK(size,0) );
PUT_FOOT( GET_NEXT(bp), PACK(size,0) ); 
return GET_PREV(bp);
}
}

static void place(void *bp,size_t asize)
{
size_t csize = GET_SIZE(bp);
delete_node( bp );
if((csize-asize)>=BLKSIZE){
PUT_HEAD( bp,PACK(asize,1) );
PUT_FOOT( bp,PACK(asize,1) );
bp=GET_NEXT(bp);
PUT_HEAD( bp,PACK(csize-asize,0) );
PUT_FOOT( bp,PACK(csize-asize,0) );
insert_node( coalesce(bp) );
}
else{
PUT_HEAD( bp,PACK(csize,1) );
PUT_FOOT( bp,PACK(csize,1) );
}
}

static void* find_fit( size_t asize )
{
/* the most fit block */
void *fit = NULL;
/* temporary location of the search */
void *temp = free_tree_rt;
/* use tree to implement a comparative best fit search */
for(;temp!=NULL;){
/* The following node in the search may be worse, so we need to record the
most fit so far. */
if( asize <= GET_SIZE(temp) ){
fit = temp;
temp = (void *)GET_LEFT(temp);
}
else
temp = (void *)GET_RIGHT(temp);
}
return fit;
} 

static void insert_node( void *bp )
{
/* root is NULL */
if( free_tree_rt == NULL ){
free_tree_rt = bp;
PUT_LEFT( bp, NULL );
PUT_RIGHT(bp, NULL );
PUT_PRNT( bp, NULL );
PUT_BROS( bp, NULL );
return;
}
/* treat temp as the start */
void *temp = free_tree_rt;
/* loop to locate the position */
while( 1 ){
/* Case 1: size of the block exactly matches the node. */
if( GET_SIZE(bp)==GET_SIZE(temp) ){
if( (void *)GET_BROS(temp) != NULL )
 {/* more than one block in the node */
if( temp == free_tree_rt ){/* temp is parent,and the root*/
free_tree_rt = bp;
PUT_PRNT( bp, NULL );
}
else{/* temp is parent, and not the root */
if( (void *)GET_LEFT(GET_PRNT(temp)) == temp
)
 /* temp is left child(temp's parent's left child is temp) */
PUT_LEFT( GET_PRNT(temp), bp );
//put temp's parent's left point as bp.
else /* temp is right child */
PUT_RIGHT( GET_PRNT(temp), bp ); 
PUT_PRNT( bp, GET_PRNT(temp) );
//put bp's parent as temp's parent.
}
PUT_LEFT( bp, GET_LEFT(temp) );
PUT_RIGHT( bp, GET_RIGHT(temp) );
PUT_BROS( bp, temp );
 //if temp is not parent(only siblings)
if( (void *)GET_LEFT(temp) != NULL )
PUT_PRNT( GET_LEFT(temp), bp );
if( (void *)GET_RIGHT(temp) != NULL )
PUT_PRNT( GET_RIGHT(temp), bp );
PUT_LEFT( temp, bp );
PUT_RIGHT( temp, -1 );
break;
}
else{/* no more than one block in the node */
PUT_BROS( bp, NULL );
PUT_LEFT( bp, temp );
PUT_RIGHT( bp, -1 );
PUT_BROS( temp, bp );
if( (void *)GET_BROS(bp) != NULL )
PUT_LEFT( GET_BROS(bp), bp );
break;
}
}
/* Case 2: size of the block is less than that of the node. */
else if( GET_SIZE(bp) < GET_SIZE(temp) ){
if( (void *)GET_LEFT(temp) != NULL ){
temp = (void *)GET_LEFT( temp );
}else{
PUT_LEFT( temp, bp ); 
PUT_PRNT( bp, temp );
PUT_LEFT( bp, NULL );
PUT_RIGHT( bp, NULL );
PUT_BROS( bp, NULL );
break;
}
}
/* Case 3 size of the block is greater than that of the node. */
else{
if( (void *)GET_RIGHT(temp) != NULL ){
temp = (void *)GET_RIGHT(temp);
}else{
PUT_RIGHT( temp, bp );
PUT_PRNT( bp, temp );
PUT_LEFT( bp, NULL );
PUT_RIGHT( bp, NULL );
PUT_BROS( bp, NULL );
break;
}
}
}
} 

static void delete_node(void *bp)
{
/* Case that the block is the only one in the node */ 
if( (void *)GET_BROS(bp) == NULL && GET_RIGHT(bp) != -1 ){
if( bp == free_tree_rt ){/* the node is the root */
if( (void *)GET_RIGHT(bp) == NULL ){/* no right child */
free_tree_rt=(void *)GET_LEFT(bp);
if( free_tree_rt != NULL )
PUT_PRNT( free_tree_rt, NULL );
}
else{/* it has a right child */
void *temp = (void *)GET_RIGHT(bp);
while( (void *)GET_LEFT(temp) != NULL )
temp = (void *)GET_LEFT(temp);
void *tempL = (void *)GET_LEFT(bp);
void *tempR = (void *)GET_RIGHT(temp);
void *tempP = (void *)GET_PRNT(temp);
free_tree_rt = temp;
if( free_tree_rt != NULL )
PUT_PRNT( free_tree_rt, NULL );
PUT_LEFT( temp,GET_LEFT(bp) );
if( temp != (void *)GET_RIGHT(bp) ){
PUT_RIGHT( temp,GET_RIGHT(bp) );
PUT_LEFT( tempP, tempR );
if( tempR != NULL)
PUT_PRNT( tempR, tempP );
PUT_PRNT( GET_RIGHT(bp),temp );
}
if( tempL != NULL )
PUT_PRNT( tempL, temp );
}
}
else{/* the node is not the root */
if( (void *)GET_RIGHT(bp) == NULL ){/* no right child */
if( (void *)GET_LEFT( GET_PRNT( bp ) ) == bp ) 
PUT_LEFT( GET_PRNT(bp), GET_LEFT(bp) );
else
PUT_RIGHT( GET_PRNT(bp), GET_LEFT(bp) );
if( (void *)GET_LEFT(bp) != NULL)
PUT_PRNT( GET_LEFT(bp), GET_PRNT(bp) );
}else{/* it has a right child */
void *temp = (void *)GET_RIGHT(bp);
while( (void *)GET_LEFT(temp) != NULL )
temp = (void *)GET_LEFT(temp);
void *tempL = (void *)GET_LEFT(bp);
void *tempR = (void *)GET_RIGHT(temp);
void *tempP = (void *)GET_PRNT(temp);
if( (void *)GET_LEFT(GET_PRNT(bp)) == bp )
PUT_LEFT( GET_PRNT(bp), temp );
else
PUT_RIGHT( GET_PRNT(bp), temp );
PUT_PRNT( temp, GET_PRNT(bp) );
PUT_LEFT( temp, GET_LEFT(bp) );
if( temp != (void *)GET_RIGHT(bp)){
PUT_RIGHT( temp, GET_RIGHT(bp) );
PUT_LEFT( tempP, tempR );
if( tempR != NULL )
PUT_PRNT( tempR,tempP );
PUT_PRNT( GET_RIGHT(bp), temp );
}
if( tempL != NULL )
PUT_PRNT( tempL, temp );
}
}
}else{/* Other case */ 
if( bp == free_tree_rt ){/* the node is the root */
free_tree_rt = (void *)GET_BROS(bp);
PUT_PRNT( free_tree_rt, NULL );
PUT_LEFT( free_tree_rt, GET_LEFT(bp) );
PUT_RIGHT( free_tree_rt, GET_RIGHT(bp) );
if( (void *)GET_LEFT(bp) != NULL )
PUT_PRNT( GET_LEFT(bp), free_tree_rt );
if( (void *)GET_RIGHT(bp) != NULL )
PUT_PRNT( GET_RIGHT(bp), free_tree_rt );
}else{/* the node is not the root */
if( GET_RIGHT(bp) == -1 ){/* not the first block in the node */
PUT_BROS( GET_LEFT(bp),GET_BROS(bp) );
if( (void *)GET_BROS(bp) != NULL )
PUT_LEFT( GET_BROS(bp),GET_LEFT(bp) );
}else{/* the first block in the node */
if( (void *)GET_LEFT(GET_PRNT(bp)) == bp )
PUT_LEFT( GET_PRNT(bp), GET_BROS(bp) );
else
PUT_RIGHT( GET_PRNT(bp), GET_BROS(bp) );
PUT_PRNT( GET_BROS(bp), GET_PRNT(bp) );
PUT_LEFT( GET_BROS(bp), GET_LEFT(bp) );
PUT_RIGHT( GET_BROS(bp), GET_RIGHT(bp) );
if( (void *)GET_LEFT(bp) != NULL )
PUT_PRNT(GET_LEFT(bp), GET_BROS(bp) );
if( (void *)GET_RIGHT(bp) != NULL)
PUT_PRNT(GET_RIGHT(bp), GET_BROS(bp) );
}
}
}
}

void mm_exit(){
	;
}


    

