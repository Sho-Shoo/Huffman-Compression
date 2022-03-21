/**************************************************************************/
/*              COPYRIGHT Carnegie Mellon University 2021                 */
/* Do not post this file or any derivative on a public site or repository */
/**************************************************************************/
/* Huffman coding
 *
 * 15-122 Principles of Imperative Computation
 */

#include <stdlib.h>
#include <stdbool.h>
#include <stdio.h>
#include <string.h>
#include <assert.h>
#include <ctype.h>

#include "lib/contracts.h"
#include "lib/xalloc.h"
#include "lib/file_io.h"
#include "lib/heaps.h"

#include "freqtable.h"
#include "htree.h"
#include "encode.h"
#include "bitpacking.h"

// Print error message
void error(char *msg) {
  fprintf(stderr, "%s\n", msg);
  exit(1);
}

/* in htree.h: */
/* typedef struct htree_node htree; */
struct htree_node {
  symbol_t value;
  unsigned int frequency;
  htree *left;
  htree *right;
};

/**********************************************/
/* Task 1: Checking data structure invariants */
/**********************************************/

/* forward declaration -- DO NOT MODIFY */
bool is_htree(htree *H);

bool is_htree_leaf(htree *H) {
  if(H == NULL) return false; // Not a tree leaf if it is a NULL pointer 
  if(H->frequency <= 0) return false; // Freq must be strictly positive 
  // Left and right children must be NULL
  return H->left == NULL && H->right == NULL; 
}

bool is_htree_interior(htree *H) {
  if(H == NULL) return false; // Must be non-NULL
  // H's left and right children must also be valid trees 
  if(!(is_htree(H->left) && is_htree(H->right))) return false; 
  // Freq of H must match the sum of freq of its children 
  return H->frequency == H->left->frequency + H->right->frequency; 
}

bool is_htree(htree *H) {
  if(H == NULL) return false; // Must be non-NULL
  return is_htree_leaf(H) || is_htree_interior(H); 
}

/********************************************************/
/* Task 2: Building Huffman trees from frequency tables */
/********************************************************/

/* for lib/heaps.c */
// Tree nodes with lower frequencies would have higher priority 
// Returns true if e1 is STRICTLY higher priority than e2
bool htree_higher_priority(elem e1, elem e2) {
  REQUIRES(e1 != NULL); 
  REQUIRES(e2 != NULL); 

  // No \hastag()? Really? 
  htree *tree1 = (htree*) e1; 
  htree *tree2 = (htree*) e2; 
  ASSERT(is_htree(tree1)); // For safety 
  ASSERT(is_htree(tree2)); // For safety 

  return tree1->frequency < tree2->frequency; // Must be strict 
}

// Build a priority queue from a freqtable 
void build_pq(pq_t Q, freqtable_t table)
{
  REQUIRES(table != NULL); 
  REQUIRES(Q != NULL && pq_empty(Q)); 

  int char_count = 0; 
  // This choice of type of i might be DANGEROUS, we'll see 
  for(int i = 0; i < NUM_SYMBOLS; i++)  
  {
    unsigned int freq = table[i]; 
    if(freq > 0) // The char occurs in the text 
    {
      char_count++; 
      htree *node = xmalloc(sizeof(htree)); 
      // Initialize the htree node 
      node->value = i; 
      node->frequency = freq; 
      node->left = NULL; 
      node->right = NULL; 

      ASSERT(!pq_full(Q)); // For safety 
      pq_add(Q, (elem) node); // Add the node into the priority queue 
    }
  }
  // Signal error if strictly less than 2 distinct characters 
  if(char_count < 2) error("Only 0 or 1 distinct character in the text"); 
}

void free_htree(htree *tree)
{
  REQUIRES(is_htree(tree)); 

  if(is_htree_leaf(tree)) // This is base case 
  {
    free(tree); 
  }

  ASSERT(is_htree_interior(tree)); // For safety 
  // Recursion case 
  free_htree(tree->left); 
  free_htree(tree->right); 
  free(tree);
}

// typedef void elem_free_fn(elem e);
void elem_free(elem e) // Wrapper function 
{
  htree *tree = (htree*) e; 
  ASSERT(is_htree(tree)); 
  free_htree(tree); 
}

// build a htree from a frequency table
htree* build_htree(freqtable_t table) {
  // Initialize a new priority queue 
  pq_t Q = pq_new((int) NUM_SYMBOLS, &htree_higher_priority, &elem_free); 
  build_pq(Q, table); // Fill the priority queue with htree elements 

  // Merge the trees in priority queue 
  while(!pq_empty(Q))
  {
    htree *tree1 = (htree*) pq_rem(Q); 
    ASSERT(is_htree(tree1)); // For safety 

    if(pq_empty(Q)) { // tree1 is the last tree in the pq, then return it 
      pq_free(Q); 
      return tree1; 
    }

    htree *tree2 = (htree*) pq_rem(Q); 
    ASSERT(is_htree(tree2)); // For safety 

    // Initialize a root node for tree1 and tree2
    htree *root = xmalloc(sizeof(htree)); // This should always be a innner node
    root->value = (symbol_t) 0; // Does not really matter 
    root->frequency = tree1->frequency + tree2->frequency; 
    root->left = NULL; 
    root->right = NULL; 

    if(tree1->frequency <= tree2->frequency)  // Modify: = added
    // If tree1 has lower frequency, tree1 on left
    {
      root->left = tree1; 
      root->right = tree2; 
    } else { // tree2 on left, tree1 on right
      root->left = tree2; 
      root->right = tree1; 
    }
    ASSERT(!pq_full(Q)); // For safety 
    pq_add(Q, (elem) root); 
  }

  // Don't really want to be here, actually return statement in the loop
  assert(false); 
  pq_free(Q); 
  return NULL; 
}


/*******************************************/
/*  Task 3: decoding a text                */
/*******************************************/

// Find the length of the code corresponding to the tree 
size_t find_len(htree *H, bit_t *code)
{
  REQUIRES(is_htree(H)); 
  REQUIRES(code != NULL); 

  size_t res = 0; 

  htree *node  = H; 
  for(size_t i = 0; code[i] != '\0'; i++)
  {
    // printf("code is %c here!\n", code[i]);

    if(code[i] == '0'){
      node = node->left;  // 0 means to left 
    } 
    else { // ASSERT(code[i] == '1');
      node = node->right; // 1 mean go right 
    }

    if(is_htree_leaf(node)) { // Encounters a leaf node, set back to the root 
      res++; 
      node = H; 
    }

  }

  if(node != H) error("Invalid code to decode!"); 

  return res; 

}


void parse_code(htree *H, bit_t *code, symbol_t *res, size_t len)
// Note that res is of length len 
{
  REQUIRES(is_htree(H)); 
  REQUIRES(code != NULL); 
  REQUIRES(res != NULL); 

  // Loop initialization 
  htree *node  = H; 
  size_t array_ind = 0; 

  for(size_t i = 0; code[i] != '\0'; i++)
  {
    if(code[i] == '0'){
      node = node->left;  // 0 means to left 
    } 
    else { // ASSERT(code[i] == '1');
      node = node->right; // 1 mean go right 
    }

    if(is_htree_leaf(node)) { // Encounters a leaf node, set back to the root 
      res[array_ind] = node->value; 
      array_ind++; 
      node = H; 
    }
  }
  assert(len == array_ind);
}

// Decode code according to H, putting decoded length in src_len
symbol_t* decode_src(htree *H, bit_t *code, size_t *src_len) {
  REQUIRES(is_htree(H)); 
  REQUIRES(code != NULL); 
  REQUIRES(src_len != NULL); 

  // First pass to get the src_len 
  size_t len = find_len(H, code); 
  *src_len = len; 

  // Second pass to obtain the symbol_t array 
  symbol_t *res = xcalloc(len, sizeof(symbol_t)); 
  parse_code(H, code, res, len); 

  return res; 
}


/***************************************************/
/* Task 4: Building code tables from Huffman trees */
/***************************************************/

// Return a heap allocated bitstring identical as the stack allocated str 
bitstring_t create_char_ptr(char str[])
{
  int len; // Document the lenth of the output string, including '\0'
  for(len = 0; str[len] != '\0'; len++) {;} 
  len ++; 

  bitstring_t res = xcalloc(len, sizeof(bit_t)); 
  for(int i = 0; i < len; i++)
  {
    ASSERT(str[i] == '\0' || str[i] == '0' || str[i] == '1');
    res[i] = str[i]; 
  }

  return res; 

}

// This function populates table with information in H 
// prev_string documents the previous path taken
void htree_to_codetable_body(htree *H, codetable_t table, 
                             bitstring_t prev_string) 
{
  REQUIRES(is_htree(H)); 

  if(is_htree_leaf(H)){ // Base case here
    table[H->value] = prev_string; 
    return; 
  }

  ASSERT(is_htree_interior(H)); 

  bitstring_t next_path_left = xcalloc(sizeof(bit_t), strlen(prev_string)+2);
  strcpy(next_path_left, prev_string); 
  strcat(next_path_left, "0"); // Go left, set second to last bit to 0 
  htree_to_codetable_body(H->left, table, next_path_left); 

  bitstring_t next_path_right = xcalloc(sizeof(bit_t), strlen(prev_string)+2); 
  strcpy(next_path_right, prev_string); 
  strcat(next_path_right, "1"); // Go right, set second to last bit to 1
  htree_to_codetable_body(H->right, table, next_path_right); 

  free(prev_string);

  return ;

}

size_t max(size_t x, size_t y)
{
  if(x > y) return x; 
  else return y; 
}

// Find the maximum depth of the htree
size_t max_depth(htree *H)
{
  REQUIRES(is_htree(H)); 

  if(is_htree_leaf(H)){ // Base case 
    return 1; 
  }

  ASSERT(is_htree_interior(H)); 

  return max(max_depth(H->left), max_depth(H->right)) + (size_t) 1; 
}


// Returns code table for characters in H
codetable_t htree_to_codetable(htree *H) {
  REQUIRES(is_htree(H)); 

  codetable_t table = xcalloc(NUM_SYMBOLS, sizeof(bitstring_t)); 

  bitstring_t empty_bstring = xcalloc(sizeof(bit_t), 1);
  htree_to_codetable_body(H, table, empty_bstring); 

  // ENSURES(is_codetable(table));
  return table; 
}


/*******************************************/
/*  Task 5: Encoding a text                */
/*******************************************/

// Get the size of encoded bit string 
size_t get_size(codetable_t table, symbol_t *src, size_t src_len)
{
  REQUIRES(src != NULL); 
  // REQUIRES(is_codetable(table)); 

  size_t size = 0; 
  for(size_t i = 0; i < src_len; i++)
  {
    bitstring_t bs = table[src[i]]; // Extract bitstring from the codetable 
    size += strlen(bs);
  }

  return size; 
}

void populate_bstring(bit_t *target_bs ,codetable_t table, 
                      symbol_t *src, size_t src_len, size_t curr_ind)
{
  REQUIRES(target_bs != NULL);
  REQUIRES(src != NULL); 
  // REQUIRES(is_codetable(table));

  for(size_t i = 0; i < src_len; i++)
  {
    bitstring_t bs = table[src[i]]; // Extract bitstring from the codetable
    strcpy(target_bs+curr_ind, bs); 
    curr_ind += strlen(bs); 
  }

}

// Encodes source according to codetable
bit_t* encode_src(codetable_t table, symbol_t *src, size_t src_len) {
  REQUIRES(src != NULL); 
  // REQUIRES(is_codetable(table));

  size_t res_size = get_size(table, src, src_len) + 1; 
  bit_t *res = xcalloc(sizeof(bit_t), res_size); 
  populate_bstring(res, table, src, src_len, 0);

  return res; 
}


/**************************************************/
/*  Task 6: Building a frequency table from file  */
/**************************************************/

// Build a frequency table from a source file (or STDIN)
freqtable_t build_freqtable(char *fname) {

  FILE *descr = fopen(fname, "r"); 
  freqtable_t table = xcalloc(sizeof(unsigned int), NUM_SYMBOLS); 

  // Loop through the file 
  for(int c = fgetc(descr); c != EOF; c = fgetc(descr))
  {
    ASSERT(0 <= c && c < NUM_SYMBOLS); // For safety 
    table[c]++; // Frequency of character c increments 
  }

  fclose(descr); // Close the file describer 

  // ENSURES(is_freqtable(table));
  return table; 
}



/************************************************/
/*  Task 7: Packing and unpacking a bitstring   */
/************************************************/

// Get the length the unit8_t array 
size_t get_res_len(size_t bits_len)
{
  size_t step = 8; // Packing into unit8_t, so a step should be 8 bits 

  if(bits_len%step == 0) return bits_len/step; 
  else return bits_len/step + 1; 
}

void populate_byte_array(uint8_t *bytes, size_t bytes_len, bit_t *bits)
{
  size_t step = 8; 

  // Loop through the byte array 
  for(size_t i = 0; i < bytes_len; i++)
  {
    ASSERT(i*step < strlen(bits)); // For safety 
    bit_t *starting_bit = bits + i*step; // Current byte's starting point in bits
    uint8_t byte = 0; // Record the current byte value; 
    uint8_t placeval = 128; // Place value of a bit
    for(size_t j = 0; j < step; j++)
    {
      // If reaching the end of the bits array 
      if(starting_bit[j] == '\0') break; 
      else if(starting_bit[j] == '1') byte += placeval*1; 
      else {  // Do nothing in this case
        ASSERT(starting_bit[j] == '0'); 
      }
      

      ASSERT(placeval > 0); // placeval should be at least 1 
      placeval /= 2; 
    }

    bytes[i] = byte; 

  }
}

// Pack a string of bits into an array of bytes
uint8_t* pack(bit_t *bits) {

  size_t len = strlen(bits); 
  // First pass, get the length of output 
  size_t res_len = get_res_len(len); 
  uint8_t *res = xcalloc(sizeof(uint8_t), res_len); 
  // Second pass, filling the uint8 array w/ bytes 
  populate_byte_array(res, res_len, bits); 
  
  ENSURES(res != NULL);
  return res; 
}


//**************************************************************************//

// Fill the next 8 bits starting from starting_bit with the content to byte 
void byte2bit(bit_t *starting_bit, uint8_t byte)
{
  size_t step = 8; 
  // Loop through <step> times 
  for(size_t i = 0; i < step; i++)
  {
    size_t shift_place = step - i - 1; // Number of places shifted by 
    uint8_t digit = (byte >> shift_place) & 0x01; 
    ASSERT(digit == (uint8_t) 1 || digit == (uint8_t) 0); // For safety 

    if(digit == (uint8_t) 1) starting_bit[i] = '1'; 
    else                     starting_bit[i] = '0'; 
  }
  
}



// Unpack an array of bytes c of length len into a NUL-terminated string of ASCII bits
bit_t* unpack(uint8_t *c, size_t len) {
  // Length of res bits array should be 8 * <length of uint8 array>
  // The last is reserved for the NUL terminator 
  size_t step = 8;
  bit_t* bits = xcalloc(sizeof(bit_t), step*len+1);
  // size_t bits_len = step*len; 

  // Loop thru the byte array 
  for(size_t i = 0; i < len; i++)
  {
    uint8_t byte = c[i]; 
    // ASSERT(step*i < bits_len); 
    bit_t *starting_bit = bits + step*i; 
    byte2bit(starting_bit, byte); 
  }

  return bits;  
}
