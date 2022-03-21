/**************************************************************************/
/*              COPYRIGHT Carnegie Mellon University 2021                 */
/* Do not post this file or any derivative on a public site or repository */
/**************************************************************************/
/* Encoding and decoding a file given a frequency table
 *
 * 15-122 Principles of Imperative Computation
 */

#include <stdlib.h>
#include <stdbool.h>
#include <stdio.h>

#include "freqtable.h"

#ifndef _HTREE_H_
#define _HTREE_H_

// Huffman trees
typedef struct htree_node htree;

// True if H is a leaf node
bool hleaf(htree *H);
// build an htree from a frequency table
htree* build_htree(freqtable_t ftable);
// print an htree
void print_htree(htree *H);
// dispose of a htree
void htree_free(htree *H);

// Bitstrings
typedef char bit_t;                   // Type of bits
typedef bit_t *bitstring_t;           // Type of bitstrings
bool is_bitstring(bitstring_t bits);  // Valid NUL-terminated bitstring

// Code tables
typedef bitstring_t *codetable_t;
bool is_codetable(codetable_t table);  // Valid code table

// build a code table from an htree
codetable_t htree_to_codetable(htree *H);
// build an htree from a code table
htree* htree_from_codetable(codetable_t table);
// Read code table from file (or STDIN)
codetable_t read_codetable(char *fname);
// Write code table to file
void write_codetable(codetable_t table, char *fname);
// print a code table
void print_codetable(codetable_t table);
// return the number of symbols in use in a code table
unsigned int codetable_size(codetable_t table);
// return the overall length of the codes in a code table
size_t total_code_length(codetable_t table);
// dispose of a code table
void codetable_free(codetable_t table);

#endif /* _HTREE_H_ */
