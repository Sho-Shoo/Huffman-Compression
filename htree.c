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
#include <string.h>
#include <assert.h>
#include <ctype.h>

#include "lib/contracts.h"
#include "lib/xalloc.h"
#include "lib/file_io.h"
#include "lib/heaps.h"

#include "freqtable.h"
#include "htree.h"

/* in huffman.h: */
/* typedef struct htree_node htree; */
struct htree_node {
  symbol_t value;
  unsigned int frequency;
  htree *left;
  htree *right;
};

/**************************************/
/* Checking data structure invariants */
/**************************************/

bool is_htree(htree *H);
bool is_htree_leaf(htree *H);
bool is_htree_interior(htree *H);

/***************************************/
/* Huffman trees from frequency tables */
/***************************************/

// build a htree from a frequency table
//htree* build_htree(freqtable_t table);

// True if H is a leaf node
bool hleaf(htree *H) {
  if (H == NULL) return false;
  return H->left == NULL && H->right == NULL;
}


void print_htree_aux(htree *H, bit_t *b, size_t b_len) {
  REQUIRES(is_htree(H));
  if (hleaf(H)) {
    symbol_t c = H->value;
    unsigned int f = H->frequency;
    if (isprint((char)c)) printf("  '%c' (frequency %u): %s\n",   c, f, b);
    else                  printf("  \\%02X (frequency %u): %s\n", c, f, b);
    free(b);
    return;
  }

  ASSERT(is_htree_interior(H));
  bit_t *left  = xcalloc(sizeof(bit_t), b_len + 2);
  bit_t *right = xcalloc(sizeof(bit_t), b_len + 2);
  strcpy(left,  b);
  strcpy(right, b);
  free(b);
  left[b_len]  = '0';
  right[b_len] = '1';
  print_htree_aux(H->left,  left,  b_len + 1);
  print_htree_aux(H->right, right, b_len + 1);
}

// Print Huffman tree
void print_htree(htree *H) {
  REQUIRES(is_htree_interior(H));
  printf("Huffman tree:\n");
  size_t b_len = 0;   // index where to write next character
  bit_t *left  = xcalloc(sizeof(bit_t), b_len + 2);
  bit_t *right = xcalloc(sizeof(bit_t), b_len + 2);
  strcpy(left,  "0");
  strcpy(right, "1");
  print_htree_aux(H->left,  left,  b_len + 1);
  print_htree_aux(H->right, right, b_len + 1);
  printf("\n");
}


// Dispose of a htree
void htree_free(htree *H) {
  if (H != NULL) {
    htree_free(H->left);
    htree_free(H->right);
    free(H);
  }
}


/*******************************************/
/* Building code tables from Huffman trees */
/*******************************************/

// Checks whether s is a string of '0' and '1'
bool is_bitstring(bit_t *s) {
  if (s == NULL) return false;
  unsigned int len = strlen(s);
  for (unsigned int i = 0; i < len; i++)
    if (!(s[i] == '0' || s[i] == '1')) return false;
  return true;
}

// Checks whether table is a valid code table
bool is_codetable(codetable_t table) {
  //@requires \length(table) == NUM_LETTER;
  if (table == NULL) return false;

  unsigned short n = 0;  // Number of distinct symbols in use
  for (unsigned short c = 0; c < NUM_SYMBOLS; c++)
    if (table[c] != NULL) {
      n++;
      if (!is_bitstring(table[c])) return false;
    }
  if (n <= 1) return false; // not enough symbols in use
  return true;
}

// Returns code table for characters in H
//codetable_t htree_to_codetable(htree *H);

// Add bogus frequencies to a bare htree to make is_htree happy
void fix_frequencies(htree *H) {
  REQUIRES(H != NULL);
  if (hleaf(H))
    H->frequency = 1;
  else {
    fix_frequencies(H->left);
    fix_frequencies(H->right);
    H->frequency = H->left->frequency + H->right->frequency;
  }
  ENSURES(is_htree(H));
}

// Creates H based on a code table
htree *htree_from_codetable(codetable_t table) {
  htree *H = xcalloc(1, sizeof(htree));
  for (unsigned short c = 0; c < NUM_SYMBOLS; c++)
    if (table[c] != NULL) {
      bitstring_t code = table[c];
      htree *p = H;
      for (unsigned short i = 0; i < strlen(code); i++) {
        if (code[i] == '0') {
          if (p->left == NULL)
            p->left = xcalloc(1, sizeof(htree));
          p = p->left;
        }
        if (code[i] == '1') {
          if (p->right == NULL)
            p->right = xcalloc(1, sizeof(htree));
          p = p->right;
        }
      }
      p->value = c;
    }
  fix_frequencies(H);
  ENSURES(is_htree(H));
  return H;
}


// Read code table from file (or STDIN)
codetable_t read_codetable(char *fname) {
  unsigned int max_line_length = 50;  // Longest expected line
  char *line = xcalloc(max_line_length, sizeof(char));
  codetable_t table = xcalloc(NUM_SYMBOLS, sizeof(char*));

  FILE *stream = xfopen(fname, "r");
  while (fgets(line, max_line_length, stream) != NULL) {
    char c;      // printable characters
    int i;       // non-printable characters
    bit_t *bits = xcalloc(strlen(line), sizeof(bit_t)); // associated bitstring
    if (sscanf(line, "%1c:%s\n", &c, bits) == 2)
      table[(symbol_t)c] = bits;
    else if (sscanf(line, "%i:%s\n", &i, bits) == 2)
      table[(symbol_t)i] = bits;
    else if (sscanf(line, "\n") == 0) {}  // Skip empty lines
    else {
      fprintf(stderr, "Could not parse line %s\n", line);
      exit(1);
    }
  }
  if (fname != NULL) fclose(stream);
  free(line);

  ENSURES(is_codetable(table));
  return table;
}

// Write code table to file
void write_codetable(codetable_t table, char *fname) {
  REQUIRES(is_codetable(table));
  FILE *stream = xfopen(fname, "w");
  for (unsigned short c = 0; c < NUM_SYMBOLS; c++) {
    char *s = table[(symbol_t)c];
    if (s != NULL) {
      if (isprint(c)) fprintf(stream, "%c:%s\n",     c, s);
      else            fprintf(stream, "0x%02X:%s\n", c, s);
    }
  }
  if (fname != NULL) fclose(stream);
}

// Print code table
void print_codetable(codetable_t table) {
  REQUIRES(is_codetable(table));
  printf("Code table:\n");
  for (unsigned short c = 0; c < NUM_SYMBOLS; c++)
    if (table[c] != NULL) {
      if (isprint((char)c)) printf("  '%c': %s\n",   c, table[c]);
      else                  printf("  \\%02X: %s\n", c, table[c]);
    }
  printf("\n");
}


// Number of letters in use in code table
unsigned int codetable_size(codetable_t table) {
  REQUIRES(is_codetable(table));
  unsigned int size = 0;
  for (unsigned int i = 0; i < NUM_SYMBOLS; i++)
    if (table[i] != NULL) size++;
  return size;
}

// Overall length of all letters in use in code table
size_t total_code_length(codetable_t table) {
  REQUIRES(is_codetable(table));
  size_t size = 0;
  for (unsigned int i = 0; i < NUM_SYMBOLS; i++)
    if (table[i] != NULL) size += strlen(table[i]);
  return size;
}

// Dispose of code table
void codetable_free(codetable_t table) {
  REQUIRES(is_codetable(table));
  for (unsigned short c = 0; c < NUM_SYMBOLS; c++)
    /* free string stored in code table */
    if (table[c] != NULL) free(table[c]);
  /* free code table itself */
  free(table);
}
