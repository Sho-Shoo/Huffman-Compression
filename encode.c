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

#include "htree.h"
#include "encode.h"


bool h_verbose = false;
void verbose_huffman() {
  h_verbose = true;
}


/*******************************************/
/*  Encoding and decoding a text           */
/*******************************************/

// Encodes source according to codetable, putting encoded length in code_len
//bit_t* encode_src(codetable_t table, symbol_t *src, size_t src_len);

// Decode code according to H, putting decoded length in src_len
//symbol_t* decode_src(htree *H, bit_t *code, size_t *src_len);

// Prints a source and code string synchronized, symbol by symbol
void prettyprint(codetable_t table,
                 symbol_t *src,  size_t  src_len,
                 bit_t   *code,  size_t code_len,
                 unsigned int max) {
  REQUIRES(is_codetable(table));

  char *pretty_src  = xcalloc(src_len + code_len + 1, sizeof(char));
  char *pretty_code = xcalloc(src_len + code_len + 1, sizeof(char));
  size_t pretty_idx = 0;

  size_t code_idx = 0;
  for (size_t i = 0; i < src_len && i < max; i++) {
    symbol_t c = src[i];
    if (table[c] == NULL) {
      fprintf(stderr, "Symbol %c (0x%02X) has no associated code\n",
              isprint(c) ? c : (symbol_t)0xFF, c);
      exit(1);
    }
    size_t len = strlen(table[c]);  // Expected code length of c
    strncpy(pretty_code + pretty_idx, code + code_idx, len);
    pretty_code[pretty_idx + len] = ' ';
    pretty_src[pretty_idx] = isprint(c) ? c : (symbol_t)0xFF;
    for (size_t w = 0; w < len; w++)
      pretty_src[pretty_idx + w+1] = ' ';
    pretty_idx += len + 1;
    code_idx += len;
  }
  pretty_src[pretty_idx]  = '\0';
  pretty_code[pretty_idx] = '\0';

  printf("%s\n%s\n", pretty_src, pretty_code);

  free(pretty_src);
  free(pretty_code);
}

// Encodes source file to code file according to codetable
void encode(codetable_t table, char *src_fname, char *code_fname) {
  size_t src_len;
  symbol_t *src = (symbol_t*)read_file_to_byte_array(src_fname, &src_len);

  if (h_verbose) {
    printf("==> Calling your encode_src ...         ");
    fflush(stdout);
  }
  bit_t *code = encode_src(table, src, src_len);
  if (h_verbose) printf("called!\n");
  size_t code_len = strlen(code);
  if (h_verbose) prettyprint(table, src, src_len, code, code_len, src_len);

  FILE *code_stream = xfopen(code_fname, "w");
  fwrite(code, sizeof(bit_t), code_len, code_stream);
  if (code_fname != NULL) fclose(code_stream);

  printf("\nEncoded %u characters (%u bits) into %u bits\n",
         (unsigned int)src_len, (unsigned int)(8*src_len), (unsigned int)code_len);
  free(src);
  free(code);
}


// Decode code file to source file according to H
// (table is NULL except possibly in verbose mode)
void decode(htree *H, char *code_fname, char *src_fname, codetable_t table) {
  size_t code_len;
  bit_t *code = (bit_t *)read_file_to_char_array(code_fname, &code_len);
  size_t src_len;
  if (h_verbose) {
    printf("==> Calling your decode_src ...         ");
    fflush(stdout);
  }
  symbol_t *src = decode_src(H, code, &src_len);
  if (h_verbose) printf("called!\n");
  if (h_verbose) {
    printf("==> Calling your htree_to_codetable ... ");
    fflush(stdout);
    codetable_t table_computed = htree_to_codetable(H);
    if (table_computed != NULL) {
      printf("called!\n");
      prettyprint(table_computed, src, src_len, code, code_len, src_len);
      codetable_free(table_computed);
    }
    else {
      printf("failed (but this may not be bad)\n");
      if (table != NULL) {
        prettyprint(table, src, src_len, code, code_len, src_len);
        // table is freed by main
      }
      else {
        printf("\tTo display the encoded and decoded texts in lockstep, you need\n");
        printf("\t- either to supply a frequency file with the -f option,\n");
        printf("\t- or to implement htree_to_codetable\n");
      }
    }
  }

  FILE *src_stream =  xfopen(src_fname, "w");
  fwrite(src, sizeof(symbol_t), src_len, src_stream);
  if (src_fname != NULL) fclose(src_stream);

  printf("\nDecoded %u bits into %u characters (%u bits)\n",
         (unsigned int)code_len, (unsigned int)src_len, (unsigned int)(8*code_len));
  free(src);
  free(code);
}
