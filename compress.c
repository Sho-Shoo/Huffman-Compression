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
#include <stdint.h>

#include "lib/contracts.h"
#include "lib/xalloc.h"
#include "lib/file_io.h"

#include "encode.h"
#include "compress.h"


bool c_verbose = false;
void verbose_compress() {
  c_verbose = true;
}
bool v_verbose = false;
void very_verbose_compress() {
  v_verbose = true;
}


/* Compressed file format:
uint32_t                 - magic: magic number
uint16_t                 - code_start: offset of code_len (see below)
uint8_t                  - num_symbols8: number of symbols in use
uint8_t[num_symbols8]    - letters_in_use: symbols in use
uint8_t[num_symbols8]    - code_sizes: size of code of each symbol in use
uint8_t*                 - padded_letter_codes: concatenation of codes of the
                           symbols in use, padded to the next byte
uint32_t                 - code_len: length of compressed code
uint8_t[padded_code_len] - code: compressed code, padded to next byte
*/

// Compress src to file fname (or STDOUT) using codetable table
//   fname_size is the number of bytes written to fname
void compress_src(codetable_t table, symbol_t *src, size_t src_len,
                  char *fname, size_t *fname_size) {
  FILE *stream = xfopen(fname, "w");

  if (c_verbose) {
    printf("Compressing text using\n");
    print_codetable(table);
  }
  // Magic number
  uint32_t magic = MAGIC;
  fwrite(&magic, sizeof(uint32_t), 1, stream);

  // Starting position of code segment
  unsigned int num_symbols = codetable_size(table);  // may be NUM_SYMBOLS
  size_t table_len = total_code_length(table);
  uint16_t code_start = sizeof(uint8_t) // num_symbols
        + num_symbols * sizeof(uint8_t) // letters
        + num_symbols * sizeof(uint8_t) // code length of each letter
        + num_padded_bytes(table_len) * sizeof(uint8_t); // letter codes

  fwrite(&code_start, sizeof(uint16_t), 1, stream);
  if (v_verbose)
    printf("Code segment starts at byte %u\n", code_start);

  // Number of symbols in use
  uint8_t num_symbols8 = (uint8_t)num_symbols; // cast to byte
  fwrite(&num_symbols8, sizeof(uint8_t), 1, stream);
  if (v_verbose)
    printf("%u letters in use:\n", num_symbols);
  // Each symbol in use
  for (unsigned short i = 0; i < NUM_SYMBOLS; i++)  // Write letters
    if (table[i] != NULL) { // symbol is in use
      fwrite(&i, sizeof(uint8_t), 1, stream);
      //if (v_verbose) printf("  - Wrote '%c' (0x%02X)\n", i, i);
    }
  // Size of each symbol in use
  for (unsigned short i = 0; i < NUM_SYMBOLS; i++)  // Write letter code lengths
    if (table[i] != NULL) { // symbol is in use
      uint8_t cl = strlen(table[i]);
      fwrite(&cl, sizeof(uint8_t), 1, stream);
      //if (v_verbose) printf("  #  Code of '%c' (0x%02X) -> %s (%u bits) \n", i, i, table[i], cl);
    }

  // Code of each symbol in use
  bit_t *letter_codes = xcalloc(table_len + 1, sizeof(bit_t));
  uint8_t  c = 0;  // Character
  uint16_t k = 0;  // Code
  for (unsigned short i = 0; i < NUM_SYMBOLS; i++)  // Write letters
    if (table[i] != NULL) { // character is in use
      uint8_t cl = strlen(table[i]);
      strcpy(letter_codes + k, table[i]);
      c++;
      k +=cl;
      if (v_verbose)
        printf("  #  Code of '%c' (0x%02X) -> %s (%u bits) \n",
               i, i, table[i], cl);
    }
  if (c_verbose) {
    printf("==> Calling your pack ...               ");
    fflush(stdout);
  }
  uint8_t *padded_codes = pack(letter_codes);
  if (c_verbose) printf("called!\n");
  //if (v_verbose) printf("done packing %u bytes (%u bits)\n", num_padded_bytes(table_len), (unsigned int)table_len);
  free(letter_codes);
  fwrite(padded_codes, sizeof(uint8_t), num_padded_bytes(table_len), stream);
  free(padded_codes);

  if (c_verbose) {
    printf("==> Calling your encode_src ...         ");
    fflush(stdout);
  }
  bit_t *bits = encode_src(table, src, src_len);
  if (c_verbose) printf("called!\n");
  uint32_t bits_len = (uint32_t)strlen(bits);

  // Source length
  fwrite(&bits_len, sizeof(uint32_t), 1, stream);
  // Source message
  if (c_verbose) {
    printf("==> Calling your pack ...               ");
    fflush(stdout);
  }
  uint8_t *padded_bits = pack(bits);
  if (c_verbose) printf("called!\n");
  free(bits);
  fwrite(padded_bits, sizeof(uint8_t), num_padded_bytes(bits_len), stream);
  free(padded_bits);

  *fname_size = file_size(stream);
  fclose(stream);
}


void compress(char *src_fname, char *code_fname) {
  size_t src_len;
  symbol_t *src = (symbol_t *)read_file_to_byte_array(src_fname, &src_len);

  freqtable_t F = build_freqtable(src_fname);
  if (c_verbose) {
    printf("==> Calling your build_htree ...        ");
    fflush(stdout);
  }
  htree *H  = build_htree(F);
  if (c_verbose) printf("called!\n");
  if (c_verbose) { printf("==> Calling your htree_to_codetable ... ");
    fflush(stdout);
  }
  codetable_t C = htree_to_codetable(H);
  if (c_verbose) printf("called!\n");

  size_t code_fname_size;
  compress_src(C, src, src_len, code_fname, &code_fname_size);

  freqtable_free(F);
  htree_free(H);
  codetable_free(C);
  free(src);

  printf("Deflated %s (%u bytes) into %s (%u bytes): %d%% compression ratio\n",
         src_fname == NULL ? "STDOUT" : src_fname, (unsigned int)src_len,
         code_fname, (unsigned int)code_fname_size,
         (int)(100 - (100*code_fname_size)/src_len));
}


void uncompress(char *src_fname, char *code_fname) {
  FILE *code_stream = xfopen(code_fname, "r");
  size_t code_fname_size = file_size(code_stream);

  // Read magic number
  uint32_t magic;
  fread(&magic, sizeof(uint32_t), 1, code_stream);
  if (magic != MAGIC) {
    fprintf(stderr, "Bad magic number %d\n", magic);
    exit(1);
  }

  // Starting position of code segment
  uint16_t code_start;
  fread(&code_start, sizeof(uint16_t), 1, code_stream);
  if (v_verbose)
    printf("Code segment starts at byte %u\n", code_start);

  // Number of symbols in use
  uint8_t num_symbols8;
  fread(&num_symbols8, sizeof(uint8_t), 1, code_stream);
  unsigned int num_symbols = num_symbols8 == 0 ? NUM_SYMBOLS : num_symbols8;
  if (num_symbols == 1) {
    printf("%s has a single symbol in its code table: that can't be!\n",
           src_fname);
    exit(1);
  }
  if (v_verbose) {
    printf("%u letters in use, ", num_symbols);
    fflush(stdout);
  }
  // Each symbol in use
  uint8_t *letters_in_use = xcalloc(num_symbols, sizeof(uint8_t));
  //unsigned int l =
  fread(letters_in_use, sizeof(uint8_t), num_symbols, code_stream);
  /*if (v_verbose) {
    printf("read %u of them\n", l);
    for (unsigned short i = 0; i < num_symbols; i++)
      printf("  - Read '%c' (0x%02X)\n", letters_in_use[i], letters_in_use[i]);
  }*/
  // Size of each symbol in use
  uint8_t *code_sizes = xcalloc(num_symbols, sizeof(uint8_t));
  fread(code_sizes, sizeof(uint8_t), num_symbols, code_stream);
  uint16_t overall_code_size = 0;
  for (unsigned short i = 0; i < num_symbols; i++) {
    // if (v_verbose) printf("  # Code of '%c' (0x%02X) is %u bits\n", letters_in_use[i], letters_in_use[i], code_sizes[i]);
    overall_code_size += code_sizes[i];
  }
  // Code of each symbol in use
  uint16_t padded_overall_code_size = code_start - 1 - 2*num_symbols;
  uint8_t *padded_letter_codes = xcalloc(padded_overall_code_size, sizeof(uint8_t));
  fread(padded_letter_codes, sizeof(uint8_t), padded_overall_code_size, code_stream);

  if (c_verbose) {
    printf("==> Calling your unpack ...             ");
    fflush(stdout);
  }
  char *letter_codes = unpack(padded_letter_codes, padded_overall_code_size);
  if (c_verbose) printf("called!\n");
  free(padded_letter_codes);

  codetable_t table = xcalloc(NUM_SYMBOLS, sizeof(bitstring_t));
  unsigned short k = 0;
  for (unsigned short i = 0; i < num_symbols; i++) {
    table[letters_in_use[i]] = xcalloc(code_sizes[i] + 1, sizeof(char));
    strncpy(table[letters_in_use[i]], letter_codes + k, code_sizes[i]);
    k += code_sizes[i];
    if (v_verbose) printf("  * Code of '%c' (0x%02X) is %s (%u bits)\n", letters_in_use[i], letters_in_use[i], table[letters_in_use[i]], code_sizes[i]);
  }
  free(letters_in_use);
  free(code_sizes);
  free(letter_codes);
  if (c_verbose)  {
    printf("Retrieved the following code table:\n");
    print_codetable(table);
  }

  // Code length
  uint32_t code_len;
  fread(&code_len, sizeof(uint32_t), 1, code_stream);
  if (v_verbose) printf("Code length is %u bit\n", code_len);
  // Code
  uint8_t *code = xcalloc(num_padded_bytes(code_len), sizeof(uint8_t));
  fread(code, sizeof(uint8_t), num_padded_bytes(code_len), code_stream);
  fclose(code_stream);

  if (c_verbose) {
    printf("==> Calling your unpack ...             ");
    fflush(stdout);
  }
  bit_t *bits = unpack(code, num_padded_bytes(code_len));
  if (c_verbose) printf("called!\n");
  //  if (v_verbose) printf("Code is %u bits:\n%s\n", (unsigned int)strlen(bits), bits);
  bits[code_len] = '\0';  // drops padding
  free(code);

  htree *H = htree_from_codetable(table);

  size_t src_len;
  if (c_verbose) {
    printf("==> Calling your decode_src ...         ");
    fflush(stdout);
  }
  symbol_t *src = decode_src(H, bits, &src_len);
  if (c_verbose) printf("called!\n");
  codetable_free(table);
  htree_free(H);

  FILE *src_stream = xfopen(src_fname, "w");
  fwrite(src, sizeof(symbol_t), src_len, src_stream);
  if (src_fname != NULL) fclose(src_stream);
  free(src);

  if (c_verbose) {
    printf("\nDecoded %u bits into %u characters (%u bits)",
           (unsigned int)code_len, (unsigned int)src_len, (unsigned int)(8*src_len));
    fflush(stdout);
  }

  free(bits);
  if (src_fname == NULL) printf("\n"); // Add newline if printing to terminal
  printf("Inflated %s (%u bytes) into %s (%u bytes): %d%% compression ratio\n",
         code_fname, (unsigned int)code_fname_size,
         src_fname == NULL ? "STDOUT" : src_fname, (unsigned int)src_len,
         (int)(100 - (100*code_fname_size)/src_len));
}
