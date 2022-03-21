/**************************************************************************/
/*              COPYRIGHT Carnegie Mellon University 2021                 */
/* Do not post this file or any derivative on a public site or repository */
/**************************************************************************/
/* Manipulating frequency tables
 *
 * 15-122 Principles of Imperative Computation
 */

#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <assert.h>
#include <stdbool.h>
#include <ctype.h>

#include "lib/contracts.h"
#include "lib/xalloc.h"
#include "lib/file_io.h"

#include "freqtable.h"


// Check that frequency table is valid
bool is_freqtable(freqtable_t table)
//@requires \length(table) == NUM_SYMBOLS;
{
  return table != NULL;
}


// Build a frequency table from a source file (or STDIN)
// freqtable_t build_freqtable(char *fname);


// Read frequency table from frequency file (or STDIN)
freqtable_t read_freqtable(char *fname) {
  unsigned int max_line_length = 20;  // Longest expected line
  char *line = xcalloc(max_line_length, sizeof(char));
  freqtable_t table = xcalloc(NUM_SYMBOLS, sizeof(unsigned int));

  FILE *stream = xfopen(fname, "r");
  while (fgets(line, max_line_length, stream) != NULL) {
    char c;     // printable characters
    int i;      // non-printable characters
    unsigned int f; // associated frequency
    if (sscanf(line, "%1c:%u\n", &c, &f) == 2)
      table[(symbol_t)c] = f;
    else if (sscanf(line, "%i:%u\n", &i, &f) == 2)
      table[(symbol_t)i] = f;
    else if (sscanf(line, "\n") == 0) {}  // Skip empty lines
    else {
      fprintf(stderr, "Could not parse line %s\n", line);
      exit(1);
    }
  }
  if (fname != NULL) fclose(stream);
  free(line);

  ENSURES(is_freqtable(table));
  return table;
}


// Write a frequency table to file (or STDOUT)
void write_freqtable(freqtable_t table, char *fname) {
  REQUIRES(is_freqtable(table));

  FILE *stream = xfopen(fname, "w");
  for (unsigned short c = 0; c < NUM_SYMBOLS; c++) {
    unsigned int f = table[(symbol_t)c];
    if (f != 0) {
      if (isprint(c)) fprintf(stream, "%c:%u\n", c, f);
      else            fprintf(stream, "0x%02X:%u\n", c, f);
    }
  }
  if (fname != NULL) fclose(stream);
}


// Print a frequency table
void print_freqtable(freqtable_t table) {
  REQUIRES(is_freqtable(table));
  printf("Frequency table:\n");
  for (unsigned short c = 0; c < NUM_SYMBOLS; c++) {
    unsigned int f = table[(symbol_t)c];
    if (f != 0) {
      if (isprint(c)) printf("  '%c' occurs %3u times\n", c, f);
      else            printf("  \\%02X occurs %3u times\n", c, f);
    }
  }
  printf("\n");
}


// Dispose of frequency table after we're done
void freqtable_free(freqtable_t table) {
  free(table);
}
