/**************************************************************************/
/*              COPYRIGHT Carnegie Mellon University 2021                 */
/* Do not post this file or any derivative on a public site or repository */
/**************************************************************************/
/* Useful file I/O wrappers
 *
 * 15-122 Principles of Imperative Computation
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "file_io.h"
#include "xalloc.h"


// open filename in given mode, exiting program in case of error
FILE* xfopen (char *fname, char *mode) {
  FILE* stream;
  if (fname != NULL)               stream = fopen(fname, mode);
  else if (strcmp(mode, "w") == 0) stream = stdout;
  else                             stream = stdin;

  if (stream == NULL) {
    perror(fname);
    exit(1);
  }
  return stream;
}


// returns the number of bytes in a file (or MAX_STDIN)
size_t file_size(FILE *F) {
  if (F == stdin) return MAX_STDIN_LEN;

  fseek(F, 0L, SEEK_END);
  unsigned size = ftell(F);
  rewind(F);
  return size;
}


byte_t* read_file_to_byte_array(char *fname, size_t *size) {
  FILE *stream = xfopen(fname, "r");
  *size = file_size(stream);
  byte_t* bytes = xcalloc(*size, sizeof(byte_t));
  fread(bytes, sizeof(byte_t), *size, stream);
  if (fname != NULL) fclose(stream);
  return bytes;
}

char* read_file_to_char_array(char *fname, size_t *size) {
  FILE *stream = xfopen(fname, "r");
  *size = file_size(stream);
  char* chars = xcalloc(*size + 1, sizeof(char));

  unsigned n = 0;
  int c;
  while ((c = fgetc(stream)) != EOF) {
    chars[n] = c;
    n++;
  }
  chars[n] = '\0';
  if (fname != NULL) fclose(stream);

  strtok(chars, "\n");  // remove trailing new lines
  return chars;
}
