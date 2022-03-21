/**************************************************************************/
/*              COPYRIGHT Carnegie Mellon University 2021                 */
/* Do not post this file or any derivative on a public site or repository */
/**************************************************************************/
/* Useful file I/O wrappers
 *
 * 15-122 Principles of Imperative Computation
 */


#ifndef _FILE_IO_H_
#define _FILE_IO_H_

#include <stdint.h>


#define MAX_STDIN_LEN 1000

// open filename in given mode, exiting program in case of error
FILE* xfopen(char *fname, char *mode);

// returns the number of bytes in a file (or MAX_STDIN)
size_t file_size(FILE *F);


typedef uint8_t byte_t;

// Reads binary file fname reporting number of bytes in *size
byte_t* read_file_to_byte_array(char *fname, size_t *size);

// Reads text file fname reporting number of characters in *size
char* read_file_to_char_array(char *fname, size_t *size);

#endif   /* _FILE_IO_H_ */
