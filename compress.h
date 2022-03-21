/**************************************************************************/
/*              COPYRIGHT Carnegie Mellon University 2021                 */
/* Do not post this file or any derivative on a public site or repository */
/**************************************************************************/
/* Compressing and uncompressing a file given a file
 *
 * 15-122 Principles of Imperative Computation
 */

#include <stdio.h>

#include "encode.h"
#include "bitpacking.h"

#ifndef _COMPRESS_H_
#define _COMPRESS_H_

// Set verbose flag
void verbose_compress();
void very_verbose_compress();

// Magic number for compressed files
#define MAGIC 0xC0DEBEAD

// Compress src to file fname (or STDOUT) using codetable table
//   fname_size is the number of bytes written to fname
void compress_text(codetable_t table, symbol_t *src, size_t src_len,
                   char *fname, size_t *fname_size);

// Compress src_fname (or STDIN) to code_fname (or STDOUT)
void compress(char *src_fname, char *code_fname);

// Uncompress code_fname (or STDIN) into src_fname (or STDOUT)
void uncompress(char *src_fname, char *code_fname);

#endif /* _COMPRESS_H_ */
