/**************************************************************************/
/*              COPYRIGHT Carnegie Mellon University 2021                 */
/* Do not post this file or any derivative on a public site or repository */
/**************************************************************************/
/* Manipulating frequency tables
 *
 * 15-122 Principles of Imperative Computation
 */

#include <stdbool.h>

#ifndef _FREQTABLE_H_
#define _FREQTABLE_H_

// Number of symbols in uncompressed files
#define NUM_SYMBOLS 256

typedef unsigned char symbol_t;     // Type of symbols
typedef unsigned int *freqtable_t;  // Type of frequency tables


// Check that frequency table is valid
bool is_freqtable(freqtable_t table);

// Build a frequency table from a source file
freqtable_t build_freqtable(char *fname);

// Read frequency table from frequency file
freqtable_t read_freqtable(char *fname);

// Write a frequency table to file
void write_freqtable(freqtable_t table, char *fname);

// Print a frequency table
void print_freqtable(freqtable_t table);

// Dispose of frequency table after we're done
void freqtable_free(freqtable_t table);

#endif /* _FREQTABLE_H_ */
