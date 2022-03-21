/**************************************************************************/
/*              COPYRIGHT Carnegie Mellon University 2021                 */
/* Do not post this file or any derivative on a public site or repository */
/**************************************************************************/
/* Huffman coding
 *
 * 15-122 Principles of Imperative Computation
 */

#include <string.h>
#include <stdint.h>

#include "lib/contracts.h"
#include "lib/xalloc.h"

#include "compress.h"


// Returns ceil(bits_len/8)
unsigned int num_padded_bytes(unsigned int bit_len) {
  return bit_len/8 + (bit_len%8==0 ? 0 : 1);
}


// Pack a NUL-terminated string of ASCII bits into an array of bytes; length = strlen(bits)/8
// uint8_t* pack(bit_t* bits);

// Unpack an array of bytes c of length len into a NUL-terminated string of ASCII bits
// bit_t* unpack(uint8_t *c, size_t len);
