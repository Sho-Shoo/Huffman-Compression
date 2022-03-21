/**************************************************************************/
/*              COPYRIGHT Carnegie Mellon University 2021                 */
/* Do not post this file or any derivative on a public site or repository */
/**************************************************************************/
/* Huffman coding
 *
 * Main file
 * 15-122 Principles of Imperative Computation
 */

#include <stdlib.h>
#include <stdbool.h>
#include <stdio.h>
#include <string.h>
#include <assert.h>
#include <getopt.h>
#include <ctype.h>

#include "freqtable.h"
#include "htree.h"
#include "encode.h"
#include "compress.h"

#define NOP 0
#define ENCODE 1
#define DECODE 2
#define COMPRESS 3
#define UNCOMPRESS 4
#define WRITE_FREQ 5


void usage(char *prog_name, char option) {
  if (   option == 's'
      || option == 'h'
      || option == 'a'
      || option == 'f'
      || option == 'r')
    fprintf(stderr, "Option -%c requires an argument.\n", option);
  else if (isprint(option) || option == 0) {
    if (option != 0) fprintf(stderr, "Unknown option `-%c'.\n", option);
    fprintf(stderr, "Usage:\n\t %s <args>\n\n", prog_name);
    fprintf(stderr, "Valid arguments:\n");
    fprintf(stderr, "\t-s <s-file> __or__ --source <s-file>\n");
    fprintf(stderr, "\t   use <s-file> for uncompressed file\n\n");

    fprintf(stderr, "\t-h <h-file> __or__ --code <h-file>\n");
    fprintf(stderr, "\t   use <h-file> for compressed binary file\n\n");

    fprintf(stderr, "\t-a <a-file> __or__ --binascii <a-file>\n");
    fprintf(stderr, "\t   use <a-file> for compressed binASCII file\n\n");

    fprintf(stderr, "\t-f <f-file> __or__ --freq <f-file>\n");
    fprintf(stderr, "\t   use <f-file> for frequency table file\n\n");

    fprintf(stderr, "\t-r <r-file> __or__ --htree <r-file>\n");
    fprintf(stderr, "\t   use <r-file> for Huffman tree file\n\n");

    fprintf(stderr, "\t-E __or__ --encode\n");
    fprintf(stderr, "\t   encode <s-file> (or STDIN) into <a-file> (or STDOUT)\n");
    fprintf(stderr, "\t   using letter frequencies in <s-file> unless <f-file> is provided\n\n");

    fprintf(stderr, "\t-D __or__ --decode\n");
    fprintf(stderr, "\t   decode <a-file> (or STDIN) into <s-file> (or STDOUT)\n");
    fprintf(stderr, "\t   using letter frequencies in <f-file>\n\n");

    fprintf(stderr, "\t-C __or__ --compress\n");
    fprintf(stderr, "\t   compress <s-file> (or STDIN) into <h-file> (or STDOUT)\n\n");

    fprintf(stderr, "\t-U __or__ uncompress\n");
    fprintf(stderr, "\t   uncompress <h-file> (or STDIN) into <s-file> (or STDOUT)\n\n");

    fprintf(stderr, "\t-F  __or__ --write-freq\n");
    fprintf(stderr, "\t   write frequency table of <s-file> to <f-file> (or STDOUT)\n\n");

    fprintf(stderr, "\t-Q __or__ --print-freq\n");
    fprintf(stderr, "\t   print frequency table\n\n");

    fprintf(stderr, "\t-R __or__ --print-htree\n");
    fprintf(stderr, "\t   print Huffman tree\n\n");

    fprintf(stderr, "\t-T __or__ --print-codes\n");
    fprintf(stderr, "\t   print code table\n\n");

    fprintf(stderr, "\t-V __or__ --verbose\n");
    fprintf(stderr, "\t   set verbose mode\n\n");

    fprintf(stderr, "\t-H __or__ --help\n");
    fprintf(stderr, "\t   display usage instructions\n\n");
  } else
    fprintf(stderr, "Unknown option character `\\x%x'.\n", option);
  exit(1);
}

htree* build_htree_verbose(freqtable_t table, bool verbose) {
  if (verbose) {
    printf("==> Calling your build_htree ...        ");
    fflush(stdout);
  }
  htree *H = build_htree(table);
  if (verbose) printf("called!\n");
  return H;
}

freqtable_t build_freqtable_verbose(char *fname, bool verbose) {
  if (verbose) {
    printf("==> Calling your build_freqtable ...    ");
    fflush(stdout);
  }
  freqtable_t F = build_freqtable(fname);
  if (verbose) printf("called!\n");
  return F;
}

codetable_t htree_to_codetable_verbose(htree *H, bool verbose) {
  if (verbose) {
    printf("==> Calling your htree_to_codetable ... ");
    fflush(stdout);
  }
  codetable_t C = htree_to_codetable(H);
  if (verbose) printf("called!\n");
  return C;
}

int main (int argc, char **argv) {
  // Process arguments
  char *source_fname     = NULL;
  char *compressed_fname = NULL;
  char *binascii_fname   = NULL;
  char *frequency_fname  = NULL;
  char *codetable_fname  = NULL;
  int op_flag = NOP;
  bool print_freqtable_flag = false;
  bool print_htree_flag     = false;
  bool print_codetable_flag = false;
  bool verbose = false;


  if (argc == 1) usage(argv[0], 0);

  int c;
  while (1) {
      static struct option long_options[] =
        {
          // Options with arguments
          {"source",          required_argument, 0, 's'},
          {"code",            required_argument, 0, 'h'},
          {"binascii",        required_argument, 0, 'a'},
          {"freq",            required_argument, 0, 'f'},
          {"htree",           required_argument, 0, 'r'},
          // Operations
          {"encode",          no_argument,       0, 'E'},
          {"decode",          no_argument,       0, 'D'},
          {"compress",        no_argument,       0, 'C'},
          {"uncompress",      no_argument,       0, 'U'},
          {"write-freq",      no_argument,       0, 'F'},
          // Flags
          {"print-freq",      no_argument,       0, 'Q'},
          {"print-htree",     no_argument,       0, 'R'},
          {"print-codes",     no_argument,       0, 'T'},
          {"verbose",         no_argument,       0, 'V'},
          {"help",            no_argument,       0, 'H'},
          // End of options
          {0, 0, 0, 0}
        };
      // getopt_long stores the option index here.
      int option_index = 0;

      c = getopt_long (argc, argv, "EDCUFQRTVWHs:h:a:f:r:",
                       long_options, &option_index);

      if (c == -1) break; // end of the options

      switch (c) {
      case 's': source_fname     = optarg;    break;
      case 'h': compressed_fname = optarg;    break;
      case 'a': binascii_fname   = optarg;    break;
      case 'f': frequency_fname  = optarg;    break;
      case 'r': codetable_fname  = optarg;    break;

      case 'E': op_flag = ENCODE;             break;
      case 'D': op_flag = DECODE;             break;
      case 'C': op_flag = COMPRESS;           break;
      case 'U': op_flag = UNCOMPRESS;         break;
      case 'F': op_flag = WRITE_FREQ;         break;

      case 'Q': print_freqtable_flag = true;  break;
      case 'R': print_htree_flag     = true;  break;
      case 'T': print_codetable_flag = true;  break;
      case 'V':
        verbose = true;
        verbose_huffman();
        verbose_compress();
        break;
      case 'W': very_verbose_compress();      break;

      case 'H':
      case '?': usage(argv[0], optopt);       abort();
                // fallthrough causes warning in gcc7

      default: abort ();
      }
  }

  freqtable_t F = NULL;
  htree *H      = NULL;
  codetable_t C = NULL;

  switch (op_flag) {
  case NOP:
    if (frequency_fname != NULL) {
      F = read_freqtable(frequency_fname);
      if (print_freqtable_flag) print_freqtable(F);
      H = build_htree_verbose(F, verbose);
      if (print_htree_flag)     print_htree(H);
      C = htree_to_codetable_verbose(H, verbose);
      if (print_codetable_flag) print_codetable(C);
      if (codetable_fname != NULL) write_codetable(C, codetable_fname);
    } else if (source_fname != NULL) {
      F = build_freqtable_verbose(source_fname, verbose);
      if (print_freqtable_flag) print_freqtable(F);
      H = build_htree_verbose(F, verbose);
      if (print_htree_flag)     print_htree(H);
      C = htree_to_codetable_verbose(H, verbose);
      if (verbose) printf("called!\n");
      if (print_codetable_flag) print_codetable(C);
      if (codetable_fname != NULL) write_codetable(C, codetable_fname);
    } else {
      if (print_freqtable_flag) printf("No frequency table to show\n");
      if (print_htree_flag)     printf("No Huffman tree to show\n");
      if (print_codetable_flag) printf("No code table to show\n");
    }
    break;

  case ENCODE:
    if (codetable_fname == NULL) {  // No code table given
      if (frequency_fname != NULL)  // Read frequency table file if there is one
        F = read_freqtable(frequency_fname);
      else                          // otherwise, get frequencies from source file
        F = build_freqtable_verbose(source_fname, verbose);
      if (print_freqtable_flag) print_freqtable(F);
      H = build_htree_verbose(F, verbose);
      if (print_htree_flag)     print_htree(H);
      C = htree_to_codetable_verbose(H, verbose);
    } else                         // Use code table instead if given
      C = read_codetable(codetable_fname);
    if (print_codetable_flag) print_codetable(C);
    encode(C, source_fname, binascii_fname);
    break;

  case DECODE:
    if (codetable_fname != NULL) {
      C = read_codetable(codetable_fname);
      if (print_codetable_flag) print_codetable(C);
      H = htree_from_codetable(C);
      if (print_htree_flag)     print_htree(H);
      if (print_freqtable_flag)
        printf("Need a frequency file to display frequency table\n");
    } else if (frequency_fname != NULL) {
      F = read_freqtable(frequency_fname);
      if (print_freqtable_flag) print_freqtable(F);
      H = build_htree_verbose(F, verbose);
      if (print_htree_flag)     print_htree(H);
      if (print_codetable_flag) {
        C = htree_to_codetable_verbose(H, verbose);
        print_codetable(C);
      }
    } else {
      printf("Need a htree or frequency file to decode source\n");
      exit(1);
    }
    decode(H, binascii_fname, source_fname, C);
    break;

  case COMPRESS:
    if (print_freqtable_flag) {
      F = build_freqtable_verbose(source_fname, verbose);
      print_freqtable(F);
    }
    if (print_codetable_flag) {
      //if (F != NULL) build_freqtable_verbose(source_fname, verbose);
      if (F == NULL) F = build_freqtable_verbose(source_fname, verbose);
      H = build_htree_verbose(F, verbose);
      C = htree_to_codetable_verbose(H, verbose);
      print_codetable(C);
    }
    compress(source_fname, compressed_fname);
    break;

  case UNCOMPRESS:
    if (print_codetable_flag)
      printf("Use -V flag to display the code table\n");
    if (print_freqtable_flag)
      printf("The frequency table is not available while uncompressing\n");
    uncompress(source_fname, compressed_fname);
    break;

  case WRITE_FREQ:
    F = build_freqtable_verbose(source_fname, verbose);
    write_freqtable(F, frequency_fname);
    if (print_freqtable_flag) print_freqtable(F);
    if (print_codetable_flag) {
      H = build_htree_verbose(F, verbose);
      C = htree_to_codetable_verbose(H, verbose);
      print_codetable(C);
    }
    break;

  default:
    printf("Unknow operation %d\n", op_flag);
  }

  if (F != NULL) freqtable_free(F);
  if (H != NULL) htree_free(H);
  if (C != NULL) codetable_free(C);
  return 0;
}
