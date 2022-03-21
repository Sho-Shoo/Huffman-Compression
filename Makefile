CC=gcc
CFLAGS=-Wall -Wextra -Werror -Wshadow -std=c99 -pedantic -g
LIB=lib/*.c
GIVEN1=freqtable.c htree.c encode.c bitpacking.c compress.c main.c
GIVEN2=freqtable.c htree.c bitpacking.c test-htree.c
GIVEN3=bitpacking.c test-pack.c

safe:
	$(CC) $(CFLAGS) -DDEBUG $(LIB) $(GIVEN1) huffman.c \
	    -o huff-safe

fast:
	$(CC) $(CFLAGS) $(LIB) $(GIVEN1) huffman.c \
	     -o huff-fast

htree:
	$(CC) $(CFLAGS) -DDEBUG $(LIB) $(GIVEN2) huffman.c \
	     -o test-htree

pack:
	$(CC) $(CFLAGS) -DDEBUG $(LIB) $(GIVEN3) huffman.c \
	     -o test-pack
