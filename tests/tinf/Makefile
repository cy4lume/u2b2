CC = mips-linux-gnu-gcc
CFLAGS = -fprofile-arcs -ftest-coverage -g
QEMU = qemu-mips-static
LIBC = /usr/mips-linux-gnu/

test.elf: adler32.c crc32.c tinfgzip.c tinflate.c tinfzlib.c test.c
	$(CC) $(CFLAGS) -o test.elf adler32.c crc32.c tinfgzip.c tinflate.c tinfzlib.c test.c

clean:
	$(RM) *.elf *.gcda *.gcno *.gcov

run: test.elf
	$(QEMU) -L $(LIBC) ./test.elf

gcov: run
	gcov -o . *.gcno