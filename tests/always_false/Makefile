CC = mips-linux-gnu-gcc
CFLAGS = -fprofile-arcs -ftest-coverage -g
QEMU = qemu-mips-static
LIBC = /usr/mips-linux-gnu/

test.elf: test.c
	$(CC) $(CFLAGS) -o test.elf test.c

clean:
	$(RM) *.elf *.gcda *.gcno *.gcov

run: test.elf
	$(QEMU) -L $(LIBC) ./test.elf

gcov: run
	gcov -o . *.gcno