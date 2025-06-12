CC = mips-linux-gnu-gcc

CFLAGS = -Wall -Wextra -fprofile-arcs -ftest-coverage -g

md5: md5.c main.c
	@$(CC) $(CFLAGS) -o md5 md5.c main.c

clean:
	@$(RM) md5
