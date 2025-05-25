from z3 import *
import capstone.mips_const as mips
from state import Memory, Registers

HEAP_BASE = 0x10000000

# some helper functions
def range_unroll(n, max_unroll=256):
    if isinstance(n, BitVecNumRef):
        return list(range(n.as_long()))
    else:
        return list(range(max_unroll))

# mem allocations
class Libc:
    def malloc(size: BitVec)->BitVec:
        base = HEAP_BASE
        HEAP_BASE += simplify(size).as_long()
        return base

    def calloc():
        pass

    def realloc():
        pass

    # mem free
    def free(regs: Registers, mem: Memory):
        ptr = regs[mips.MIPS_REG_A0]
        mem.pop(simplify(ptr).as_long(), None)
        return regs, mem

    # misc mem instr
    def memcpy(regs: Registers, mem: Memory):
        dst = regs[mips.MIPS_REG_A0]
        src = regs[mips.MIPS_REG_A1]
        n = regs[mips.MIPS_REG_A2]

        new_mem = mem
        for i in range_unroll(n):
            byte = Select(mem, src + i)
            new_mem = Store(new_mem, dst + i, byte)
        
        new_regs = regs.copy()
        new_regs[mips.MIPS_REG_V0] = dst

        return new_regs, new_mem

    def memset(regs: Registers, mem: Memory):
        s = regs[mips.MIPS_REG_A0]
        c = regs[mips.MIPS_REG_A1]
        n = regs[mips.MIPS_REG_A2]

        new_mem = mem
        for i in range_unroll(n):
            new_mem = Store(new_mem, s + i, c)
        
        new_regs = regs.copy()
        new_regs[mips.MIPS_REG_V0] = s1

        return new_regs, new_mem

    def memmove():
        pass

    # str operations
    def strlen(regs: Registers, mem: Memory):
        pass
        """
        s = regs[mips.MIPS_REG_A0]
        
        new_regs = regs.copy()
        new_regs[mips.MIPS_REG_V0] = 
        # 언롤링하고 대충잘하면됨ㅋㅋ
        
        return new_regs, mem
        """

    def strnlen():
        # TODO
        pass

    def strcmp(regs: Registers, mem: Memory):
        # TODO
        pass

    def strncmp():
        # TODO
        pass

    def strchr():
        pass

    def strrchr():
        pass

    def strstr():
        pass

    def strtok():
        pass

    def strcpy():
        # TODO
        pass

    def strncpy():
        # TODO
        pass

    def sprintf():
        pass

    def snprintf():
        pass

    # file
    def open():
        # TODO
        pass

    def close():
        # TODO
        pass

    def read(regs: Registers, mem: Memory):
        # TODO
        pass

    def write():
        # TODO
        pass

    def lseek():
        pass

    def stat():
        pass

    def fopen():
        pass

    def fclose():
        pass

    def fread():
        pass

    def fwrite():
        pass

    def fseek():
        pass

    def ftell():
        pass

    def fflush():
        pass

    def getchar():
        pass

    def putchar():
        pass

    def gets():
        pass

    def fgets():
        pass

    def puts():
        pass

    def printf():
        pass

    def fprintf():
        pass

    def scanf():
        pass

    def sscanf():
        pass

    # process controls
    def exit():
        # TODO
        pass

    def abort():
        pass

    def system():
        pass

    def fork():
        pass

    def execve():
        pass

    def wait():
        pass

    def kill():
        pass

    # time
    def time():
        pass

    def gettimeofday():
        pass

    def clock():
        pass

    # pseudo-random
    def rand():
        # TODO
        pass

    def srand():
        # TODO
        pass

    # sorting / search
    def qsort():
        pass

    def bsearch():
        pass

    # typecasting
    def atoi():
        # TODO
        pass

    def atol():
        # TODO
        pass

    def strtol():
        pass

    def strtod():
        pass

    # math
    def sin():
        pass

    def cos():
        pass

    def tan():
        pass

    def exp():
        pass

    def log():
        pass

    def pow():
        pass

    def sqrt():
        pass

    def ceil():
        pass

    def floor():
        pass


"""
1. 메모리 관리 함수

malloc(size_t size)
calloc(size_t nmemb, size_t size)
realloc(void *ptr, size_t size)
free(void *ptr)

2. 문자열·메모리 조작 함수

복사/설정
memcpy(void *dest, const void *src, size_t n)
memmove(void *dest, const void *src, size_t n)
memset(void *s, int c, size_t n)
길이·검색·비교
strlen(const char *s)
strnlen(const char *s, size_t maxlen)
strcmp(const char *s1, const char *s2)
strncmp(const char *s1, const char *s2, size_t n)
strchr(const char *s, int c)
strrchr(const char *s, int c)
strstr(const char *haystack, const char *needle)
strtok(char *str, const char *delim)
포맷팅·복사
strcpy(char *dest, const char *src)
strncpy(char *dest, const char *src, size_t n)
sprintf(char *str, const char *format, …)
snprintf(char *str, size_t size, const char *format, …)

3. 입출력(I/O) 함수

파일 기반
open(const char *pathname, int flags, mode_t mode)
close(int fd)
read(int fd, void *buf, size_t count)
write(int fd, const void *buf, size_t count)
lseek(int fd, off_t offset, int whence)
stat(const char *path, struct stat *buf)
표준 스트림
fopen(const char *path, const char *mode)
fclose(FILE *stream)
fread(void *ptr, size_t size, size_t nmemb, FILE *stream)
fwrite(const void *ptr, size_t size, size_t nmemb, FILE *stream)
fseek(FILE *stream, long offset, int whence)
ftell(FILE *stream)
fflush(FILE *stream)
문자 단위·문자열 단위
getchar(void)
putchar(int c)
gets(char *s) (취약)
fgets(char *s, int size, FILE *stream)
puts(const char *s)
printf(const char *format, …)
fprintf(FILE *stream, const char *format, …)
scanf(const char *format, …)
sscanf(const char *str, const char *format, …)

4. 프로세스 제어·시스템 호출 래퍼

exit(int status)
abort(void)
system(const char *command)
fork(void)
execve(const char *filename, char *const argv[], char *const envp[])
wait(int *status)
kill(pid_t pid, int sig)

5. 시간·난수·정렬·변환

시간
time(time_t *t)
gettimeofday(struct timeval *tv, struct timezone *tz)
clock(void)
난수
rand(void)
srand(unsigned int seed)
정렬·검색
qsort(void *base, size_t nmemb, size_t size, int (*compar)(const void *, const void *))
bsearch(const void *key, const void *base, size_t nmemb, size_t size, int (*compar)(const void *, const void *))
형 변환
atoi(const char *nptr)
atol(const char *nptr)
strtol(const char *nptr, char **endptr, int base)
strtod(const char *nptr, char **endptr)

6. 수학 함수 (math.h)

sin(double x), cos(double x), tan(double x)
exp(double x), log(double x), pow(double x, double y)
sqrt(double x), ceil(double x), floor(double x)
이 중 symbolic execution이나 후킹 레이어에서 자주 추상화하는 대상은

메모리 할당(malloc/free)
문자열 조작(strlen, memcpy, strcmp)
입출력(read/write, printf)
시스템 제어(execve, system)"""