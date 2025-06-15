from z3 import *
import capstone.mips_const as mips
from state import Memory, Registers
import syscall
import time as py_time

HEAP_BASE = 0x10000000

PTR_WIDTH = 0x20
PTRDIFF_MAX = 0x7FFFFFFF

free_list = []
alloc_sizes = {}
# some helper functions

# typecasting
def to_uint32(x):
    if isinstance(x, int):
        return x & 0xFFFFFFFF
    elif isinstance(x, (BitVecNumRef, BitVecRef)):
        w = x.size()
        if w == 32:
            return ZeroExt(32-w, x)
        else:
            return Extract(31, 0, x)
    
    raise TypeError(f"Type not supported {type(x)}")

# symbol unrolling
def range_unroll(n, max_unroll=256):
    if isinstance(n, int):
        return list(range(n))
    elif isinstance(n, BitVecNumRef):
        return list(range(n.as_long()))
    else:
        return list(range(max_unroll))

def get_byte_from_address(mem: Memory, addr: z3.BitVecRef) -> z3.BitVecRef:
    if addr.size() != 32:
        raise ValueError("_get_byte_from_address expects a 32-bit address BitVec.")
    w_addr = addr & ~z3.BitVecVal(3, 32)
    b_off = addr & z3.BitVecVal(3, 32)
    w_val = mem.load(w_addr)
    b0 = z3.Extract(31, 24, w_val)
    b1 = z3.Extract(23, 16, w_val)
    b2 = z3.Extract(15, 8, w_val)
    b3 = z3.Extract(7, 0, w_val)
    sel_byte = z3.simplify(
        z3.If(b_off == z3.BitVecVal(0, 32), b0,
        z3.If(b_off == z3.BitVecVal(1, 32), b1,
        z3.If(b_off == z3.BitVecVal(2, 32), b2, b3))))
    return sel_byte

class Libc:
    _libc_rand_seed = 1
    _libc_rand_call_count = 0
# mem allocations
    @staticmethod
    def malloc(regs: Registers, mem: Memory, tp: str):
        global HEAP_BASE, PTR_WIDTH, PTRDIFF_MAX, alloc_sizes
        size = regs[mips.MIPS_REG_A0]
        base = HEAP_BASE

        if isinstance(size, BitVecNumRef):
            size = simplify(size).as_long()

            
        size = to_uint32(size)

        if size > PTRDIFF_MAX:
            regs[mips.MIPS_REG_V0] = 0
            return regs, mem, (BitVecVal(0, PTR_WIDTH) == BitVec("malloc_null", PTR_WIDTH))

        HEAP_BASE += size

        if tp == "run":
            alloc_sizes[base] = size
            sym_slot = BitVec("mem_%x" % base, PTR_WIDTH)

            regs[mips.MIPS_REG_V0] = sym_slot
            mem.store(base, sym_slot)

            return regs, mem
        elif tp == "trace":
            alloc_sizes[base] = size
            regs[mips.MIPS_REG_V0] = base
            mem.store(base, 0)

            return regs, mem
    
        else:
            raise TypeError(f"execution type {type(tp)} not supported")

    @staticmethod
    def calloc(regs: Registers, mem: Memory, tp: str):
        global HEAP_BASE, PTRDIFF_MAX, alloc_sizes
        nmemb = regs[mips.MIPS_REG_A0]
        size = regs[mips.MIPS_REG_A1]

        base = HEAP_BASE

        if isinstance(size, BitVecNumRef):
            size = size.as_long()
        
        if isinstance(nmemb, BitVecNumRef):
            nmemb = nmemb.as_long()
        
        size = to_uint32(size)
        nmemb = to_uint32(nmemb)

        space = size * nmemb
        HEAP_BASE += space
        
        if space > PTRDIFF_MAX:
            regs[mips.MIPS_REG_V0] = 0
            return regs, mem

        for i in range(nmemb * size):
            mem.store(base + i, 0) # init
        
        alloc_sizes[base] = space
        regs[mips.MIPS_REG_V0] = base

        return regs, mem

    @staticmethod
    def realloc():
        pass

    # mem free
    @staticmethod
    def free(regs: Registers, mem: Memory, tp: str):
        global alloc_sizes, free_list

        ptr = regs[mips.MIPS_REG_A0]

        if isinstance(ptr, BitVecNumRef):
            ptr = ptr.as_long()
        
        if ptr in free_list:
            raise RuntimeError("Double free occurred")

        if isinstance(ptr, int):
            size = alloc_sizes.pop(ptr, None)

            if size is None:
                raise("Double free occurred")
            else:
                free_list.append(ptr)
            
        return regs, mem

    # misc mem instr
    @staticmethod
    def memcpy(regs: Registers, mem: Memory, tp: str):
        # need to impl lhu, sh to test this.
        dst = regs[mips.MIPS_REG_A0]
        src = regs[mips.MIPS_REG_A1]
        n = regs[mips.MIPS_REG_A2]

        if isinstance(n, BitVecNumRef):
            n = n.as_long()
        elif not isinstance(n, int):
            raise TypeError(f"type {type(n)} not supported for memcpy size")
        
        for i in range(n):
            byte = mem.load(src + i)
            mem.store(dst + i, byte)
        
        regs[mips.MIPS_REG_V0] = dst

        return regs, mem

    @staticmethod
    def memset(regs: Registers, mem: Memory, tp:str):
        s = regs[mips.MIPS_REG_A0]
        c = regs[mips.MIPS_REG_A1]
        n = regs[mips.MIPS_REG_A2]


        if isinstance(n, int):
            pass
        elif isinstance(n, BitVecNumRef):
            n = n.as_long()
        else:
            raise TypeError(f"type {type(n)} not supported for memset size")
        
        if isinstance(c, int):
            c = c & 0xFF
        elif isinstance(c, BitVecNumRef):
            c = simplify(c & 0xFF)
        else:
            raise TypeError(f"type {type(n)} not supported for memset char")

        for i in range(n):
            #mem.store(s + i, c)
            pass

        regs[mips.MIPS_REG_V0] = s

        return regs, mem

    @staticmethod
    def memmove():
        pass

    # str operations

    @staticmethod
    def strlen(regs: Registers, mem: Memory, tp: str):
        pass

    @staticmethod
    def strnlen():
        # TODO
        pass

    @staticmethod
    def strcmp(regs: Registers, mem: Memory, tp: str):
        # TODO
        pass

    @staticmethod
    def strncmp(regs: Registers, mem: Memory, tp: str):
        str1 = regs[mips.MIPS_REG_A0]
        str2 = regs[mips.MIPS_REG_A1]

        n = regs[mips.MIPS_REG_A2]
        if isinstance(n, int):
            pass
        elif isinstance(n, z3.BitVecNumRef):
            n = n.as_long()
        else:
            raise ValueError(f"strncmp n={n} not yet supported")
        
        conds = []
        for i in range(n // 4):
            c1 = mem.load(str1 + 4 * i)
            c2 = mem.load(str2 + 4 * i)
            conds.append(z3.If(c1 < c2, -1, z3.If(c1 > c2, 1, 0)))

        if n % 4 != 0:
            c1 = mem.load(str1 + (n - (n % 4)))
            c2 = mem.load(str2 + (n - (n % 4)))

            c1 = z3.Extract(31, 32 - 8 * (n % 4), c1)
            c2 = z3.Extract(31, 32 - 8 * (n % 4), c2)
            conds.append(z3.If(c1 < c2, -1, z3.If(c1 > c2, 1, 0)))

        acc = 0
        for cond in reversed(conds):
            acc = z3.simplify(z3.If(cond != 0, cond, acc))

        regs[mips.MIPS_REG_V0] = acc

        return regs, mem

    @staticmethod
    def strchr():
        pass

    @staticmethod
    def strrchr():
        pass

    @staticmethod
    def strstr():
        pass

    @staticmethod
    def strtok():
        pass

    @staticmethod
    def strcpy(regs: Registers, mem: Memory, tp: str):
        dst = regs[mips.MIPS_REG_A0]
        src = regs[mips.MIPS_REG_A1]
        pass

    @staticmethod
    def strncpy():
        # TODO
        pass

    @staticmethod
    def sprintf():
        pass

    @staticmethod
    def snprintf():
        pass

    # file
    @staticmethod
    def open():
        # TODO
        pass

    @staticmethod
    def close():
        # TODO
        pass

    @staticmethod
    def read(regs: Registers, mem: Memory, tp: str):
        # TODO
        pass

    @staticmethod
    def write():
        # TODO
        pass

    @staticmethod
    def lseek():
        pass

    @staticmethod
    def stat():
        pass

    @staticmethod
    def fopen():
        pass

    @staticmethod
    def fclose():
        pass

    @staticmethod
    def fread():
        pass

    @staticmethod
    def fwrite():
        pass

    @staticmethod
    def fseek():
        pass

    @staticmethod
    def ftell():
        pass

    @staticmethod
    def fflush():
        pass

    @staticmethod
    def getchar():
        pass

    @staticmethod
    def putchar():
        pass

    @staticmethod
    def gets():
        pass

    @staticmethod
    def fgets():
        pass

    @staticmethod
    def puts(regs: Registers, mem: Memory, type: str):
        s = b""
        index = regs[mips.MIPS_REG_A0]
        while True:
            data = mem.load(index)
            if isinstance(data, z3.BitVecNumRef):
                data = data.as_long()
            elif isinstance(data, int):
                pass
            else:
                s += f"[[ z3: {data} ]]".encode()
                break

            data = int.to_bytes(data, 4, "big")
            if b"\x00" in data:
                s += data.split(b"\x00")[0]
                break
            else:
                s += data

            index += 4
        print("Stdout:", s.decode() + "\n")
        regs[mips.MIPS_REG_V0] = len(s) + 1
        return regs, mem

    @staticmethod
    def printf(regs: Registers, mem: Memory, tp: str):
        FORMAT_STR_MAX_LEN = 256
        MAX_S_LEN = 128

        fmt_ptr = regs[mips.MIPS_REG_A0]
        
        arg_regs = [mips.MIPS_REG_A1, mips.MIPS_REG_A2, mips.MIPS_REG_A3]
        current_arg_idx = 0
        stack_arg_offset = 0

        output_parts = []
        char_count = z3.BitVecVal(0, 32)
        fmt_concrete_str = ""
        can_proceed = True
        concrete_fmt_addr = None

        if isinstance(fmt_ptr, z3.BitVecNumRef):
            concrete_fmt_addr = fmt_ptr.as_long()
        elif isinstance(fmt_ptr, int):
            concrete_fmt_addr = fmt_ptr
        else: # Symbolic fmt_ptr
            if tp == "run":
                regs[mips.MIPS_REG_V0] = -1
                return regs, mem
            regs[mips.MIPS_REG_V0] = -1
            return regs, mem

        if concrete_fmt_addr == 0:
            regs[mips.MIPS_REG_V0] = -1
            return regs, mem

        try:
            for i in range(FORMAT_STR_MAX_LEN):
                current_char_address_bv = z3.BitVecVal(concrete_fmt_addr + i, 32)
                char_code_bv = get_byte_from_address(mem, current_char_address_bv) 
                
                if isinstance(char_code_bv, z3.BitVecNumRef):
                    c_val = char_code_bv.as_long()
                    if c_val == 0:
                        break
                    fmt_concrete_str += chr(c_val)
                else:
                    can_proceed = False
                    break

            if i == FORMAT_STR_MAX_LEN -1:
                if not isinstance(char_code_bv, z3.BitVecNumRef) or char_code_bv.as_long() != 0:
                    can_proceed = False
        except Exception as e:
            print(f"Error reading format string: {e}")
            regs[mips.MIPS_REG_V0] = -1
            return regs, mem

        if not can_proceed and not fmt_concrete_str:
            regs[mips.MIPS_REG_V0] = -1
            return regs, mem

        fmt_idx = 0
        def get_arg():
            nonlocal current_arg_idx, stack_arg_offset
            if current_arg_idx < len(arg_regs):
                arg_val = regs[arg_regs[current_arg_idx]]
                current_arg_idx += 1
                return arg_val
            else:
                arg_addr = regs[mips.MIPS_REG_SP] + stack_arg_offset
                stack_arg_offset += 4
                return mem.load(arg_addr)

        while fmt_idx < len(fmt_concrete_str):
            char = fmt_concrete_str[fmt_idx]
            if char == '%':
                fmt_idx += 1
                if fmt_idx >= len(fmt_concrete_str):
                    output_parts.append('%')
                    char_count = char_count + 1
                    break
                
                specifier = fmt_concrete_str[fmt_idx]

                if specifier == '%':
                    output_parts.append('%')
                    char_count = char_count + 1
                elif specifier in ('d', 'i', 'u', 'x', 'X', 'o', 'p', 'c'):
                    try:
                        arg = get_arg()
                    except IndexError:
                        can_proceed = False; break 

                    if isinstance(arg, z3.BitVecNumRef):
                        val = arg.as_long()
                        s = ""
                        if specifier == 'd' or specifier == 'i': s = str(val) 
                        elif specifier == 'u': s = str(val & 0xFFFFFFFF) 
                        elif specifier == 'x': s = hex(val & 0xFFFFFFFF)[2:]
                        elif specifier == 'X': s = hex(val & 0xFFFFFFFF)[2:].upper()
                        elif specifier == 'o': s = oct(val & 0xFFFFFFFF)[2:]
                        elif specifier == 'p': s = hex(val & 0xFFFFFFFF) if val != 0 else "(nil)"
                        elif specifier == 'c': s = chr(val & 0xFF)
                        output_parts.append(s)
                        char_count = char_count + len(s)
                    else:
                        estimated_len = 0
                        if specifier == 'c': estimated_len = 1
                        elif specifier == 'p': estimated_len = 10
                        else: estimated_len = 10
                        char_count = char_count + estimated_len
                elif specifier == 's':
                    try:
                        str_ptr = get_arg()
                    except IndexError:
                        can_proceed = False; break

                    concrete_str_ptr_addr = None
                    is_definitely_null_str = False

                    if isinstance(str_ptr, z3.BitVecNumRef):
                        concrete_str_ptr_addr = str_ptr.as_long()
                        if concrete_str_ptr_addr == 0: is_definitely_null_str = True
                    elif isinstance(str_ptr, int):
                        concrete_str_ptr_addr = str_ptr
                        if concrete_str_ptr_addr == 0: is_definitely_null_str = True

                    if is_definitely_null_str:
                        output_parts.append("(null)")
                        char_count = char_count + 6
                    elif concrete_str_ptr_addr is not None:
                        s_chars_list = []
                        s_len_val = 0
                        try:
                            for k_s in range(MAX_S_LEN):
                                s_char_bv = Libc.get_byte_from_address(mem, concrete_str_ptr_addr + k_s)
                                if isinstance(s_char_bv, z3.BitVecNumRef):
                                    s_c_val = s_char_bv.as_long()
                                    if s_c_val == 0: break
                                    s_chars_list.append(chr(s_c_val))
                                    s_len_val += 1
                                else:
                                    break 
                        except Exception:
                            s_len_val = 0
                            can_proceed = False; break
                        
                        output_parts.append("".join(s_chars_list))
                        char_count = char_count + s_len_val
                    else:
                        char_count = char_count + 0
                else:
                    output_parts.append('%')
                    char_count = char_count + 1
                    if fmt_idx < len(fmt_concrete_str):
                        output_parts.append(specifier)
                        char_count = char_count + 1
            else:
                output_parts.append(char)
                char_count = char_count + 1
            fmt_idx += 1
            if not can_proceed: break

        if not can_proceed and not output_parts:
             if isinstance(regs[mips.MIPS_REG_V0], z3.BitVecRef) and regs[mips.MIPS_REG_V0].as_long() != -1 :
                regs[mips.MIPS_REG_V0] = -1
        else:
            final_print_str = "".join(output_parts)
            if tp == "run" or tp == "trace":
                if final_print_str:
                    print("printf: ",final_print_str)
            regs[mips.MIPS_REG_V0] = z3.simplify(char_count)
        return regs, mem

    @staticmethod
    def fprintf():
        pass

    @staticmethod
    def scanf():
        pass

    @staticmethod
    def sscanf():
        pass

    # process controls
    @staticmethod
    def exit(regs: Registers, mem: Memory, tp: str):
        syscall.handle_sys_exit(regs, mem)
        return regs, mem

    @staticmethod
    def abort():
        pass

    @staticmethod
    def system(regs: Registers, mem: Memory, tp: str):
        command = regs[mips.MIPS_REG_A0]
        if isinstance(command, (z3.BitVecNumRef, int)) and (command if isinstance(command, int) else command.as_long()) == 0:
            regs[mips.MIPS_REG_V0] = 1
        else:
            regs[mips.MIPS_REG_V0] = 0
        return regs, mem

    @staticmethod
    def fork(regs: Registers, mem: Memory, tp: str):
        regs[mips.MIPS_REG_V0] = 0
        return regs, mem

    @staticmethod
    def execve():
        pass

    @staticmethod
    def wait():
        pass

    @staticmethod
    def kill():
        pass

    # time
    @staticmethod
    def time(regs: Registers, mem: Memory, tp: str):
        sym_time = z3.BitVec(f"time_{int(py_time.time())}", 32)
        
        tloc_ptr = regs[mips.MIPS_REG_A0]
        is_not_null = True

        if isinstance(tloc_ptr, (z3.BitVecNumRef, int)) and (tloc_ptr if isinstance(tloc_ptr, int) else tloc_ptr.as_long()) == 0:
            is_not_null = False
        if tp == "run" :
            if is_not_null:
                mem.store(tloc_ptr, sym_time)
        elif tp == "trace" and is_not_null:
            mem.store(tloc_ptr, int(py_time.time()))
        regs[mips.MIPS_REG_V0] = sym_time if tp == "run" else int(py_time.time())
        return regs, mem

    @staticmethod
    def gettimeofday(regs: Registers, mem: Memory, tp: str):
        tv_ptr = regs[mips.MIPS_REG_A0]
        if isinstance(tv_ptr, (z3.BitVecNumRef, int)) and (tv_ptr if isinstance(tv_ptr, int) else tv_ptr.as_long()) == 0:
            regs[mips.MIPS_REG_V0] = -1 # FAULT
            return regs, mem

        if tp == "run":
            sym_tv_sec = z3.BitVec(f"tv_sec_{int(py_time.time())}", 32)
            sym_tv_usec = z3.BitVec(f"tv_usec_{int(py_time.time())}", 32)

            mem.store(tv_ptr, sym_tv_sec)
            mem.store(tv_ptr + 4, sym_tv_usec)
            regs[mips.MIPS_REG_V0] = 0
        elif tp == "trace":
            now = py_time.time()
            sec = int(now)
            usec = int((now - sec) * 1_000_000)
            mem.store(tv_ptr, sec)
            mem.store(tv_ptr + 4, usec)
            regs[mips.MIPS_REG_V0] = 0
            
        return regs, mem

    @staticmethod
    def clock(regs: Registers, mem: Memory, tp: str):
        if tp == "run":
            sym_clock = z3.BitVec(f"clock_val_{int(py_time.time())}", 32)
            regs[mips.MIPS_REG_V0] = sym_clock
        elif tp == "trace":
            regs[mips.MIPS_REG_V0] = int(py_time.time() * 1000)
            
        return regs, mem

    # pseudo-random
    @staticmethod
    def rand(regs: Registers, mem: Memory, tp: str):
        if tp == "run":
            rand_val = z3.BitVec(f"rand_{Libc._libc_rand_call_count}", 32)
            Libc._libc_rand_call_count += 1
            regs[mips.MIPS_REG_V0] = rand_val
        elif tp == "trace":
            A = 1103515245
            C = 12345

            current_seed = Libc._libc_rand_seed
            if isinstance(current_seed, z3.BitVecNumRef):
                current_seed = current_seed.as_long()
            elif not isinstance(current_seed, int):
                current_seed = 1
            
            new_seed = (current_seed * A + C) & 0xFFFFFFFF
            Libc._libc_rand_seed = new_seed
            rand_val = (new_seed // 65536) % 32768
            regs[mips.MIPS_REG_V0] = rand_val

        return regs, mem

    @staticmethod
    def srand(regs: Registers, mem: Memory, tp: str):
        seed = regs[mips.MIPS_REG_A0]
        Libc._libc_rand_seed = seed
        Libc._libc_rand_call_count = 0
        return regs, mem

    # sorting / search
    @staticmethod
    def qsort():
        pass

    @staticmethod
    def bsearch():
        pass

    # typecasting
    @staticmethod
    def atoi(regs, mem):
        # TODO
        # print(regs[mips.MIPS_REG_A0])
        pass

    @staticmethod
    def atol():
        # TODO
        pass

    @staticmethod
    def strtol():
        pass

    @staticmethod
    def strtod():
        pass

    # math
    @staticmethod
    def sin():
        pass

    @staticmethod
    def cos():
        pass

    @staticmethod
    def tan():
        pass

    @staticmethod
    def exp():
        pass

    @staticmethod
    def log():
        pass

    @staticmethod
    def pow():
        pass

    @staticmethod
    def sqrt():
        pass

    @staticmethod
    def ceil():
        pass

    @staticmethod
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
