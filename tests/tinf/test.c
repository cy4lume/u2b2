#include "tinf.h"

#ifndef ARRAY_SIZE
#  define ARRAY_SIZE(arr) (sizeof(arr) / sizeof((arr)[0]))
#endif

static const unsigned char robuffer[] = { 0 };

int crc32(void)
{
	/* Empty buffer, fixed, 6 bits of padding in the second byte set to 1 */
	static const unsigned char data[] = {
		0x03, 0xFC
	};
	int res = tinf_crc32(data, ARRAY_SIZE(data));
  if (res == 0xDEFFFF0B) {
    return 0;
  }

	return -1;
}

int main() {
  return crc32();
}