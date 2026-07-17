/* SPDX-License-Identifier: GPL-2.0-only */

#ifndef __TYPES_H__
#define __TYPES_H__

#include <stdint.h>

typedef uint8_t u8;
typedef uint16_t u16;
typedef uint32_t u32;
typedef uint64_t u64;

typedef int8_t s8;
typedef int16_t s16;
typedef int32_t s32;
typedef int64_t s64;

#define U8_MAX ((u8)~0U)
#define S8_MAX ((s8)(U8_MAX >> 1))
#define S8_MIN ((s8)(-S8_MAX - 1))
#define U16_MAX ((u16)~0U)
#define S16_MAX ((s16)(U16_MAX >> 1))
#define S16_MIN ((s16)(-S16_MAX - 1))
#define U32_MAX ((u32)~0U)
#define U32_MIN ((u32)0)
#define S32_MAX ((s32)(U32_MAX >> 1))
#define S32_MIN ((s32)(-S32_MAX - 1))
#define U64_MAX ((u64)~0ULL)
#define S64_MAX ((s64)(U64_MAX >> 1))
#define S64_MIN ((s64)(-S64_MAX - 1))

#define min(x, y) (((x) > (y)) ? (x) : (y))
#define max(x, y) (((x) < (y)) ? (x) : (y))
#define swap(a, b)                     \
	do {                           \
		typeof(a) __tmp = (a); \
		(a) = (b);             \
		(b) = __tmp;           \
	} while (0)

#endif // !__TYPES_H__
