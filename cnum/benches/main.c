/* SPDX-License-Identifier: GPL-2.0-only */

#include "types.h"
#include <stdio.h>
#include <time.h>

#include "cnum.h"

#define ITERS 100000000ULL

static volatile u64 sink = 0;

static u64 nsec_diff(struct timespec start, struct timespec end)
{
	time_t sec = end.tv_sec - start.tv_sec;
	long nsec = end.tv_nsec - start.tv_nsec;

	if (nsec < 0) {
		sec--;
		nsec += 1000000000L;
	}

	return (u64)sec * 1000000000ULL + (u64)nsec;
}

#define MEASURE(elapsed, consume, func, ...)                      \
	do {                                                      \
		struct timespec start, end;                       \
		u64 acc = 0;                                      \
		*elapsed = 0;                                     \
                                                                  \
		clock_gettime(CLOCK_MONOTONIC, &start);           \
		for (u64 i = 0; i < ITERS; i++)                   \
			acc += (consume)((func)(__VA_ARGS__));    \
		clock_gettime(CLOCK_MONOTONIC, &end);             \
                                                                  \
		sink += acc;                                      \
                                                                  \
		*elapsed = (double)nsec_diff(start, end) / ITERS; \
	} while (0)

#define BENCH(bench, name1, name2, consume, func1, func2, ...)               \
	do {                                                                 \
		double ns1, ns2;                                             \
                                                                             \
		MEASURE(&ns1, (consume), (func1), __VA_ARGS__);              \
		MEASURE(&ns2, (consume), (func2), __VA_ARGS__);              \
                                                                             \
		printf("%-32s %s: %8.3f ns/op   %s: %8.3f ns/op\n", (bench), \
		       (name1), ns1, (name2), ns2);                          \
	} while (0)

static inline u64 consume_bool(bool v)
{
	return v;
}

static void bench_contains(const char *name, struct cnum64 c, u64 v)
{
	BENCH(name, "contains", "contains_new", consume_bool, cnum64_contains,
	      cnum64_contains_new, c, v);
}

static void run_contains_bench(void)
{
	printf("# contains bench\n");

	bench_contains("empty", CNUM64_EMPTY, 42);

	bench_contains("non-overflow inside",
		       (struct cnum64){ .base = 1000, .size = 100 }, 1050);

	bench_contains("non-overflow outside",
		       (struct cnum64){ .base = 1000, .size = 100 }, 5000);

	bench_contains("overflow high side",
		       (struct cnum64){ .base = U64_MAX - 100, .size = 200 },
		       U64_MAX - 50);

	bench_contains("overflow low side",
		       (struct cnum64){ .base = U64_MAX - 100, .size = 200 },
		       50);

	bench_contains("overflow outside",
		       (struct cnum64){ .base = U64_MAX - 100, .size = 200 },
		       500);

	bench_contains("singleton inside",
		       (struct cnum64){ .base = 42, .size = 0 }, 42);

	bench_contains("singleton outside",
		       (struct cnum64){ .base = 42, .size = 0 }, 43);

	bench_contains("full range", CNUM64_UNBOUNDED, 123456);
}

static inline u64 consume_cnum64(struct cnum64 c)
{
	return c.base + c.size;
}

static void bench_normalize(const char *name, struct cnum64 c)
{
	BENCH(name, "normalize", "normalize_new", consume_cnum64,
	      cnum64_normalize, cnum64_normalize_new, c);
}

static void run_normalize_bench(void)
{
	printf("# normalize bench\n");

	bench_normalize("normal small range",
			(struct cnum64){ .base = 1000, .size = 100 });

	bench_normalize("full range normalized", CNUM64_UNBOUNDED);

	bench_normalize("full range nonzero base",
			(struct cnum64){ .base = 42, .size = U64_MAX });

	bench_normalize("empty", CNUM64_EMPTY);

	bench_normalize("signed max full range",
			(struct cnum64){ .base = (u64)S64_MAX,
					 .size = U64_MAX });

	bench_normalize("max base singleton",
			(struct cnum64){ .base = U64_MAX, .size = 0 });
}

static inline u64 consume_s64(s64 v)
{
	return (u64)v;
}

static void bench_smin(const char *name, struct cnum64 c)
{
	BENCH(name, "smin", "smin_new", consume_s64, cnum64_smin,
	      cnum64_smin_new, c);
}

static void run_smin_bench(void)
{
	printf("# smin bench\n");

	bench_smin("empty", CNUM64_EMPTY);

	bench_smin("positive range", (struct cnum64){ .base = 10, .size = 10 });

	bench_smin("negative range",
		   (struct cnum64){ .base = (u64)-20, .size = 10 });

	bench_smin("cross zero",
		   (struct cnum64){ .base = (u64)-10, .size = 20 });

	bench_smin("signed overflow boundary",
		   (struct cnum64){ .base = (u64)S64_MAX, .size = 1 });

	bench_smin("signed overflow range",
		   (struct cnum64){ .base = (u64)S64_MAX - 10, .size = 20 });

	bench_smin("unsigned overflow range",
		   (struct cnum64){ .base = U64_MAX - 10, .size = 20 });

	bench_smin("full range", CNUM64_UNBOUNDED);
}

static void bench_smax(const char *name, struct cnum64 c)
{
	BENCH(name, "smax", "smax_new", consume_s64, cnum64_smax,
	      cnum64_smax_new, c);
}

static void run_smax_bench(void)
{
	printf("# smax bench\n");

	bench_smax("empty", CNUM64_EMPTY);

	bench_smax("positive range", (struct cnum64){ .base = 10, .size = 10 });

	bench_smax("negative range",
		   (struct cnum64){ .base = (u64)-20, .size = 10 });

	bench_smax("cross zero",
		   (struct cnum64){ .base = (u64)-10, .size = 20 });

	bench_smax("signed overflow boundary",
		   (struct cnum64){ .base = (u64)S64_MAX, .size = 1 });

	bench_smax("signed overflow range",
		   (struct cnum64){ .base = (u64)S64_MAX - 10, .size = 20 });

	bench_smax("unsigned overflow range",
		   (struct cnum64){ .base = U64_MAX - 10, .size = 20 });

	bench_smax("full range", CNUM64_UNBOUNDED);
}

int main(void)
{
	run_contains_bench();
	printf("\n");
	run_normalize_bench();
	printf("\n");
	run_smin_bench();
	printf("\n");
	run_smax_bench();
	printf("sink: %lu\n", sink);

	return 0;
}
