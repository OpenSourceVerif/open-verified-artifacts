# SPDX-License-Identifier: MIT
# Z3 formal verification for cnum32_lshr (range shift)
# Theorem: forall ci, cx, x, k:
#         ci non-empty, cx non-empty, x in ci, k in cx
#         implies (x >> k) in cnum32_lshr(ci, cx)
#
# C implementation (from cnum_def.h, T=32):
#   is_empty:  base == U32_MAX && size == U32_MAX
#   is_const:  size == 0
#   is_top:    base == 0 && size == U32_MAX
#   lshr_const(ci, k):
#               if empty(ci)  -> EMPTY
#               if top(ci)    -> ci
#               if k >= 32   -> top
#               if !cross_unsigned_limit(ci):
#                   from_urange(ci.base>>k, (ci.base+ci.size)>>k)
#               else -> top
#   lshr(ci, cx):
#               if empty(ci) -> EMPTY
#               if is_const(cx) -> lshr_const(ci, cx.base)
#               lb = lshr_const(ci, cx.base)
#               ub = lshr_const(cx, cx.base+cx.size)
#               if is_top(lb) || is_top(ub) -> top
#               else -> from_urange(umin(lb), umax(ub))

from z3 import *
import time

def main():
    t0 = time.monotonic()

    T = 32
    UT_MAX = BitVecVal((1 << T) - 1, T)
    EMPTY_base = UT_MAX
    EMPTY_size = UT_MAX
    TOP_base   = BitVecVal(0, T)
    TOP_size   = UT_MAX

    ci_base = BitVec("ci_base", T)
    ci_size = BitVec("ci_size", T)
    cx_base = BitVec("cx_base", T)
    cx_size = BitVec("cx_size", T)
    x = BitVec("x", T)
    k = BitVec("k", T)

    def is_empty(base, size):
        return And(base == EMPTY_base, size == EMPTY_size)

    def urange_overflow(base, size):
        return UGT(size, UT_MAX - base)

    def contains(base, size, v):
        empty = is_empty(base, size)
        ov = urange_overflow(base, size)
        return If(empty,
                  False,
                  If(ov,
                     Or(UGE(v, base), ULE(v, base + size)),
                     And(UGE(v, base), ULE(v, base + size))))

    def is_const(base, size):
        return size == 0

    def is_top(base, size):
        return And(base == TOP_base, size == TOP_size)

    def cross_unsigned_limit(base, size):
        if is_empty(base, size):
            return False
        if is_top(base, size):
            return False
        return And(contains(base, size, UT_MAX),
                   contains(base, size, BitVecVal(0, T)))

    # lshr_const(ci, k)
    ci_top = is_top(ci_base, ci_size)
    ci_crosses = And(Not(is_empty(ci_base, ci_size)),
                     Not(ci_top),
                     contains(ci_base, ci_size, UT_MAX),
                     contains(ci_base, ci_size, BitVecVal(0, T)))

    cx_overflow = UGT(cx_base, UT_MAX - cx_size)

    # overflow-aware k_max
    k_max = If(cx_overflow, BitVecVal(0, T), cx_base + cx_size)
    cx_max_k_large = UGE(k_max, BitVecVal(T, T))
    k_large = UGE(k, BitVecVal(T, T))

    # lshr_const(ci, k_max) — shift by max k
    lb_new_base = LShR(ci_base, k_max)
    lb_new_ub   = LShR(ci_base + ci_size, k_max)
    lb_exact_base = If(UGT(lb_new_base, lb_new_ub), EMPTY_base, lb_new_base)
    lb_exact_size = If(UGT(lb_new_base, lb_new_ub), EMPTY_size, lb_new_ub - lb_new_base)

    lb_base = If(Or(is_empty(ci_base, ci_size), ci_top),
                 ci_base,
                 If(cx_max_k_large,
                    TOP_base,
                    If(ci_crosses,
                       TOP_base,
                       lb_exact_base)))
    lb_size = If(Or(is_empty(ci_base, ci_size), ci_top),
                 ci_size,
                 If(cx_max_k_large,
                    TOP_size,
                    If(ci_crosses,
                       TOP_size,
                       lb_exact_size)))

    # lshr_const(ci, k) — shift by min k (k == cx.base)
    ub_new_base = LShR(ci_base, k)
    ub_new_ub   = LShR(ci_base + ci_size, k)
    ub_exact_base = If(UGT(ub_new_base, ub_new_ub), EMPTY_base, ub_new_base)
    ub_exact_size = If(UGT(ub_new_base, ub_new_ub), EMPTY_size, ub_new_ub - ub_new_base)

    ub_base = If(Or(is_empty(ci_base, ci_size), ci_top),
                 ci_base,
                 If(k_large,
                    TOP_base,
                    If(ci_crosses,
                       TOP_base,
                       ub_exact_base)))
    ub_size = If(Or(is_empty(ci_base, ci_size), ci_top),
                 ci_size,
                 If(k_large,
                    TOP_size,
                    If(ci_crosses,
                       TOP_size,
                       ub_exact_size)))

    # umin / umax
    def umin(base, size):
        return If(urange_overflow(base, size), BitVecVal(0, T), base)

    def umax(base, size):
        return If(urange_overflow(base, size), UT_MAX, base + size)

    # from_urange
    def from_urange(min_val, max_val):
        return If(UGT(min_val, max_val),
                  BitVecVal(EMPTY_base, T),
                  (max_val - min_val))

    # lshr(ci, cx)
    cx_const = is_const(cx_base, cx_size)

    res_base = If(Or(is_empty(ci_base, ci_size), is_empty(cx_base, cx_size)),
                  EMPTY_base,
                  If(cx_const,
                     lb_base,
                     If(cx_overflow,
                        TOP_base,
                        If(Or(is_top(lb_base, lb_size), is_top(ub_base, ub_size)),
                           TOP_base,
                           umin(lb_base, lb_size)))))
    res_size = If(Or(is_empty(ci_base, ci_size), is_empty(cx_base, cx_size)),
                  EMPTY_size,
                  If(cx_const,
                     lb_size,
                     If(cx_overflow,
                        TOP_size,
                        If(Or(is_top(lb_base, lb_size), is_top(ub_base, ub_size)),
                           TOP_size,
                           umax(ub_base, ub_size) - umin(lb_base, lb_size)))))

    x_shr = LShR(x, k)

    s = Solver()
    s.set("timeout", 36000000)

    s.add(contains(ci_base, ci_size, x))
    s.add(contains(cx_base, cx_size, k))
    s.add(Not(contains(res_base, res_size, x_shr)))

    print("Verifying cnum32_lshr range-shift (1hr timeout)...")
    print("Theorem: x in ci and k in cx implies (x>>k) in lshr(ci,cx)\n")

    result = s.check()
    elapsed = time.monotonic() - t0
    if result == sat:
        print("FAIL: Counterexample found!")
        return 1
    elif result == unsat:
        print("PASS: cnum32_lshr verified.")
        print(f"  elapsed: {elapsed:.3f}s")
        return 0
    else:
        print("UNKNOWN: solver timeout or error")
        print(f"  elapsed: {elapsed:.3f}s")
        return 2

if __name__ == "__main__":
    exit(main())
