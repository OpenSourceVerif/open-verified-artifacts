# SPDX-License-Identifier: MIT
# Z3 formal verification for cnum32_lshr
# Theorem: forall ci, cx, x, k:
#         ci non-empty, cx non-empty, x in ci, k in cx, cx constant
#         implies (x >> k) in cnum32_lshr(ci, cx)
#
# C implementation (from cnum_def.h, T=32):
#   is_const:  size == 0
#   lshr_const(ci,k):  see z3_verify_cnum32_lshr_const.py
#   lshr(ci, cx):      if empty -> EMPTY
#                       if is_const(cx) -> lshr_const(ci, cx.base)
#                       else -> top

from z3 import *
import time

def main():
    t0 = time.monotonic()

    UT_MAX = BitVecVal(0xFFFFFFFF, 32)
    EMPTY_base = UT_MAX
    EMPTY_size = UT_MAX

    ci_base = BitVec("ci_base", 32)
    ci_size = BitVec("ci_size", 32)
    cx_base = BitVec("cx_base", 32)
    cx_size = BitVec("cx_size", 32)
    x = BitVec("x", 32)
    k = BitVec("k", 32)

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

    ci_top = And(ci_base == BitVecVal(0, 32), ci_size == UT_MAX)
    ci_crosses = And(Not(is_empty(ci_base, ci_size)),
                     Not(ci_top),
                     contains(ci_base, ci_size, UT_MAX),
                     contains(ci_base, ci_size, BitVecVal(0, 32)))

    cx_top = And(cx_base == BitVecVal(0, 32), cx_size == UT_MAX)
    k_large = UGE(cx_base, BitVecVal(32, 32))
    cx_const = is_const(cx_base, cx_size)

    # lshr_const(ci, cx.base) — exact branch
    new_base = LShR(ci_base, cx_base)
    new_ub   = LShR(ci_base + ci_size, cx_base)
    exact_base = If(UGT(new_base, new_ub), EMPTY_base, new_base)
    exact_size = If(UGT(new_base, new_ub), EMPTY_size, new_ub - new_base)
    lshr_const_base = If(Or(is_empty(ci_base, ci_size), ci_top),
                         ci_base,
                         If(k_large,
                            BitVecVal(0, 32),
                            If(ci_crosses,
                               BitVecVal(0, 32),
                               exact_base)))
    lshr_const_size = If(Or(is_empty(ci_base, ci_size), ci_top),
                         ci_size,
                         If(k_large,
                            UT_MAX,
                            If(ci_crosses,
                               UT_MAX,
                               exact_size)))

    # lshr(ci, cx)
    res_base = If(Or(is_empty(ci_base, ci_size), is_empty(cx_base, cx_size)),
                  EMPTY_base,
                  If(cx_const,
                     lshr_const_base,
                     BitVecVal(0, 32)))
    res_size = If(Or(is_empty(ci_base, ci_size), is_empty(cx_base, cx_size)),
                  EMPTY_size,
                  If(cx_const,
                     lshr_const_size,
                     UT_MAX))

    x_shr = LShR(x, k)

    s = Solver()
    s.set("timeout", 36000000)

    s.add(contains(ci_base, ci_size, x))
    s.add(contains(cx_base, cx_size, k))
    s.add(Not(contains(res_base, res_size, x_shr)))

    print("Verifying cnum32_lshr (1hr timeout)...")
    print("Theorem: x in ci and k in cx (cx constant) implies (x>>k) in lshr(ci,cx)\n")

    result = s.check()
    elapsed = time.monotonic() - t0
    if result == sat:
        print("FAIL: Counterexample found!")
        print(f"  elapsed: {elapsed:.3f}s")
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
