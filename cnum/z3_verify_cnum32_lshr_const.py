# SPDX-License-Identifier: MIT
# Z3 formal verification for cnum32_lshr_const (cnum_def.h line 254-263, T=32)
#
# Theorem: forall ci, k, x: ci non-empty and 0 <= k < 32
#         implies (x >> k) in lshr_const(ci, k)
#
# C implementation (from cnum_def.h):
#   lshr_const(ci, k):
#               if empty(ci)                    -> EMPTY
#               if cross_unsigned_limit(ci)      -> {0, UT_MAX>>k}
#               new_base = ci.base >> k
#               new_ub   = (ci.base + ci.size) >> k
#               return from_urange(new_base, new_ub)
#   from_urange(lo, hi): if lo > hi -> EMPTY; else {base=lo, size=hi-lo}

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
    k       = BitVec("k", T)
    x       = BitVec("x", T)

    def is_empty(base, size):
        return And(base == EMPTY_base, size == EMPTY_size)

    def is_top(base, size):
        return And(base == TOP_base, size == TOP_size)

    def urange_overflow(base, size):
        return UGT(size, UT_MAX - base)

    def contains(base, size, v):
        empty = is_empty(base, size)
        ov    = urange_overflow(base, size)
        return If(empty, False,
                  If(ov,
                     Or(UGE(v, base), ULE(v, base + size)),
                     And(UGE(v, base), ULE(v, base + size))))

    def cross_unsigned_limit(base, size):
        return If(Or(is_empty(base, size), is_top(base, size)),
                  False,
                  And(contains(base, size, UT_MAX),
                      contains(base, size, BitVecVal(0, T))))

    # lshr_const: EMPTY if empty; UNBOUNDED if cross_unsigned_limit; else from_urange.
    new_base = LShR(ci_base, k)
    new_ub   = LShR(ci_base + ci_size, k)
    exact_base = If(UGT(new_base, new_ub), EMPTY_base, new_base)
    exact_size = If(UGT(new_base, new_ub), EMPTY_size, new_ub - new_base)

    ci_crosses = cross_unsigned_limit(ci_base, ci_size)
    # cross_unsigned_limit: result is [0, UT_MAX>>k] = {base=0, size=UT_MAX>>k}.
    res_base = If(is_empty(ci_base, ci_size), ci_base,
                  If(ci_crosses, BitVecVal(0, T),
                     exact_base))
    res_size = If(is_empty(ci_base, ci_size), ci_size,
                  If(ci_crosses, LShR(UT_MAX, k),
                     exact_size))

    x_shr = LShR(x, k)

    # Theorem: ci non-empty, 0 <= k < T, x in ci  implies  x>>k in res
    theorem = Implies(
        And(ULE(k, BitVecVal(T - 1, T)),  # 0 <= k < T
            contains(ci_base, ci_size, x)),
        contains(res_base, res_size, x_shr))

    s = Solver()
    s.set("timeout", 3600000)
    s.add(Not(theorem))
    
    result = s.check()
    elapsed = time.monotonic() - t0
    if result == sat:
        print("FAIL: Counterexample found!")
        print(f"  elapsed: {elapsed:.3f}s")
        return 1
    elif result == unsat:
        print("PASS: cnum32_lshr_const verified.")
        print(f"  elapsed: {elapsed:.3f}s")
        return 0
    else:
        print("UNKNOWN: solver timeout or error")
        print(f"  elapsed: {elapsed:.3f}s")
        return 2

if __name__ == "__main__":
    exit(main())
