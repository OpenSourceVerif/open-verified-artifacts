# SPDX-License-Identifier: MIT
# Z3 formal verification for cnum32_lshr_const (cnum_def.h, T=32)
#
# Theorem: forall ci, k, x: ci non-empty, x in ci
#         implies (x >> (k & (T-1))) in lshr_const(ci, k)
#
# C implementation (from cnum_def.h):
#   lshr_const(ci, k):
#               if empty(ci)              -> EMPTY
#               k &= T-1;
#               if urange_overflow(ci) -> {0, UT_MAX>>k}
#               new_base = ci.base >> k
#               new_ub   = (ci.base + ci.size) >> k
#               return from_urange(new_base, new_ub)
#   from_urange(lo, hi): if lo > hi -> EMPTY; else {base=lo, size=hi-lo}

from z3 import *
import time

def main():
    t0 = time.monotonic()

    T = 32
    UT_MAX_VAL = (1 << T) - 1
    UT_MAX = BitVecVal(UT_MAX_VAL, T)
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
        # base + size as C uint32_t (wrap on overflow)
        sum_wrapped = (base + size) & UT_MAX
        return If(empty, False,
                  If(ov,
                     Or(UGE(v, base), ULE(v, sum_wrapped)),
                     And(UGE(v, base), ULE(v, base + size))))

    ci_empty = is_empty(ci_base, ci_size)
    ci_top   = is_top(ci_base, ci_size)
    ci_cul   = urange_overflow(ci_base, ci_size)

    # lshr_const: k &= T-1
    k_norm = k & BitVecVal(T - 1, T)
    # urange_overflow(ci): result is {0, UT_MAX>>k}
    cul_res_base = BitVecVal(0, T)
    cul_res_size = LShR(UT_MAX, k_norm)
    # non-cul path: from_urange(ci.base>>k, (ci.base+ci.size)>>k)
    new_base = LShR(ci_base, k_norm)
    new_ub   = LShR(ci_base + ci_size, k_norm)
    nc_base = If(UGT(new_base, new_ub), EMPTY_base, new_base)
    nc_size = If(UGT(new_base, new_ub), EMPTY_size, new_ub - new_base)

    res_base = If(ci_empty, EMPTY_base, If(ci_cul, cul_res_base, nc_base))
    res_size = If(ci_empty, EMPTY_size, If(ci_cul, cul_res_size, nc_size))

    x_shr = LShR(x, k_norm)

    # Theorem: x in ci  implies  x>>(k&31) in lshr_const(ci, k)
    # (k is unconstrained 32-bit; lshr_const internally normalizes it)
    theorem = Implies(
        contains(ci_base, ci_size, x),
        contains(res_base, res_size, x_shr))

    s = Solver()
    s.set("timeout", 3600000)
    s.add(Not(theorem))

    print("Verifying cnum32_lshr_const (1hr timeout)...")
    print("Theorem: ci non-empty, k unconstrained, x in ci")
    print("         implies (x>>(k&31)) in lshr_const(ci,k)\n")

    result = s.check()
    elapsed = time.monotonic() - t0
    if result == sat:
        m = s.model()
        print("FAIL: Counterexample found!")
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
