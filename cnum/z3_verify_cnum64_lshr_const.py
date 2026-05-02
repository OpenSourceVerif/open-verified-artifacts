# SPDX-License-Identifier: MIT
# Z3 formal verification for cnum64_lshr_const
# Theorem: forall ci, k, x: ci non-empty and x in ci and k < 64
#         implies (x >> k) in cnum64_lshr_const(ci, k)
#
# C implementation (from cnum_def.h, T=64):
#   is_empty:        base == U64_MAX && size == U64_MAX
#   contains:        if empty -> false
#                   if urange_overflow -> v >= base || v <= base + size
#                   else               -> v >= base && v <= base + size
#   urange_overflow: size > UT_MAX - base
#   cross_unsigned_limit:
#                   if empty -> false
#                   if top (base==0 && size==UT_MAX) -> false
#                   else -> contains(UT_MAX) && contains(0)
#   lshr_const(ci,k):
#                   if empty -> EMPTY
#                   if top   -> ci  (unchanged)
#                   if k >= 64 -> top
#                   if !cross_unsigned_limit(ci):
#                       from_urange(ci.base>>k, (ci.base+ci.size)>>k)
#                   else -> top

from z3 import *
import time

def main():
    t0 = time.monotonic()

    UT_MAX = BitVecVal(0xFFFFFFFFFFFFFFFF, 64)
    EMPTY_base = UT_MAX
    EMPTY_size = UT_MAX

    ci_base = BitVec("ci_base", 64)
    ci_size = BitVec("ci_size", 64)
    k = BitVec("k", 64)
    x = BitVec("x", 64)

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

    ci_top = And(ci_base == BitVecVal(0, 64), ci_size == UT_MAX)

    ci_crosses = And(Not(is_empty(ci_base, ci_size)),
                     Not(ci_top),
                     contains(ci_base, ci_size, UT_MAX),
                     contains(ci_base, ci_size, BitVecVal(0, 64)))

    k_large = UGE(k, BitVecVal(64, 64))

    # from_urange(ci.base>>k, (ci.base+ci.size)>>k)
    new_base = LShR(ci_base, k)
    new_ub   = LShR(ci_base + ci_size, k)
    exact_base = If(UGT(new_base, new_ub), EMPTY_base, new_base)
    exact_size = If(UGT(new_base, new_ub), EMPTY_size, new_ub - new_base)

    res_base = If(Or(is_empty(ci_base, ci_size), ci_top),
                  ci_base,
                  If(k_large,
                     BitVecVal(0, 64),
                     If(ci_crosses,
                        BitVecVal(0, 64),
                        exact_base)))
    res_size = If(Or(is_empty(ci_base, ci_size), ci_top),
                  ci_size,
                  If(k_large,
                     UT_MAX,
                     If(ci_crosses,
                        UT_MAX,
                        exact_size)))

    x_shr = LShR(x, k)

    s = Solver()
    s.set("timeout", 36000000)

    s.add(contains(ci_base, ci_size, x))
    s.add(Not(contains(res_base, res_size, x_shr)))

    print("Verifying cnum64_lshr_const (1hr timeout)...")
    print("Theorem: x in ci and k < 64 implies (x>>k) in lshr_const(ci,k)\n")

    result = s.check()
    elapsed = time.monotonic() - t0
    if result == sat:
        print("FAIL: Counterexample found!")
        print(f"  elapsed: {elapsed:.3f}s")
        return 1
    elif result == unsat:
        print("PASS: cnum64_lshr_const verified.")
        print(f"  elapsed: {elapsed:.3f}s")
        return 0
    else:
        print("UNKNOWN: solver timeout or error")
        print(f"  elapsed: {elapsed:.3f}s")
        return 2

if __name__ == "__main__":
    exit(main())
