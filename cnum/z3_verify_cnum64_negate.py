# SPDX-License-Identifier: MIT
# Z3 formal verification for cnum64_negate
# Theorem: forall ci, x: ci non-empty and x in ci implies -x in cnum64_negate(ci)
#
# C implementation (from cnum_def.h, T=64):
#   is_empty:   base == U64_MAX && size == U64_MAX
#   contains:   if empty -> false
#               if urange_overflow -> v >= base || v <= base + size
#               else               -> v >= base && v <= base + size
#   negate:     if empty -> EMPTY
#               else -> normalize({-(base+size), size})

from z3 import *
import time

def main():
    set_param("timeout", 3600000)
    t0 = time.monotonic()

    UT_MAX = BitVecVal(0xFFFFFFFFFFFFFFFF, 64)
    ST_MAX = BitVecVal(0x7FFFFFFFFFFFFFFF, 64)
    EMPTY_base = UT_MAX
    EMPTY_size = UT_MAX

    ci_base = BitVec("ci_base", 64)
    ci_size = BitVec("ci_size", 64)
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

    def normalize_base(base, size):
        cond = And(size == UT_MAX, base != 0)
        return If(cond, 0, base)

    ci_empty = is_empty(ci_base, ci_size)
    neg_base_raw = - (ci_base + ci_size)
    norm_neg_base = normalize_base(neg_base_raw, ci_size)
    res_base = If(ci_empty, EMPTY_base, norm_neg_base)
    res_size = If(ci_empty, EMPTY_size, ci_size)
    neg_x = - x

    s = Solver()
    s.set("timeout", 3600000)

    s.add(Not(ci_empty))
    s.add(contains(ci_base, ci_size, x))
    s.add(Not(contains(res_base, res_size, neg_x)))

    print("Verifying cnum64_negate (1hr timeout)...")
    print("Theorem: x in ci implies -x in cnum64_negate(ci)\n")

    result = s.check()
    elapsed = time.monotonic() - t0
    if result == sat:
        m = s.model()
        print("FAIL: Counterexample found!")
        print(f"  elapsed: {elapsed:.3f}s")
        print(f"  ci = ({m[ci_base]}, {m[ci_size]})")
        print(f"  x  = {m[x]}")
        print(f"  -x = {m[neg_x]}")
        print(f"  result = ({m[res_base]}, {m[res_size]})")
        return 1
    elif result == unsat:
        print("PASS: cnum64_negate verified.")
        print(f"  elapsed: {elapsed:.3f}s")
        return 0
    else:
        print("UNKNOWN: solver timeout or error")
        print(f"  elapsed: {elapsed:.3f}s")
        return 2

if __name__ == "__main__":
    exit(main())
