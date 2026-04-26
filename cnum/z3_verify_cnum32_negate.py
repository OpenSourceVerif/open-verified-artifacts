# SPDX-License-Identifier: MIT
# Z3 formal verification for cnum32_negate
# Theorem: forall ci, x: ci non-empty and x in ci implies -x in cnum32_negate(ci)
#
# C implementation (from cnum_def.h, T=32):
#   is_empty:   base == U32_MAX && size == U32_MAX
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

    UT_MAX = BitVecVal(0xFFFFFFFF, 32)
    ST_MAX = BitVecVal(0x7FFFFFFF, 32)
    EMPTY_base = UT_MAX
    EMPTY_size = UT_MAX

    ci_base = BitVec("ci_base", 32)
    ci_size = BitVec("ci_size", 32)
    x = BitVec("x", 32)

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

    def negate_base(base,size):
        empty = is_empty(base, size)
        neg_base_raw = - (base + size)
        return normalize_base(neg_base_raw, size)

    ci_empty = is_empty(ci_base,ci_size)
    norm_neg_base = negate_base(ci_base,ci_size)
    res_base = If(ci_empty, EMPTY_base, norm_neg_base)
    res_size = If(ci_empty, EMPTY_size, ci_size)
    neg_x = - x

    s = Solver()
    s.set("timeout", 3600000)

    s.add(Not(ci_empty))
    s.add(contains(ci_base, ci_size, x))
    s.add(Not(contains(res_base, res_size, neg_x)))

    print("Verifying cnum32_negate (1hr timeout)...")
    print("Theorem: x in ci implies -x in cnum32_negate(ci)\n")

    result = s.check()
    elapsed = time.monotonic() - t0
    if result == sat:
        m = s.model()
        print("FAIL: Counterexample found!")
        return 1
    elif result == unsat:
        print("PASS: cnum32_negate verified.")
        print(f"  elapsed: {elapsed:.3f}s")
        return 0
    else:
        print("UNKNOWN: solver timeout or error")
        print(f"  elapsed: {elapsed:.3f}s")
        return 2

if __name__ == "__main__":
    exit(main())
