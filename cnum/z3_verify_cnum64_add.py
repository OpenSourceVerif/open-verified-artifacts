# SPDX-License-Identifier: MIT
# Z3 formal verification for cnum64_add
# Theorem: forall ci, cj, x, y: ci non-empty and cj non-empty
#         and x in ci and y in cj implies x+y in cnum64_add(ci, cj)
#
# C implementation (from cnum_def.h, T=64):
#   is_empty:   base == U64_MAX && size == U64_MAX
#   contains:   if empty -> false
#               if urange_overflow -> v >= base || v <= base + size
#               else               -> v >= base && v <= base + size
#   urange_overflow: size > UT_MAX - base
#   add:        if empty -> EMPTY
#               if size_a > UT_MAX - size_b -> {0, UT_MAX}
#               else -> normalize({base_a+base_b, size_a+size_b})
#   normalize:  if size==UT_MAX && base!=0 && base!=ST_MAX -> base=0
#               else -> base unchanged

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
    cj_base = BitVec("cj_base", 64)
    cj_size = BitVec("cj_size", 64)
    x = BitVec("x", 64)
    y = BitVec("y", 64)

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
    cj_empty = is_empty(cj_base, cj_size)
    add_ov = UGT(ci_size, UT_MAX - cj_size)
    raw_base = ci_base + cj_base
    raw_size = ci_size + cj_size
    norm_res_base = normalize_base(raw_base, raw_size)
    norm_res_size = raw_size
    res_base = If(Or(ci_empty, cj_empty), EMPTY_base, If(UGT(ci_size, UT_MAX - cj_size), 0, norm_res_base))
    res_size = If(Or(ci_empty, cj_empty), EMPTY_size, If(UGT(ci_size, UT_MAX - cj_size), UT_MAX, norm_res_size))

    x_plus_y = x + y

    s = Solver()
    s.set("timeout", 36000000)

    s.add(Not(ci_empty))
    s.add(Not(cj_empty))
    s.add(contains(ci_base, ci_size, x))
    s.add(contains(cj_base, cj_size, y))
    s.add(Not(contains(res_base, res_size, x_plus_y)))

    print("Verifying cnum64_add (1hr timeout)...")
    print("Theorem: x in ci and y in cj implies x+y in cnum64_add(ci,cj)\n")

    result = s.check()
    elapsed = time.monotonic() - t0
    if result == sat:
        print("FAIL: Counterexample found!")
        print(f"  elapsed: {elapsed:.3f}s")
        return 1
    elif result == unsat:
        print("PASS: cnum64_add verified.")
        print(f"  elapsed: {elapsed:.3f}s")
        return 0
    else:
        print("UNKNOWN: solver timeout or error")
        print(f"  elapsed: {elapsed:.3f}s")
        return 2

if __name__ == "__main__":
    exit(main())
