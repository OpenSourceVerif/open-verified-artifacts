# SPDX-License-Identifier: MIT
# Z3 formal verification for cnum32_lshr (cnum_def.h, T=32)
#
# Theorem: forall ci, cx, x, k:
#         ci non-empty, cx non-empty, cx non-overflow, x in ci, k in cx, 0 <= k < T
#         implies (x >> k) in lshr(ci, cx)
#
# C implementation (from cnum_def.h):
#   lshr(ci, cx):
#               if empty(ci)        -> EMPTY
#               if empty(cx)        -> EMPTY
#               if is_const(cx)     -> lshr_const(ci, cx.base)
#               if cross_unsigned_limit(ci) -> {0, UT_MAX>>cx.base}
#               k_min = cx.base
#               k_max = cx.base + cx.size
#               return from_urange(ci.base>>k_max, (ci.base+ci.size)>>k_min)
#   lshr_const(ci, k):
#               if empty(ci)                   -> EMPTY
#               if cross_unsigned_limit(ci)    -> {0, UT_MAX>>k}
#               return from_urange(ci.base>>k, (ci.base+ci.size)>>k)
#   from_urange(lo,hi): if lo>hi -> EMPTY; else {base=lo, size=hi-lo}
#   cross_unsigned_limit(c): non-empty, non-top, contains both UT_MAX and 0

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
    cx_base = BitVec("cx_base", T)
    cx_size = BitVec("cx_size", T)
    x       = BitVec("x", T)
    k       = BitVec("k", T)

    def is_empty(base, size):
        return And(base == EMPTY_base, size == EMPTY_size)

    def is_top(base, size):
        return And(base == TOP_base, size == TOP_size)

    def is_const(base, size):
        return size == BitVecVal(0, T)

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

    # C: from_urange(lo, hi): if lo>hi -> EMPTY; else {base=lo, size=hi-lo}
    # hi may underflow below lo due to unsigned wrap in (ci.base+ci.size)>>k_min
    def from_urange(lo, hi):
        ov   = UGT(lo, hi)
        size = If(ov, hi - lo + UT_MAX + BitVecVal(1, T), hi - lo)
        return If(And(Not(is_empty(ci_base, ci_size)), Not(is_top(ci_base, ci_size)), ov),
                  # wrapped interval: [lo..UT_MAX] U [0..hi]
                  If(urange_overflow(lo, size), (EMPTY_base, EMPTY_size),
                     (lo, size)),
                  (lo, size))

    cx_const = is_const(cx_base, cx_size)
    cx_empty = is_empty(cx_base, cx_size)
    cx_ov    = UGT(cx_base, UT_MAX - cx_size)

    # --- const cx path: lshr_const(ci, cx.base) ---
    lo_const = LShR(ci_base, cx_base)
    hi_const = LShR(ci_base + ci_size, cx_base)
    sz_const = If(UGT(hi_const, lo_const), hi_const - lo_const,
                  hi_const - lo_const + UT_MAX + BitVecVal(1, T))
    const_res_b = If(cross_unsigned_limit(ci_base, ci_size), BitVecVal(0, T), lo_const)
    const_res_s = If(cross_unsigned_limit(ci_base, ci_size), LShR(UT_MAX, cx_base), sz_const)

    # --- non-const cx path: from_urange(ci.base>>k_max, (ci.base+ci.size)>>k_min) ---
    k_min = cx_base
    k_max = cx_base + cx_size
    lo    = LShR(ci_base, k_max)
    hi    = LShR(ci_base + ci_size, k_min)
    ov_lu = UGT(lo, hi)
    sz_nc = If(ov_lu, hi - lo + UT_MAX + BitVecVal(1, T), hi - lo)
    nc_res_b = lo
    nc_res_s = sz_nc

    # --- cross_unsigned_limit(ci) early return: {0, UT_MAX>>cx.base} ---
    cul_ov  = cross_unsigned_limit(ci_base, ci_size)
    cul_res_b = BitVecVal(0, T)
    cul_res_s = LShR(UT_MAX, cx_base)

    ci_empty = is_empty(ci_base, ci_size)
    ci_top   = is_top(ci_base, ci_size)

    res_b = If(Or(ci_empty, cx_empty), EMPTY_base,
               If(ci_top, TOP_base,
                  If(cul_ov, cul_res_b,
                     If(cx_const, const_res_b, nc_res_b))))
    res_s = If(Or(ci_empty, cx_empty), EMPTY_size,
               If(ci_top, TOP_size,
                  If(cul_ov, cul_res_s,
                     If(cx_const, const_res_s, nc_res_s))))

    x_shr = LShR(x, k)

    # Theorem: ci non-empty, cx non-empty, cx non-overflow, x in ci, k in cx, 0 <= k < T
    #          implies x>>k in lshr(ci, cx)
    theorem = Implies(
        And(Not(ci_empty),
            Not(cx_empty),
            Not(ci_top),
            Not(cx_const),
            Not(cx_ov),
            contains(ci_base, ci_size, x),
            contains(cx_base, cx_size, k),
            ULE(k, BitVecVal(T - 1, T))),
        contains(res_b, res_s, x_shr))

    s = Solver()
    s.set("timeout", 3600000)
    s.add(Not(theorem))

    print("Verifying cnum32_lshr (1hr timeout)...")
    print("Theorem: ci non-empty, cx non-empty, cx non-overflow, x in ci, k in cx, 0 <= k < 32")
    print("         implies (x>>k) in lshr(ci,cx)\n")

    result = s.check()
    elapsed = time.monotonic() - t0
    if result == sat:
        m = s.model()
        print("FAIL: Counterexample found!")
        print(f"  elapsed: {elapsed:.3f}s")
        def u(name): return m[name].as_long()
        print(f"\n  ci  = {{base={u(ci_base)}, size={u(ci_size)}}}  top={bool(m[ci_base]==0 and m[ci_size]==UT_MAX_VAL)}")
        print(f"  cx  = {{base={u(cx_base)}, size={u(cx_size)}}}  const={bool(u(cx_size)==0)}  overflow={bool(u(cx_base) > UT_MAX_VAL - u(cx_size))}")
        print(f"  x   = {u(x)}")
        print(f"  k   = {u(k)}")
        print(f"  x>>k = {u(x) >> u(k)}")
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
