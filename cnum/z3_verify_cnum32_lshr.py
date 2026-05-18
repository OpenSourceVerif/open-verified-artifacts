# SPDX-License-Identifier: MIT
# Z3 formal verification for cnum32_lshr (cnum_def.h, T=32)
#
# Theorem: forall ci, cx, x, k:
#         ci non-empty, cx non-empty, x in ci, k in cx
#         implies (x >> (k & (T-1))) in lshr(ci, cx)
#
# C implementation (from cnum_def.h, lines 264-294):
#
#   normalize_shift_k(k):
#       if (k.size >= T) || (k.base % T + k.size >= T)
#           return {0, T-1};              // wraps or spans [T-1, T] -> all [0,T-1]
#       if (k.base >= T)
#           return {k.base % T, k.size}; // base truncated to [0,T-1]
#       return k;                        // unchanged
#
#   lshr(ci, cx):
#       if empty(ci) || empty(cx)         -> EMPTY
#       normalized_k = normalize_shift_k(cx)
#       if is_const(normalized_k)         -> lshr_const(ci, normalized_k.base)
#       if cross_unsigned_limit(ci)       -> {0, UT_MAX>>normalized_k.base}
#       return from_urange(ci.base>>(norm_b+norm_s), ci_upper>>norm_b)
#       (C shift implicitly masks shift amount by (T-1))
#
#   lshr_const(ci, k):
#       if empty(ci)                       -> EMPTY
#       k &= T-1
#       if cross_unsigned_limit(ci)       -> {0, UT_MAX>>k}
#       new_base = ci.base >> k
#       new_ub   = (ci.base + ci.size) >> k
#       return from_urange(new_base, new_ub)
#
#   from_urange(lo, hi): if lo > hi -> EMPTY; else {base=lo, size=hi-lo}
#
#   cross_unsigned_limit(cnum):
#       false if empty or {0, UT_MAX} (top)
#       true  if contains(UT_MAX) && contains(0)

from z3 import *
import time

def main():
    t0 = time.monotonic()

    T = 32
    UT_MAX_VAL = (1 << T) - 1
    UT_MAX = BitVecVal(UT_MAX_VAL, T)
    # EMPTY = {U32_MAX, U32_MAX} -- sentinel: base == size == UT_MAX
    EMPTY_base = UT_MAX
    EMPTY_size = UT_MAX
    # UNBOUNDED (top) = {0, U32_MAX} -- represents all 32-bit values
    TOP_base   = BitVecVal(0, T)
    TOP_size   = UT_MAX

    # Symbolic inputs
    ci_base = BitVec("ci_base", T)
    ci_size = BitVec("ci_size", T)
    cx_base = BitVec("cx_base", T)
    cx_size = BitVec("cx_size", T)
    x       = BitVec("x", T)
    k       = BitVec("k", T)

    # ---- Primitive helpers ----

    def is_empty(base, size):
        # EMPTY = {UT_MAX, UT_MAX}
        return And(base == EMPTY_base, size == EMPTY_size)

    def is_top(base, size):
        # UNBOUNDED = {0, UT_MAX}
        return And(base == TOP_base, size == TOP_size)

    def is_const(base, size):
        # Single value: size == 0
        return size == BitVecVal(0, T)

    def urange_overflow(base, size):
        # [base, base+size] overflows 32-bit wrap-around
        return UGT(size, UT_MAX - base)

    def contains(base, size, v):
        """True iff unsigned value v is in the circular range [base, base+size]."""
        empty = is_empty(base, size)
        ov    = urange_overflow(base, size)
        # base+size as C uint32_t: wrap on overflow
        sum_wrapped = (base + size) & UT_MAX
        return If(empty, False,
                  If(ov,
                     Or(UGE(v, base), ULE(v, sum_wrapped)),
                     And(UGE(v, base), ULE(v, base + size))))

    def cross_unsigned_limit(base, size):
        """
        True iff the range contains both UT_MAX and 0.
        Excludes empty and top ({0, UT_MAX}).
        In C: contains(UT_MAX) && contains(0)
        """
        return If(Or(is_empty(base, size), is_top(base, size)),
                  False,
                  And(contains(base, size, UT_MAX),
                      contains(base, size, BitVecVal(0, T))))

    # ---- Preconditions (theorem assumptions) ----
    ci_empty = is_empty(ci_base, ci_size)
    cx_empty = is_empty(cx_base, cx_size)
    cx_top   = is_top(cx_base, cx_size)
    ci_cul   = cross_unsigned_limit(ci_base, ci_size)

    # ---- normalize_shift_k(cx) ----
    # Equivalent C: (cx.size >= T) || (cx.base % T + cx.size >= T)
    # cx.size >= T  =>  normalized to {0, T-1} (UNBOUNDED)
    # (cx.base % T + cx.size >= T)  =>  range wraps [T-1, T] boundary -> {0, T-1}
    cx_size_ge_T   = UGT(cx_size, BitVecVal(T - 1, T))           # cx.size >= T
    cx_base_mod_T  = cx_base & BitVecVal(T - 1, T)               # cx.base % T
    cx_wrap_T      = UGT(cx_base_mod_T + cx_size, BitVecVal(T - 1, T))  # wraps past T-1
    norm_wraps_or_ge_T = Or(cx_size_ge_T, cx_wrap_T)             # -> {0, T-1}
    norm_base_ge_T = UGT(cx_base, BitVecVal(T - 1, T))            # cx.base >= T

    # normalize_shift_k result fields
    norm_b = If(norm_wraps_or_ge_T, TOP_base,
                If(norm_base_ge_T,  cx_base_mod_T,
                                      cx_base))
    norm_s = If(norm_wraps_or_ge_T, TOP_size,
                                      cx_size)

    norm_const      = is_const(norm_b, norm_s)   # size == 0
    norm_unbounded  = And(norm_b == TOP_base, norm_s == TOP_size)

    # ci_upper = ci.base + ci.size  (C uint32_t wrap, used by all paths)
    ci_upper = (ci_base + ci_size) & UT_MAX

    # ---- lshr_const path ----
    # C source: lshr_const(ci, normalized_k.base), which does k &= T-1 internally
    k_norm = norm_b & BitVecVal(T - 1, T)   # normalized_k.base masked
    const_cul_res_b = BitVecVal(0, T)
    const_cul_res_s = LShR(UT_MAX, k_norm)   # {0, UT_MAX>>k}
    const_nc_b = LShR(ci_base, k_norm)       # ci.base >> k
    const_nc_h = LShR(ci_upper, k_norm)      # ci_upper >> k
    const_nc_b2 = If(UGT(const_nc_b, const_nc_h), EMPTY_base, const_nc_b)
    const_nc_s2 = If(UGT(const_nc_b, const_nc_h), EMPTY_size, const_nc_h - const_nc_b)
    const_res_b = If(ci_cul, const_cul_res_b, const_nc_b2)
    const_res_s = If(ci_cul, const_cul_res_s, const_nc_s2)

    # ---- general (non-const) path ----
    # C source (line 293):
    #   from_urange(ci.base >> (norm_b + norm_s), ci_upper >> norm_b)
    # C right-shift implicitly masks shift amount by (T-1).
    # norm_b       = normalized_k.base
    # norm_b+norm_s = normalized_k.base + normalized_k.size
    norm_b_masked    = norm_b & BitVecVal(T - 1, T)
    norm_bsum_masked = (norm_b + norm_s) & BitVecVal(T - 1, T)
    k_min_is_zero = (norm_b_masked == BitVecVal(0, T))
    # lo = ci_base >> (norm_b+norm_s)  (first arg to from_urange = minimum result)
    lo_nc = LShR(ci_base, norm_bsum_masked)
    # hi = ci_upper >> norm_b          (second arg to from_urange = maximum result)
    hi_nc_raw = LShR(ci_upper, norm_b_masked)
    # C uint32_t wrap: when ci crosses UL and k_min==0, ci_upper>>0 = UT_MAX
    hi_nc = If(And(ci_cul, k_min_is_zero), UT_MAX, hi_nc_raw)
    # from_urange: if lo > hi -> EMPTY
    nc_res_b = If(UGT(lo_nc, hi_nc), EMPTY_base, lo_nc)
    nc_res_s = If(UGT(lo_nc, hi_nc), EMPTY_size, hi_nc - lo_nc)

    # ---- cross_unsigned_limit(ci) early-return in general path ----
    # C source (line 292): {0, UT_MAX >> normalized_k.base}
    # normalized_k.base is norm_b; C >> operator implicitly masks by (T-1)
    cul_res_b = BitVecVal(0, T)
    cul_res_s = LShR(UT_MAX, norm_b_masked)

    # ---- Full lshr result ----
    # C source (lines 286-293):
    # 1. empty ci or cx            -> EMPTY
    # 2. ci crosses UL             -> {0, UT_MAX >> norm_b}
    # 3. const normalized_k       -> lshr_const result
    # 4. general (non-cul)        -> from_urange(ci.base>>(norm_b+norm_s), ci_upper>>norm_b)
    res_b = If(Or(ci_empty, cx_empty), EMPTY_base,
               If(ci_cul, cul_res_b,
                  If(norm_const, const_res_b, nc_res_b)))
    res_s = If(Or(ci_empty, cx_empty), EMPTY_size,
               If(ci_cul, cul_res_s,
                  If(norm_const, const_res_s, nc_res_s)))

    # ---- Theorem ----
    # x_shr = x >> (k & (T-1))  -- actual C right-shift of chosen k in chosen cx
    x_shr = LShR(x, k & BitVecVal(T - 1, T))

    # Theorem: ci non-empty, cx non-empty, x in ci, k in cx
    #          => x>>(k&31) is in lshr(ci, cx)
    theorem = Implies(
        And(Not(ci_empty), Not(cx_empty),
            contains(ci_base, ci_size, x),
            contains(cx_base, cx_size, k)),
        contains(res_b, res_s, x_shr))

    # ---- Solver: try to find a counterexample ----
    s = Solver()
    s.set("timeout", 3600000)
    s.set("threads", 16)
    s.add(Not(theorem))  # Negate: find case where theorem is violated

    print("Verifying cnum32_lshr (1hr timeout, 16 threads)...")
    print("Theorem: ci non-empty, cx non-empty, x in ci, k in cx")
    print("         implies (x >> (k & 31)) in lshr(ci, cx)\n")

    result = s.check()
    elapsed = time.monotonic() - t0
    if result == sat:
        m = s.model()
        print("FAIL: Counterexample found!")
        print(f"  elapsed: {elapsed:.3f}s")
        def u(name):    return m[name].as_long()
        def ev(expr):   return m.eval(expr).as_long()
        def evb(expr):  return is_true(m.eval(expr))
        print(f"\n  ci        = {{base={u(ci_base)}, size={u(ci_size)}}}")
        print(f"  cx        = {{base={u(cx_base)}, size={u(cx_size)}}}")
        print(f"  ci_empty  = {evb(ci_empty)}")
        print(f"  ci_cul    = {evb(ci_cul)}")
        print(f"  cx_empty  = {evb(cx_empty)}  cx_top = {evb(cx_top)}")
        print(f"  norm_b    = {ev(norm_b)}  norm_s = {ev(norm_s)}")
        print(f"  norm_const     = {evb(norm_const)}")
        print(f"  norm_unbounded  = {evb(norm_unbounded)}")
        print(f"  norm_wraps_or_ge_T = {evb(norm_wraps_or_ge_T)}")
        print(f"  norm_base_ge_T    = {evb(norm_base_ge_T)}")
        print(f"  norm_b_masked = {ev(norm_b_masked)}  norm_bsum_masked = {ev(norm_bsum_masked)}")
        print(f"  k      = {u(k)}  (k & 31) = {u(k) & 31}")
        print(f"  x      = {u(x)}  x>>(k&31) = {u(x) >> (u(k) & 31)}")
        print(f"  contains(ci,x)   = {evb(contains(ci_base,ci_size,x))}")
        print(f"  contains(cx,k)   = {evb(contains(cx_base,cx_size,k))}")
        print(f"  const_nc_b = {ev(const_nc_b)}  const_nc_h = {ev(const_nc_h)}")
        print(f"  const_res_b = {ev(const_res_b)}  const_res_s = {ev(const_res_s)}")
        print(f"  lo_nc = {ev(lo_nc)}  hi_nc = {ev(hi_nc)}  hi_nc_raw = {ev(hi_nc_raw)}")
        print(f"  nc_res_b = {ev(nc_res_b)}  nc_res_s = {ev(nc_res_s)}")
        print(f"  cul_res_b = {ev(cul_res_b)}  cul_res_s = {ev(cul_res_s)}")
        print(f"  res       = {{base={ev(res_b)}, size={ev(res_s)}}}")
        print(f"  contains(res, x_shr) = {evb(contains(res_b, res_s, x_shr))}")
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
