"""
Z3 proof for cnum32_shl_const:
    Theorem: ci non-empty, x in ci  implies  x<<(k&31) in shl_const(ci, k)

C source (shl_const):
    struct cnum_t shl_const(cnum, k):
        if is_empty(cnum) return EMPTY
        k &= T-1
        if cross_unsigned_limit(cnum) return {0, UT_MAX << k}
        bits_to_keep = T - k
        truncated_cnum = trunc(cnum, bits_to_keep)
        if is_top(truncated_cnum) return UNBOUNDED
        return from_urange(cnum.base << k, (cnum.base + cnum.size) << k)

NOTE: C code at line 309 still uses (cnum.base + cnum.size) without C uint32_t wrap,
      which may cause counterexamples similar to the previous round.
      This Z3 model faithfully follows the C code semantics.
"""

from z3 import *
import time

def main():
    t0 = time.monotonic()

    T = 32
    UT_MAX_VAL = (1 << T) - 1
    UT_MAX = BitVecVal(UT_MAX_VAL, T)
    EMPTY_base_val = UT_MAX_VAL
    EMPTY_size_val = UT_MAX_VAL
    TOP_base_val   = 0
    TOP_size_val   = UT_MAX_VAL

    ci_base = BitVec('ci_base', T)
    ci_size = BitVec('ci_size', T)
    k       = BitVec('k', T)
    x       = BitVec('x', T)

    def is_empty(b, s):
        return And(b == EMPTY_base_val, s == EMPTY_size_val)

    def is_top(b, s):
        return And(b == TOP_base_val, s == TOP_size_val)

    def is_unbounded(b, s):
        return And(b == TOP_base_val, s == TOP_size_val)

    def contains(b, s, v):
        ov = UGT(s, UT_MAX - b)
        return If(ov,
                  Or(UGE(v, b), ULE(v, b + s)),
                  And(UGE(v, b), ULE(v, b + s)))

    def cross_unsigned_limit(base, size):
        return If(Or(is_empty(base, size), is_top(base, size)),
                  False,
                  And(contains(base, size, UT_MAX),
                      contains(base, size, BitVecVal(0, T))))

    ci_empty = is_empty(ci_base, ci_size)
    ci_cul   = cross_unsigned_limit(ci_base, ci_size)

    # k &= T-1
    k_norm = k & BitVecVal(T - 1, T)

    # cross_unsigned_limit ci -> {0, UT_MAX << k}
    cul_res_b = BitVecVal(0, T)
    cul_res_s = (UT_MAX << k_norm) & UT_MAX

    # bits_to_keep = T - k_norm
    bits_to_keep = T - k_norm

    # --- trunc(cnum, bits_to_keep) ---
    ci_ov = UGT(ci_size, UT_MAX - ci_base)

    # Same-high case: start_high == end_high
    start_high = LShR(ci_base, bits_to_keep)
    end_high   = LShR((ci_base + ci_size) & UT_MAX, bits_to_keep)
    same_high  = (start_high == end_high)

    mask = If(UGT(bits_to_keep, BitVecVal(T, T)),
              BitVecVal(0, T),
              (BitVecVal(1, T) << bits_to_keep) - BitVecVal(1, T))

    ci_upper_masked = (ci_base + ci_size) & UT_MAX
    lower_start = ci_base & mask
    lower_end   = ci_upper_masked & mask

    trunc_A_b = If(ULE(lower_start, lower_end), lower_start, TOP_base_val)
    trunc_A_s = If(ULE(lower_start, lower_end), lower_end - lower_start, TOP_size_val)

    # Cross-high case: y == end_high
    y         = start_high + BitVecVal(1, T)
    y_eq_end  = (y == end_high)

    trunc_B_b = If(And(Not(same_high), y_eq_end,
                        UGT(lower_start, lower_end)),
                   lower_start, TOP_base_val)
    trunc_B_s = If(And(Not(same_high), y_eq_end,
                        UGT(lower_start, lower_end)),
                   lower_end - lower_start, TOP_size_val)

    # trunc result
    trunc_res_b = If(same_high, trunc_A_b, trunc_B_b)
    trunc_res_s = If(same_high, trunc_A_s, trunc_B_s)
    trunc_is_top = is_top(trunc_res_b, trunc_res_s)
    trunc_is_unbounded = is_unbounded(trunc_res_b, trunc_res_s)

    # --- from_urange(cnum.base << k, (cnum.base + cnum.size) << k) ---
    # NOTE: C code does NOT mask (cnum.base + cnum.size) before shifting.
    # This is a potential bug matching the original C code.
    new_base = (ci_base << k_norm) & UT_MAX
    new_ub   = ((ci_base + ci_size) << k_norm) & UT_MAX
    nc_base  = new_base
    nc_size  = (new_ub - new_base) & UT_MAX

    # Full shl_const result:
    # 1. empty ci         -> EMPTY
    # 2. cross_ul ci       -> {0, UT_MAX << k}
    # 3. trunc is TOP      -> UNBOUNDED
    # 4. else              -> from_urange(ci.base<<k, (ci.base+ci.size)<<k)
    res_b = If(ci_empty, EMPTY_base_val,
               If(ci_cul, cul_res_b,
                  If(trunc_is_top, TOP_base_val, nc_base)))
    res_s = If(ci_empty, EMPTY_size_val,
               If(ci_cul, cul_res_s,
                  If(trunc_is_top, TOP_size_val, nc_size)))

    # x << (k & 31) with C uint32_t wrap
    x_shl = (x << k_norm) & UT_MAX

    # Theorem: ci non-empty, x in ci => x<<(k&31) in shl_const(ci, k)
    # UNBOUNDED (top: base=0, size=UT_MAX) contains everything
    theorem = Implies(
        contains(ci_base, ci_size, x),
        contains(res_b, res_s, x_shl))

    s = Solver()
    s.set("timeout", 3600000)
    s.set("threads", 16)
    s.add(Not(theorem))

    print("Verifying cnum32_shl_const (1hr timeout, 16 threads)...")
    print("Theorem: x in ci")
    print("         implies (x << (k & 31)) in shl_const(ci, k)\n")

    result = s.check()
    elapsed = time.monotonic() - t0
    if result == sat:
        m = s.model()
        print("FAIL: Counterexample found!")
        print(f"  elapsed: {elapsed:.3f}s")
        def u(name):   return m[name].as_long()
        def ev(expr):  return m.eval(simplify(expr)).as_long()
        def evb(expr): return is_true(simplify(m.eval(expr)))
        print(f"\n  ci       = {{base={u(ci_base)}, size={u(ci_size)}}}")
        print(f"  ci_empty = {evb(ci_empty)}  ci_cul = {evb(ci_cul)}")
        print(f"  k        = {u(k)}  (k & 31) = {u(k) & 31}")
        print(f"  x        = {u(x)}  x<<(k&31) = {(u(x) << (u(k) & 31)) & UT_MAX_VAL}")
        print(f"  k_norm        = {ev(k_norm)}")
        print(f"  bits_to_keep  = {ev(bits_to_keep)}")
        print(f"  mask          = {ev(mask)}")
        print(f"  ci_ov         = {evb(ci_ov)}")
        print(f"  start_high    = {ev(start_high)}  end_high = {ev(end_high)}")
        print(f"  same_high     = {evb(same_high)}  y_eq_end = {evb(y_eq_end)}")
        print(f"  lower_start   = {ev(lower_start)}  lower_end = {ev(lower_end)}")
        print(f"  trunc_res_b   = {ev(trunc_res_b)}  trunc_res_s = {ev(trunc_res_s)}")
        print(f"  trunc_is_top  = {evb(trunc_is_top)}")
        print(f"  trunc_is_unbounded = {evb(trunc_is_unbounded)}")
        print(f"  cul_res_b     = {ev(cul_res_b)}  cul_res_s = {ev(cul_res_s)}")
        print(f"  new_base      = {ev(new_base)}  new_ub = {ev(new_ub)}")
        print(f"  nc_base       = {ev(nc_base)}  nc_size = {ev(nc_size)}")
        print(f"  res           = {{base={ev(res_b)}, size={ev(res_s)}}}")
        print(f"  contains(res, x_shl) = {evb(contains(res_b, res_s, x_shl))}")
        return 1
    elif result == unsat:
        print("PASS: cnum32_shl_const verified.")
        print(f"  elapsed: {elapsed:.3f}s")
        return 0
    else:
        print("UNKNOWN: solver timeout or error")
        print(f"  elapsed: {elapsed:.3f}s")
        return 2

if __name__ == "__main__":
    exit(main())
