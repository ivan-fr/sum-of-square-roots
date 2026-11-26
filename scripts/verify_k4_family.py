"""
Exact rational verification of the explicit k = 4 quadratic family (u = 1600/379,
from w = 11/10 in u = 16 / (5 - w^2)) constructed via four iterated Fermat quartic
steps, proving r(n, 4) = O(n^{-15/2}) directly in exact SymPy rational arithmetic.
"""

import sympy as sp


def disc_2atom(m):
    det = sp.expand(m[1] ** 2 - m[0] * m[2])
    s_num = sp.expand(-m[2] * m[1] + m[3] * m[0])
    p_num = sp.expand(-m[1] * m[3] + m[2] ** 2)
    return s_num, p_num, det, sp.expand(s_num**2 - 4 * p_num * det)


def shift_moments(m, r):
    return [sp.expand(m[i + 1] - r * m[i]) for i in range(len(m) - 1)]


def fermat_step(poly_expr, var):
    p = sp.Poly(poly_expr, var)
    c4, c3, c2, c1, c0 = [sp.Rational(p.nth(i)) for i in [4, 3, 2, 1, 0]]
    assert c4 > 0
    sn, ok1 = sp.integer_nthroot(c4.p, 2)
    sd, ok2 = sp.integer_nthroot(c4.q, 2)
    assert ok1 and ok2
    av = sp.Rational(sn, sd)
    bv = c3 / (2 * av)
    gv = (c2 - bv**2) / (2 * av)
    denom = 2 * bv * gv - c1
    assert denom != 0
    x0 = (c0 - gv**2) / denom
    y0 = abs(av * x0**2 + bv * x0 + gv)
    assert p.eval(x0) == y0**2
    return x0, y0


def main():
    u_val = sp.Rational(1600, 379)  # 16 / (5 - (11/10)^2)
    mu = []
    for m in range(10):
        bm = sp.binomial(sp.Rational(1, 2), m)
        s = sum(
            sp.binomial(sp.Rational(1, 2), m + j)
            * sp.binomial(m + j, 2 * j)
            * (u_val**j)
            for j in range(m + 1)
        )
        mu.append(sp.simplify(2 * s / bm))

    t_var = sp.Symbol("t")
    m_cur = list(mu)
    nodes = []
    for step in range(4):
        m_sh = shift_moments(m_cur, t_var)
        _, _, _, D_poly = disc_2atom(m_sh[:4])
        r_val, _ = fermat_step(D_poly, t_var)
        nodes.append(r_val)
        m_cur = [val.subs(t_var, r_val) for val in m_sh]

    s_n, p_n, det_v, d_n = disc_2atom(m_cur[:4])
    assert det_v != 0 and d_n > 0
    sn, ok1 = sp.integer_nthroot(d_n.p, 2)
    sd, ok2 = sp.integer_nthroot(d_n.q, 2)
    assert ok1 and ok2
    rdisc = sp.Rational(sn, sd) / abs(det_v)
    s_v = s_n / det_v
    t5 = (-s_v - rdisc) / 2
    t6 = (-s_v + rdisc) / 2
    ts = nodes + [t5, t6]
    assert len(set(ts)) == 6

    V = sp.Matrix(6, 6, lambda i, j: ts[j] ** i)
    w = list(V.LUsolve(sp.Matrix(mu[:6])))
    pos = sum(1 for v in w if v > 0)
    neg = sum(1 for v in w if v < 0)
    assert pos == 4 and neg == 2, f"Unexpected signature (+{pos}, -{neg})"

    for m in range(8):
        diff_m = sum(w[j] * (ts[j] ** m) for j in range(6)) - mu[m]
        assert diff_m == 0, f"Moment {m} mismatch!"
    err8 = sum(w[j] * (ts[j] ** 8) for j in range(6)) - mu[8]
    assert err8 != 0

    print(f"u = {u_val} (approx {float(u_val):.6f})")
    print(f"6 distinct rational nodes (bit lengths of numer/denom):")
    for idx, (ti, wi) in enumerate(zip(ts, w), 1):
        print(
            f"  i={idx}: t_i ≈ {float(ti):+12.6f} (bits {ti.p.bit_length()}/{ti.q.bit_length()}), "
            f"w_i ≈ {float(wi):+.4e} ({'+' if wi > 0 else '-'}, bits {wi.p.bit_length()}/{wi.q.bit_length()})"
        )
    print(f"Signature: (+{pos}, -{neg})")
    print(f"Exact moments 0..7 all zero: True")
    print(f"Moment 8 residual ≈ {float(err8):.6e} != 0")
    print("[OK] Explicit k = 4 family verified in exact rational arithmetic: r(n, 4) = O(n^{-15/2})!")


if __name__ == "__main__":
    main()
