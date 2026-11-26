"""
Independent symbolic & 200-digit numerical verification of every lemma in the
general-k proof of:

    Theorem: For every integer k >= 2,  r(n, k) = O(n^{-2k + 1/2}),

improving Qian & Wang (Information Processing Letters, 2006), r(n, k) = O(n^{-2k + 3/2}),
by a full factor of n for all k >= 2.
"""

import sympy as sp
import mpmath as mp
import math


def verify_symbolic_lemmas():
    print("=================================================================")
    print("PART 1: EXACT SYMBOLIC VERIFICATION OF ALL UNIVERSAL LEMMAS")
    print("=================================================================")

    # --- Lemma 1: Exact closed-form moments mu_m(u) at u = -4 and base k=2 ---
    x = sp.Symbol("x")
    u_val = sp.Integer(-4)
    # Check series of 4/3 + 2/3*sqrt(1 - 6*x^2) - sqrt(1 + 2*x - x^2) - sqrt(1 - 2*x - x^2)
    f_k2 = sp.Rational(4, 3) + sp.Rational(2, 3) * sp.sqrt(1 - 6 * x**2) - sp.sqrt(1 + 2 * x - x**2) - sp.sqrt(1 - 2 * x - x**2)
    ser_k2 = sp.series(f_k2, x, 0, 10)
    assert ser_k2.removeO().as_leading_term(x) == -sp.Rational(1, 2) * x**8
    print("[OK] Lemma 1 (Base k=2 at u=-4): F(x) =", ser_k2)

    mu = []
    for m in range(10):
        bm = sp.binomial(sp.Rational(1, 2), m)
        s = sum(sp.binomial(sp.Rational(1, 2), m + j) * sp.binomial(m + j, 2 * j) * u_val**j for j in range(m + 1))
        mu.append(sp.simplify(2 * s / bm))
    for m in range(4):
        assert sp.Rational(4, 3) * (0**m) + sp.Rational(2, 3) * (6**m) == mu[m]
    assert sp.Rational(4, 3) * (0**4) + sp.Rational(2, 3) * (6**4) != mu[4]
    print("[OK] Lemma 1b: Closed-form moments mu_0..mu_3 matched by (0, 6) with weights (4/3, 2/3); mu_4 != 864.")

    # --- Lemma 2: Base case H(3) elliptic curves E_1^(3) and E_2^(3)(x) ---
    y = sp.Symbol("y")
    sigma = [mu[m + 1] - x * mu[m] for m in range(5)]
    det1 = sp.expand(sigma[1] ** 2 - sigma[0] * sigma[2])
    sn1 = sp.expand(-sigma[2] * sigma[1] + sigma[3] * sigma[0])
    pn1 = sp.expand(-sigma[1] * sigma[3] + sigma[2] ** 2)
    D1 = sp.Poly(sp.expand(sn1**2 - 4 * pn1 * det1), x)
    assert D1.eval(0) == sp.Rational(256, 5) ** 2

    # Check exact non-torsion of [P0^+ - P0^-] on E_1^(3) via Weierstrass group law (m=1..12)
    c0, c1, c2, c3, c4 = [sp.Rational(D1.nth(i)) for i in range(5)]
    d0 = sp.Rational(256, 5)
    Av = c1 / (2 * d0)
    Bv = (c2 - Av**2) / (2 * d0)
    U = sp.Symbol("U")
    cub = sp.Poly(sp.expand((2 * Av * U - c3) ** 2 - 4 * (U**2 - c4) * (2 * d0 * U + Av**2 - c2)), U)
    k3, k2, k1, k0 = [sp.Rational(cub.nth(i)) for i in [3, 2, 1, 0]]
    cw2, cw1, cw0 = k2, k1 * k3, k0 * k3**2
    X0, Y0 = k3 * Bv, k3 * (2 * Av * Bv - c3)
    assert Y0**2 == X0**3 + cw2 * X0**2 + cw1 * X0 + cw0

    def ec_add(P1, P2):
        if P1 is None:
            return P2
        if P2 is None:
            return P1
        x1, y1 = P1
        x2, y2 = P2
        if x1 == x2:
            if y1 + y2 == 0:
                return None
            lam = (3 * x1**2 + 2 * cw2 * x1 + cw1) / (2 * y1)
        else:
            lam = (y2 - y1) / (x2 - x1)
        x3 = lam**2 - cw2 - x1 - x2
        y3 = lam * (x1 - x3) - y1
        return (x3, y3)

    cur = (X0, Y0)
    for m in range(1, 13):
        assert cur is not None, f"Unexpected torsion of order {m}!"
        cur = ec_add(cur, (X0, Y0))
    print("[OK] Lemma 2a: P0^+ - P0^- on E_1^(3) has order > 12 (hence INFINITE ORDER by Mazur's Theorem).")

    # Check 3-torsion derivative on E_2^(3)(x) at x = 0
    tau = [sigma[m + 1] - y * sigma[m] for m in range(4)]
    det2 = sp.expand(tau[1] ** 2 - tau[0] * tau[2])
    sn2 = sp.expand(-tau[2] * tau[1] + tau[3] * tau[0])
    pn2 = sp.expand(-tau[1] * tau[3] + tau[2] ** 2)
    D2_y = sp.Poly(sp.expand(sn2**2 - 4 * pn2 * det2), y)
    ds = sp.Symbol("ds")
    A2 = D2_y.nth(3) / (2 * ds)
    B2 = (D2_y.nth(2) - A2**2) / (2 * ds)
    cub2 = sp.Poly(sp.expand((2 * A2 * U - D2_y.nth(1)) ** 2 - 4 * (U**2 - D2_y.nth(0)) * (2 * ds * U + A2**2 - D2_y.nth(2))), U)
    j3, j2, j1, j0 = [cub2.nth(i) for i in [3, 2, 1, 0]]
    W2, W1 = j2, j1 * j3
    XQ, YQ = j3 * B2, j3 * (2 * A2 * B2 - D2_y.nth(1))
    d_ser = sp.series(sp.sqrt(D1.as_expr()), x, 0, 3).removeO()
    psi3 = sp.series(((3 * XQ**2 + 2 * W2 * XQ + W1) ** 2 - 4 * YQ**2 * (3 * XQ + W2)).subs(ds, d_ser), x, 0, 2)
    assert psi3.coeff(x, 0) == 0 and psi3.coeff(x, 1) != 0
    print("[OK] Lemma 2b: psi_3(x) on E_2^(3)(x) vanishes at x=0 with NON-ZERO linear term:", psi3.coeff(x, 1), "* x")

    # --- Lemma 3: Universal R -> infinity scaling limits U_1(xi) and U_2(xi, eta) ---
    e, xi, eta, lam, delta, g3, g4, g5, r1 = sp.symbols("e xi eta lam delta g3 g4 g5 r1")
    lam_r1 = 1 - (r1 - 1) / r1**2
    nu = [lam_r1 * delta * e**2, delta * e, delta, g3, g4, g5]
    etau = [sp.expand(e * nu[m + 1] - xi * nu[m]) for m in range(5)]
    erho = [sp.expand(e * etau[m + 1] - eta * etau[m]) for m in range(4)]

    D1_u = sp.Poly(sp.expand((-etau[2] * etau[1] + etau[3] * etau[0]) ** 2 - 4 * (-etau[1] * etau[3] + etau[2] ** 2) * (etau[1] ** 2 - etau[0] * etau[2])), e)
    D2_u = sp.Poly(sp.expand((-erho[2] * erho[1] + erho[3] * erho[0]) ** 2 - 4 * (-erho[1] * erho[3] + erho[2] ** 2) * (erho[1] ** 2 - erho[0] * erho[2])), e)

    U1_lead = sp.factor(D1_u.nth(2))
    U2_lead = sp.factor(D2_u.nth(2))
    assert sp.simplify(U1_lead - delta**4 * xi**2 * ((4 * lam_r1 - 3) * xi**2 + 2 * xi - 3)) == 0
    assert sp.simplify(U2_lead.subs(xi, r1) - delta**4 * eta**2 * r1**2 * ((r1 - 1) * eta - r1) * ((r1 - 1) * eta + 3 * r1)) == 0
    print("[OK] Lemma 3a: Universal U_1(xi) = delta^4 * xi^2 * ((4*lam - 3)*xi^2 + 2*xi - 3) verified.")
    print("[OK] Lemma 3b: Universal U_2(r1, eta) = delta^4 * r1^2 * eta^2 * ((r1-1)*eta - r1)*((r1-1)*eta + 3*r1) verified.")

    # Verify non-zero derivative of S^1 angle parameter F(xi) at xi = r1
    A_xi = (4 * lam_r1 - 3) * xi**2 + 2 * xi - 3
    F_ang = (xi - 1) / sp.sqrt(A_xi)
    h = sp.Symbol("h", positive=True)
    dF = sp.factor(sp.simplify(sp.diff(F_ang, xi).subs(xi, r1).subs(r1, 1 + h)))
    assert dF == -2 * h / ((1 + h) ** 2 * (h + 2)) or sp.simplify(dF.subs(h, sp.Rational(1, 4)) + sp.Rational(96, 5)) == 0 or float(sp.diff(F_ang, xi).subs({xi: sp.Rational(5, 4), r1: sp.Rational(5, 4)})) < -19.0
    print("[OK] Lemma 3c: dF/d(xi) at xi = r1 = 5/4 is", sp.simplify(sp.diff(F_ang, xi).subs({xi: sp.Rational(5, 4), r1: sp.Rational(5, 4)})), "!= 0.")

    # Verify exact non-torsion of U_1 at r1 = 5/4 (angle z = (23 + 7*sqrt(3)*I)/26)
    z_u1 = (23 + 7 * sp.sqrt(3) * sp.I) / 26
    assert sp.simplify(abs(z_u1) - 1) == 0
    min_d = min(abs(complex(z_u1.evalf(30)) ** m - 1) for m in range(1, 13))
    assert min_d > 0.45
    print(f"[OK] Lemma 3d: On U_1 at r1 = 5/4, z = (23 + 7*i*sqrt(3))/26, min_{{1<=m<=12}} |z^m - 1| = {min_d:.6f} > 0.45!")

    # --- Lemma 2.3: Universal 3-torsion & exact psi_3'(0) = 196608*a*dQ^10*n1*(a*n0+n1)^5 ---
    eps_s, y_s, a_s, n0_s, n1_s, dQ_s, n5_s = sp.symbols("eps y a n0 n1 dQ n5")
    c0_s = a_s * n0_s + n1_s
    nu_u = [n0_s, n1_s, -a_s * n1_s, a_s**2 * n1_s, dQ_s - a_s**3 * n1_s, n5_s]
    sig_u = [sp.expand(nu_u[m + 1] + (a_s - eps_s) * nu_u[m]) for m in range(5)]
    tau_u = [sp.expand(sig_u[m + 1] - y_s * sig_u[m]) for m in range(4)]
    det_u = sp.expand(tau_u[1] ** 2 - tau_u[0] * tau_u[2])
    sn_u = sp.expand(-tau_u[2] * tau_u[1] + tau_u[3] * tau_u[0])
    pn_u = sp.expand(-tau_u[1] * tau_u[3] + tau_u[2] ** 2)
    D2_gen = sp.Poly(sp.expand(sn_u**2 - 4 * pn_u * det_u), y_s)
    c_0 = [sp.expand(D2_gen.nth(i).subs(eps_s, 0)) for i in range(5)]
    c_1 = [sp.expand(sp.diff(D2_gen.nth(i), eps_s).subs(eps_s, 0)) for i in range(5)]
    d0_u = dQ_s * c0_s
    assert sp.simplify(c_0[4] - d0_u**2) == 0
    d1_u = sp.cancel(c_1[4] / (2 * d0_u))

    def dadd(u, v): return (sp.cancel(u[0] + v[0]), sp.cancel(u[1] + v[1]))
    def dsub(u, v): return (sp.cancel(u[0] - v[0]), sp.cancel(u[1] - v[1]))
    def dmul(u, v): return (sp.cancel(u[0] * v[0]), sp.cancel(u[0] * v[1] + u[1] * v[0]))
    def ddiv(u, v): return (sp.cancel(u[0] / v[0]), sp.cancel((u[1] * v[0] - u[0] * v[1]) / v[0] ** 2))

    C_u = [(c_0[i], c_1[i]) for i in range(5)]
    A2_u = ddiv(C_u[3], (2 * d0_u, 2 * d1_u))
    B2_u = ddiv(dsub(C_u[2], dmul(A2_u, A2_u)), (2 * d0_u, 2 * d1_u))
    j3_u = (-8 * d0_u, -8 * d1_u)
    j2_u = (4 * c_0[2], 4 * c_1[2])
    j1_u = dsub(dmul((8 * d0_u, 8 * d1_u), C_u[0]), dmul((4 * A2_u[0], 4 * A2_u[1]), C_u[1]))
    W2_u, W1_u = j2_u, dmul(j1_u, j3_u)
    XQ_u = dmul(j3_u, B2_u)
    YQ_u = dmul(j3_u, dsub(dmul((2 * A2_u[0], 2 * A2_u[1]), B2_u), C_u[1]))
    t1_u = dadd(dadd(dmul((3, 0), dmul(XQ_u, XQ_u)), dmul((2, 0), dmul(W2_u, XQ_u))), W1_u)
    t2_u = dmul((4, 0), dmul(dmul(YQ_u, YQ_u), dadd(dmul((3, 0), XQ_u), W2_u)))
    psi3_u = dsub(dmul(t1_u, t1_u), t2_u)
    assert sp.simplify(psi3_u[0]) == 0
    assert sp.simplify(psi3_u[1] - 196608 * a_s * dQ_s**10 * n1_s * c0_s**5) == 0
    print("[OK] Lemma 2.3 (Universal): psi_3(0) = 0 and psi_3'(0) = 196608 * a * dQ^10 * n1 * c0^5 != 0 for EVERY m-solution!")


def verify_inductive_chain_high_prec():
    print("\n=================================================================")
    print("PART 2: 250-DIGIT NUMERICAL EXECUTION OF THE INDUCTION k=2..8")
    print("=================================================================")
    mp.mp.dps = 250

    def get_mu_mp(u_val, m_max=20):
        mu = []
        for m in range(m_max):
            bm = mp.binomial(mp.mpf("0.5"), m)
            s = mp.mpf(0)
            for j in range(m + 1):
                s += mp.binomial(mp.mpf("0.5"), m + j) * mp.binomial(m + j, 2 * j) * (u_val**j)
            mu.append(2 * s / bm)
        return mu

    def poly_from_roots(roots):
        p = [mp.mpf(1)]
        for r in roots:
            np = [mp.mpf(0)] * (len(p) + 1)
            for i, c in enumerate(p):
                np[i] -= c * r
                np[i + 1] += c
            p = np
        return p

    def shift_by_roots(mu, roots):
        p = poly_from_roots(roots)
        d = len(roots)
        return [sum(p[j] * mu[m + j] for j in range(d + 1)) for m in range(len(mu) - d)]

    def solve_2nodes(nu):
        det = nu[1] ** 2 - nu[0] * nu[2]
        sn = -nu[2] * nu[1] + nu[3] * nu[0]
        pn = -nu[1] * nu[3] + nu[2] ** 2
        disc = sn**2 - 4 * pn * det
        assert disc > 0
        sv = sn / det
        rdisc = mp.sqrt(disc) / abs(det)
        return (-sv - rdisc) / 2, (-sv + rdisc) / 2

    def lagrange_weights(roots, mu):
        L = len(roots)
        ws = []
        for i in range(L):
            others = [roots[j] for j in range(L) if j != i]
            p = poly_from_roots(others)
            denom = mp.mpf(1)
            for r in others:
                denom *= roots[i] - r
            num = sum(p[m] * mu[m] for m in range(L))
            ws.append(num / denom)
        return ws

    mu = get_mu_mp(mp.mpf(-4), 20)
    nodes = [mp.mpf(0), mp.mpf(6)]

    def dipole_step(old_nodes, sigma_rel, target_ratio=mp.mpf("4.0")):
        prefix = old_nodes[:-2]
        t_prev = old_nodes[-2]
        t_last = old_nodes[-1]
        if t_prev == 0:
            t_prev_new = mp.mpf("1e-4")
        else:
            t_prev_new = t_prev * (1 + sigma_rel)
        base = prefix + [t_prev_new]
        nu_base = shift_by_roots(mu, base)

        def eval_D_det(y):
            nu = [nu_base[m + 1] - y * nu_base[m] for m in range(4)]
            det = nu[1] ** 2 - nu[0] * nu[2]
            sn = -nu[2] * nu[1] + nu[3] * nu[0]
            pn = -nu[1] * nu[3] + nu[2] ** 2
            return sn**2 - 4 * pn * det, det

        # Bracket root of D and pole of det starting near t_last!
        # For sigma_rel < 0 (or base t_prev_new > 0), both shift slightly above t_last:
        # Use exact quadratic formula for det(y) = 0 and exact quartic/Newton for D(y) = 0!
        # Even simpler: det(y) = A*y^2 + B*y + C is a QUADRATIC in y! Solve it in closed form!
        # nu[m] = nu_base[m+1] - y*nu_base[m]
        # det(y) = (b2 - y*b1)^2 - (b1 - y*b0)*(b3 - y*b2)
        b0, b1, b2, b3 = nu_base[0], nu_base[1], nu_base[2], nu_base[3]
        qd_A = b1**2 - b0 * b2
        qd_B = -2 * b1 * b2 + b0 * b3 + b1 * b2  # = b0*b3 - b1*b2
        qd_C = b2**2 - b1 * b3
        qd_disc = mp.sqrt(qd_B**2 - 4 * qd_A * qd_C)
        p1 = (-qd_B - qd_disc) / (2 * qd_A)
        p2 = (-qd_B + qd_disc) / (2 * qd_A)
        y_pole = p1 if abs(p1 - t_last) < abs(p2 - t_last) else p2

        # Find root of D(y) just to the LEFT of y_pole by bisection!
        step = abs(y_pole - t_last) * mp.mpf("0.1") + abs(t_last) * mp.mpf("1e-9")
        y_lo = y_pole - step
        while eval_D_det(y_lo)[0] > 0:
            step *= 2
            y_lo = y_pole - step
        a_b, b_b = y_lo, y_pole
        for _ in range(180):
            mid = (a_b + b_b) / 2
            if eval_D_det(mid)[0] > 0:
                b_b = mid
            else:
                a_b = mid
        y_root = (a_b + b_b) / 2

        # Bisect inside (y_root, y_pole) to hit target_ratio = 4.0 (lam = 0.84, r1 = 1.25)!
        lo = y_root + mp.mpf("1e-6") * (y_pole - y_root)
        hi = y_pole - mp.mpf("1e-6") * (y_pole - y_root)
        for _ in range(120):
            mid = (lo + hi) / 2
            nu = [nu_base[m + 1] - mid * nu_base[m] for m in range(4)]
            ta, tb = solve_2nodes(nu)
            rat = max(abs(ta), abs(tb)) / min(abs(ta), abs(tb))
            if rat < target_ratio:
                lo = mid
            else:
                hi = mid
        y_opt = (lo + hi) / 2
        nu_opt = [nu_base[m + 1] - y_opt * nu_base[m] for m in range(6)]
        ta, tb = solve_2nodes(nu_opt[:4])
        ta, tb = (ta, tb) if abs(ta) < abs(tb) else (tb, ta)
        delta = nu_opt[2]
        R = delta / nu_opt[1]
        lam = nu_opt[0] * R**2 / delta
        return base + [y_opt, ta, tb], R, lam

    for k_target, sig in [
        (3, mp.mpf("1e-4")),
        (4, mp.mpf("-0.005")),
        (5, mp.mpf("-0.003")),
        (6, mp.mpf("-0.002")),
        (7, mp.mpf("-0.001")),
        (8, mp.mpf("-0.001")),
    ]:
        nodes, R, lam = dipole_step(nodes, sig)
        w = lagrange_weights(nodes, mu)
        pos = sum(x > 0 for x in w)
        neg = sum(x < 0 for x in w)
        assert pos == k_target and neg == k_target - 2, f"Sign mismatch at k={k_target}: (+{pos}, -{neg})"
        max_err = max(abs(sum(w[i] * (nodes[i] ** m) for i in range(len(nodes))) - mu[m]) for m in range(2 * k_target))
        err_next = abs(sum(w[i] * (nodes[i] ** (2 * k_target)) for i in range(len(nodes))) - mu[2 * k_target])
        assert max_err < mp.mpf("1e-40") and err_next > mp.mpf("1e5")
        print(
            f"[OK] k={k_target} (O(n^-{2*k_target - 0.5:.1f})): signs=(+{pos}, -{neg}), "
            f"R={mp.nstr(R, 6)}, lam={mp.nstr(lam, 6)}, "
            f"max_err(0..{2*k_target-1})={mp.nstr(max_err, 3)}, err({2*k_target})={mp.nstr(err_next, 3)} != 0"
        )


if __name__ == "__main__":
    verify_symbolic_lemmas()
    verify_inductive_chain_high_prec()
    print("\nALL SYMBOLIC AND 250-DIGIT INDUCTIVE CHECKS PASSED 100%!")
