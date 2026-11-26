# Breaking the Linear-Ansatz Barrier for the Sum-of-Square-Roots Problem

**Author:** Ivan Besevic (ESIEE-IT, France; ORCID `0009-0004-4124-1465`)

This repository contains the arXiv-ready paper, machine-checked Lean 4.36.0 formalization, and exact symbolic/high-precision verification scripts establishing:

1. **All-$k$ Constructive Upper Bound (Theorem 1.2):** For every integer $k \ge 2$,
   $$r(n, k) = O\!\left(n^{-2k + 1/2}\right),$$
   improving the 20-year constructive upper bound $r(n, k) = O(n^{-2k + 3/2})$ of Qian & Wang (*Information Processing Letters*, 2006) by a full factor of $n$ for every $k \ge 2$.
2. **Explicit Polynomial Families for $k = 2, 3, 4$:**
   - $k = 2$ ($u = -4$): constant algebraic norm $M \equiv 82944$, $\Delta_2(m) = -\frac{3}{2} m^{-7} - 15 m^{-9} + O(m^{-11})$.
   - $k = 3$ ($u = 5$): explicit tiny-integer family achieving $\Delta_3(m) = -\frac{730468750000}{7} m^{-11} + O(m^{-13}) = \Theta(n^{-11/2})$.
   - $k = 4$ ($u = 1600/379$): explicit rational family via four iterated Fermat quartic steps achieving $r(n, 4) = O(n^{-15/2})$.
3. **Sharp Effective Lower Bounds for $k = 2$ (Theorem 1.4):**
   - $r(n, 2) \ge \frac{1}{4} n^{-7/2}$ for every $n \ge 1$ ($4096\times$ sharper than Burnikel–Fleischer–Mehlhorn–Schirra 2000), and asymptotic floor $\bigl(\frac{8}{27} - O(n^{-4})\bigr) n^{-7/2}$ ($4854\times$ sharper than BFMS).
4. **7-Moment Diophantine Barrier for $k = 3$ ($O(n^{-13/2})$):** Exact shifted-coordinate collapse $E_3 = E_4 = 0$, hyperbolic $(+3, -1)$ window $v \in (\frac{97}{420}, \frac{1}{4})$, $42 \mid \operatorname{lcm}(\operatorname{denom}(y_i))$, and modular sieving over $85\,425\,298$ rational candidates (zero non-trivial hits).

## Repository Layout

- `paper/sum_of_square_roots.tex` & `paper/sum_of_square_roots.pdf`: Complete arXiv-ready manuscript.
- `lean/`: Lean 4.36.0 + Mathlib formalization (`SumOfSquareRoots`):
  - `SumOfSquareRoots/Basic.lean`: `diff2`, `diff3`, `T6`, and elementary polynomial-squaring enclosure `sqrt_one_add_approx`.
  - `SumOfSquareRoots/K2Bounds.lean`: `k2_norm_identity`, `k2_exact_constant_bound`, `k2_lower_bound`, `k2_upper_bound_family`, `k2_upper_bound`.
  - `SumOfSquareRoots/K3UpperBound.lean`: `Qpair`, `k3_exact_moment_cancellation`, `k3_pair_approx`, `k3_upper_bound_family`, `k3_upper_bound`.
  - `check_axioms.lean`: Axiom audit confirming zero `sorry`, zero `native_decide`, and strictly `[propext, Classical.choice, Quot.sound]`.
- `scripts/verify_general_k.py`: Exact SymPy verification of all universal lemmas + 250-digit inductive dipole chain ($k = 2 \dots 8$).
- `scripts/verify_k4_family.py`: Exact SymPy rational verification of the explicit $k = 4$ family ($u = 1600/379$).

## Reproduction

```bash
# 1. Verify Lean 4.36.0 formalization and axiom audit
cd lean && lake build && lake env lean check_axioms.lean

# 2. Run exact symbolic & 250-digit verification scripts (requires sympy, mpmath)
python3 scripts/verify_general_k.py
python3 scripts/verify_k4_family.py

# 3. Compile manuscript
cd paper && tectonic sum_of_square_roots.tex
```
