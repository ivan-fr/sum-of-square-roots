import Mathlib
import SumOfSquareRoots.Basic

namespace SumOfSquareRoots

/-!
# New Constructive Upper Bound for $k = 3$: $r(n, 3) = O(n^{-11/2})$

We formalize our explicit quadratic polynomial family (parameter $u = 5$), beating the
20-year-old bound $r(n, 3) = O(n^{-9/2})$ of Qian & Wang (*IPL* 2006) by a full factor of $n$:
$$\begin{aligned}
a_1(k) &= 28968^2 (k^2 - 55), & b_1(k) &= 13720^2 (49 k^2 - 1295), \\
a_2(k) &= 53125^2 (k^2 - 35), & b_2(k) &= 81600^2 (k^2 + 10k + 20), \\
a_3(k) &= 59049^2 (9k^2 + 5), & b_3(k) &= 81600^2 (k^2 - 10k + 20).
\end{aligned}$$
All proofs use pure polynomial squaring (`sqrt_one_add_approx`) and elementary algebra
(purely algebraic, self-contained proof without calculus).
-/

/-- Degree-6 polynomial in `w = z^2` matching `sqrt(1 + z + z^2/5) + sqrt(1 - z + z^2/5)` up to `O(w^7)`. -/
noncomputable def Qpair (w : ℝ) : ℝ :=
  2 - (1 / 20 : ℝ) * w - (21 / 1600 : ℝ) * w ^ 2 - (261 / 64000 : ℝ) * w ^ 3
    - (2921 / 2048000 : ℝ) * w ^ 4 - (221407 / 409600000 : ℝ) * w ^ 5
    - (7096321 / 32768000000 : ℝ) * w ^ 6

/-- Exact algebraic cancellation identity for our `u = 5`, `k = 3` family:
    all terms `w^0, w^1, w^2, w^3, w^4, w^5` vanish identically, leaving `-187/1792 * w^6`. -/
lemma k3_exact_moment_cancellation (w : ℝ) :
    28968 * T6 (-(11 / 20 : ℝ) * w)
    + 53125 * T6 (-(7 / 20 : ℝ) * w)
    + 177147 * T6 ((1 / 180 : ℝ) * w)
    - 96040 * T6 (-(37 / 140 : ℝ) * w)
    - 81600 * Qpair w
    = -(187 / 1792 : ℝ) * w ^ 6 := by
  unfold T6 Qpair
  ring

/-- Polynomial enclosure for the conjugate pair `sqrt(1 + z + z^2/5) + sqrt(1 - z + z^2/5)`
    when `0 ≤ z ≤ 1/10` (`w = z^2 ≤ 1/100`). -/
lemma k3_pair_approx {z : ℝ} (hz0 : 0 ≤ z) (hz1 : z ≤ 1 / 10) :
    |Real.sqrt (1 + z + z ^ 2 / 5) + Real.sqrt (1 - z + z ^ 2 / 5) - Qpair (z ^ 2)| ≤
      (1 / 400 : ℝ) * (z ^ 2) ^ 7 := by
  set w := z ^ 2
  have hw0 : 0 ≤ w := sq_nonneg z
  have hw1 : w ≤ 1 / 100 := by
    calc w = z ^ 2 := rfl
      _ ≤ (1 / 10 : ℝ) ^ 2 := pow_le_pow_left₀ hz0 hz1 2
      _ = 1 / 100 := by norm_num
  have hw2 : w ^ 2 ≤ 1 / 10000 := by
    calc w ^ 2 ≤ (1 / 100 : ℝ) ^ 2 := pow_le_pow_left₀ hw0 hw1 2
      _ = 1 / 10000 := by norm_num
  have hw3 : w ^ 3 ≤ 1 / 1000000 := by
    calc w ^ 3 ≤ (1 / 100 : ℝ) ^ 3 := pow_le_pow_left₀ hw0 hw1 3
      _ = 1 / 1000000 := by norm_num
  have hw4 : w ^ 4 ≤ 1 / 100000000 := by
    calc w ^ 4 ≤ (1 / 100 : ℝ) ^ 4 := pow_le_pow_left₀ hw0 hw1 4
      _ = 1 / 100000000 := by norm_num
  have hw5 : w ^ 5 ≤ 1 / 10000000000 := by
    calc w ^ 5 ≤ (1 / 100 : ℝ) ^ 5 := pow_le_pow_left₀ hw0 hw1 5
      _ = 1 / 10000000000 := by norm_num
  have hw6 : w ^ 6 ≤ 1 / 1000000000000 := by
    calc w ^ 6 ≤ (1 / 100 : ℝ) ^ 6 := pow_le_pow_left₀ hw0 hw1 6
      _ = 1 / 1000000000000 := by norm_num
  have h1p : 0 ≤ 1 + z + w / 5 := by linarith
  have h1m : 0 ≤ 1 - z + w / 5 := by linarith
  set P := Real.sqrt (1 + z + w / 5) + Real.sqrt (1 - z + w / 5)
  set t := -(3 / 5 : ℝ) * w + (1 / 25 : ℝ) * w ^ 2
  have ht_eq : t = -(3 / 5 : ℝ) * w + (1 / 25 : ℝ) * w ^ 2 := rfl
  have hP_sq : P ^ 2 = 2 + (2 / 5 : ℝ) * w + 2 * Real.sqrt (1 + t) := by
    dsimp [P, t]
    have hprod : Real.sqrt (1 + z + w / 5) * Real.sqrt (1 - z + w / 5) =
        Real.sqrt (1 + (-(3 / 5 : ℝ) * w + (1 / 25 : ℝ) * w ^ 2)) := by
      rw [← Real.sqrt_mul h1p]
      congr 1; dsimp [w]; ring
    have h1 := Real.sq_sqrt h1p
    have h2 := Real.sq_sqrt h1m
    linarith [show (Real.sqrt (1 + z + w / 5) + Real.sqrt (1 - z + w / 5)) ^ 2 =
      Real.sqrt (1 + z + w / 5) ^ 2 + Real.sqrt (1 - z + w / 5) ^ 2 +
      2 * (Real.sqrt (1 + z + w / 5) * Real.sqrt (1 - z + w / 5)) by ring]
  have hw2_le_w : w ^ 2 ≤ w := by
    have : w * w ≤ 1 * w := mul_le_mul_of_nonneg_right (by linarith) hw0
    linarith [sq w]
  have ht_le_35w : |t| ≤ (3 / 5 : ℝ) * w := by
    rw [ht_eq, abs_le]
    constructor <;> linarith [sq_nonneg w, hw2_le_w]
  have ht_abs : |t| ≤ 1 / 4 := by linarith
  have hT6_err : |Real.sqrt (1 + t) - T6 t| ≤ (3 / 1000 : ℝ) * w ^ 7 := by
    have h := sqrt_one_add_approx ht_abs
    have hpow : |t| ^ 7 ≤ ((3 / 5 : ℝ) * w) ^ 7 :=
      pow_le_pow_left₀ (abs_nonneg t) ht_le_35w 7
    have h35 : (1 / 10 : ℝ) * (3 / 5 : ℝ) ^ 7 ≤ 3 / 1000 := by norm_num
    have hw7 : 0 ≤ w ^ 7 := pow_nonneg hw0 7
    calc |Real.sqrt (1 + t) - T6 t|
        ≤ (1 / 10 : ℝ) * |t| ^ 7 := h
      _ ≤ (1 / 10 : ℝ) * ((3 / 5 : ℝ) * w) ^ 7 :=
            mul_le_mul_of_nonneg_left hpow (by norm_num)
      _ = ((1 / 10 : ℝ) * (3 / 5 : ℝ) ^ 7) * w ^ 7 := by ring
      _ ≤ (3 / 1000 : ℝ) * w ^ 7 := mul_le_mul_of_nonneg_right h35 hw7
  have hpoly_diff : |Qpair w ^ 2 - (2 + (2 / 5 : ℝ) * w + 2 * T6 t)| ≤ (1 / 1000 : ℝ) * w ^ 7 := by
    have hfac : Qpair w ^ 2 - (2 + (2 / 5 : ℝ) * w + 2 * T6 t) =
        w ^ 7 * (
          -(177265523 / 327680000000 : ℝ)
          + (2669733777 / 20971520000000 : ℝ) * w
          - (15962971043 / 2097152000000000 : ℝ) * w ^ 2
          + (123425059239 / 83886080000000000 : ℝ) * w ^ 3
          + (1469706541279 / 6710886400000000000 : ℝ) * w ^ 4
          + (50538160361473 / 1073741824000000000000 : ℝ) * w ^ 5
        ) := by
      unfold Qpair T6
      dsimp [t]
      ring
    rw [hfac, abs_mul, abs_of_nonneg (pow_nonneg hw0 7)]
    have hinner : |-(177265523 / 327680000000 : ℝ)
          + (2669733777 / 20971520000000 : ℝ) * w
          - (15962971043 / 2097152000000000 : ℝ) * w ^ 2
          + (123425059239 / 83886080000000000 : ℝ) * w ^ 3
          + (1469706541279 / 6710886400000000000 : ℝ) * w ^ 4
          + (50538160361473 / 1073741824000000000000 : ℝ) * w ^ 5| ≤ 1 / 1000 := by
      rw [abs_le]
      have hp2 : 0 ≤ w ^ 2 := pow_nonneg hw0 2
      have hp3 : 0 ≤ w ^ 3 := pow_nonneg hw0 3
      have hp4 : 0 ≤ w ^ 4 := pow_nonneg hw0 4
      have hp5 : 0 ≤ w ^ 5 := pow_nonneg hw0 5
      constructor <;> linarith
    have := mul_le_mul_of_nonneg_left hinner (pow_nonneg hw0 7)
    linarith
  have hQ_lo : (3 / 2 : ℝ) ≤ Qpair w := by
    unfold Qpair
    linarith
  have hP_lo : (3 / 2 : ℝ) ≤ P := by
    dsimp [P]
    have h1 : (3 / 4 : ℝ) ≤ Real.sqrt (1 + z + w / 5) := by
      rw [Real.le_sqrt (by norm_num) h1p]; linarith
    have h2 : (3 / 4 : ℝ) ≤ Real.sqrt (1 - z + w / 5) := by
      rw [Real.le_sqrt (by norm_num) h1m]; linarith
    linarith
  have hsum_lo : (3 : ℝ) ≤ P + Qpair w := by linarith
  have hsq_err : |P ^ 2 - Qpair w ^ 2| ≤ (7 / 1000 : ℝ) * w ^ 7 := by
    have h1 : P ^ 2 - Qpair w ^ 2 =
        2 * (Real.sqrt (1 + t) - T6 t) - (Qpair w ^ 2 - (2 + (2 / 5 : ℝ) * w + 2 * T6 t)) := by
      rw [hP_sq]; ring
    rw [h1]
    have htri := abs_sub (2 * (Real.sqrt (1 + t) - T6 t))
      (Qpair w ^ 2 - (2 + (2 / 5 : ℝ) * w + 2 * T6 t))
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at htri
    linarith
  have hmul : |P - Qpair w| * (P + Qpair w) = |P ^ 2 - Qpair w ^ 2| := by
    rw [← abs_of_nonneg (by linarith : 0 ≤ P + Qpair w), ← abs_mul]
    congr 1; ring
  have h3mul : 3 * |P - Qpair w| ≤ |P - Qpair w| * (P + Qpair w) := by
    have := mul_le_mul_of_nonneg_left hsum_lo (abs_nonneg (P - Qpair w))
    linarith
  linarith [pow_nonneg hw0 7]

set_option maxHeartbeats 400000 in
/-- **Theorem (Explicit Quadratic Family for `k = 3` Beating Qian & Wang 2006).**
    For every `k ≥ 1000`, our explicit `u = 5` quadratic family satisfies
    `0 < diff3 (a1 k) (a2 k) (a3 k) (b1 k) (b2 k) (b3 k) ≤ 1.6 × 10^11 / k^11`. -/
theorem k3_upper_bound_family {k : ℕ} (hk : 1000 ≤ k) :
    let a1 := 28968 ^ 2 * (k ^ 2 - 55)
    let a2 := 53125 ^ 2 * (k ^ 2 - 35)
    let a3 := 59049 ^ 2 * (9 * k ^ 2 + 5)
    let b1 := 13720 ^ 2 * (49 * k ^ 2 - 1295)
    let b2 := 81600 ^ 2 * (k ^ 2 + 10 * k + 20)
    let b3 := 81600 ^ 2 * (k ^ 2 - 10 * k + 20)
    1 ≤ a1 ∧ a1 ≤ 31381100000 * k ^ 2 ∧
    1 ≤ a2 ∧ a2 ≤ 31381100000 * k ^ 2 ∧
    1 ≤ a3 ∧ a3 ≤ 31381100000 * k ^ 2 ∧
    1 ≤ b1 ∧ b1 ≤ 31381100000 * k ^ 2 ∧
    1 ≤ b2 ∧ b2 ≤ 31381100000 * k ^ 2 ∧
    1 ≤ b3 ∧ b3 ≤ 31381100000 * k ^ 2 ∧
    0 < diff3 a1 a2 a3 b1 b2 b3 ∧
    diff3 a1 a2 a3 b1 b2 b3 ≤ (160000000000 : ℝ) / (k : ℝ) ^ 11 := by
  intro a1 a2 a3 b1 b2 b3
  have hk_r : (1000 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk_pos : (0 : ℝ) < (k : ℝ) := by linarith
  have hk2 : 1000000 ≤ k ^ 2 := by nlinarith only [hk]
  have h10k : 10 * k ≤ k ^ 2 := by nlinarith only [hk]
  have ha1_lo : 1 ≤ a1 := by dsimp [a1]; omega
  have ha2_lo : 1 ≤ a2 := by dsimp [a2]; omega
  have ha3_lo : 1 ≤ a3 := by dsimp [a3]; omega
  have hb1_lo : 1 ≤ b1 := by dsimp [b1]; omega
  have hb2_lo : 1 ≤ b2 := by dsimp [b2]; omega
  have hb3_lo : 1 ≤ b3 := by dsimp [b3]; omega
  have ha1_hi : a1 ≤ 31381100000 * k ^ 2 := by dsimp [a1]; omega
  have ha2_hi : a2 ≤ 31381100000 * k ^ 2 := by dsimp [a2]; omega
  have ha3_hi : a3 ≤ 31381100000 * k ^ 2 := by dsimp [a3]; omega
  have hb1_hi : b1 ≤ 31381100000 * k ^ 2 := by dsimp [b1]; omega
  have hb2_hi : b2 ≤ 31381100000 * k ^ 2 := by dsimp [b2]; omega
  have hb3_hi : b3 ≤ 31381100000 * k ^ 2 := by dsimp [b3]; omega
  -- Set z = 10 / k ∈ (0, 1/100] and w = z^2 = 100 / k^2 ∈ (0, 1/10000]
  set z : ℝ := 10 / (k : ℝ)
  set w : ℝ := z ^ 2
  have hz0 : 0 ≤ z := by positivity
  have hz_le : z ≤ 1 / 100 := by
    dsimp [z]; rw [div_le_iff₀ hk_pos]; linarith
  have hw0 : 0 ≤ w := sq_nonneg z
  have hw_le : w ≤ 1 / 10000 := by
    calc w = z ^ 2 := rfl
      _ ≤ (1 / 100 : ℝ) ^ 2 := pow_le_pow_left₀ hz0 hz_le 2
      _ = 1 / 10000 := by norm_num
  have hw_eq : w = 100 / (k : ℝ) ^ 2 := by dsimp [w, z]; ring
  -- Rewrite each of the 6 square roots as (weight * k) * sqrt(1 + ...)
  have hs_a1 : Real.sqrt a1 = 28968 * (k : ℝ) * Real.sqrt (1 + (-(11 / 20 : ℝ) * w)) := by
    have hcast : (a1 : ℝ) = (28968 * (k : ℝ)) ^ 2 * (1 + (-(11 / 20 : ℝ) * w)) := by
      dsimp [a1]
      rw [Nat.cast_mul, Nat.cast_sub (by omega : 55 ≤ k ^ 2), hw_eq]
      push_cast; field_simp; ring
    rw [hcast, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  have hs_a2 : Real.sqrt a2 = 53125 * (k : ℝ) * Real.sqrt (1 + (-(7 / 20 : ℝ) * w)) := by
    have hcast : (a2 : ℝ) = (53125 * (k : ℝ)) ^ 2 * (1 + (-(7 / 20 : ℝ) * w)) := by
      dsimp [a2]
      rw [Nat.cast_mul, Nat.cast_sub (by omega : 35 ≤ k ^ 2), hw_eq]
      push_cast; field_simp; ring
    rw [hcast, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  have hs_a3 : Real.sqrt a3 = 177147 * (k : ℝ) * Real.sqrt (1 + ((1 / 180 : ℝ) * w)) := by
    have hcast : (a3 : ℝ) = (177147 * (k : ℝ)) ^ 2 * (1 + ((1 / 180 : ℝ) * w)) := by
      dsimp [a3]; rw [hw_eq]; push_cast; field_simp; ring
    rw [hcast, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  have hs_b1 : Real.sqrt b1 = 96040 * (k : ℝ) * Real.sqrt (1 + (-(37 / 140 : ℝ) * w)) := by
    have hcast : (b1 : ℝ) = (96040 * (k : ℝ)) ^ 2 * (1 + (-(37 / 140 : ℝ) * w)) := by
      dsimp [b1]
      rw [Nat.cast_mul, Nat.cast_sub (by omega : 1295 ≤ 49 * k ^ 2), hw_eq]
      push_cast; field_simp; ring
    rw [hcast, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  have hs_b2 : Real.sqrt b2 = 81600 * (k : ℝ) * Real.sqrt (1 + z + z ^ 2 / 5) := by
    have hcast : (b2 : ℝ) = (81600 * (k : ℝ)) ^ 2 * (1 + z + z ^ 2 / 5) := by
      dsimp [b2, z]; push_cast; field_simp; ring
    rw [hcast, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  have hs_b3 : Real.sqrt b3 = 81600 * (k : ℝ) * Real.sqrt (1 - z + z ^ 2 / 5) := by
    have hcast : (b3 : ℝ) = (81600 * (k : ℝ)) ^ 2 * (1 - z + z ^ 2 / 5) := by
      dsimp [b3, z]
      rw [Nat.cast_mul, Nat.cast_add, Nat.cast_sub h10k]
      push_cast; field_simp; ring
    rw [hcast, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  -- Apply `sqrt_one_add_approx` to the 4 pure terms and `k3_pair_approx` to the conjugate pair
  have he1 : |Real.sqrt (1 + (-(11 / 20 : ℝ) * w)) - T6 (-(11 / 20 : ℝ) * w)| ≤
      (1 / 600 : ℝ) * w ^ 7 := by
    have h := sqrt_one_add_approx (t := -(11 / 20 : ℝ) * w) (by rw [abs_le]; constructor <;> linarith)
    have hle : |-(11 / 20 : ℝ) * w| = (11 / 20 : ℝ) * w := by
      rw [abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 11 / 20), abs_of_nonneg hw0]
    rw [hle] at h
    have hconst : (1 / 10 : ℝ) * (11 / 20 : ℝ) ^ 7 ≤ 1 / 600 := by norm_num
    have hw7 : 0 ≤ w ^ 7 := pow_nonneg hw0 7
    calc _ ≤ (1 / 10 : ℝ) * ((11 / 20 : ℝ) * w) ^ 7 := h
      _ = ((1 / 10 : ℝ) * (11 / 20 : ℝ) ^ 7) * w ^ 7 := by ring
      _ ≤ (1 / 600 : ℝ) * w ^ 7 := mul_le_mul_of_nonneg_right hconst hw7
  have he2 : |Real.sqrt (1 + (-(7 / 20 : ℝ) * w)) - T6 (-(7 / 20 : ℝ) * w)| ≤
      (1 / 10000 : ℝ) * w ^ 7 := by
    have h := sqrt_one_add_approx (t := -(7 / 20 : ℝ) * w) (by rw [abs_le]; constructor <;> linarith)
    have hle : |-(7 / 20 : ℝ) * w| = (7 / 20 : ℝ) * w := by
      rw [abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 7 / 20), abs_of_nonneg hw0]
    rw [hle] at h
    have hconst : (1 / 10 : ℝ) * (7 / 20 : ℝ) ^ 7 ≤ 1 / 10000 := by norm_num
    have hw7 : 0 ≤ w ^ 7 := pow_nonneg hw0 7
    calc _ ≤ (1 / 10 : ℝ) * ((7 / 20 : ℝ) * w) ^ 7 := h
      _ = ((1 / 10 : ℝ) * (7 / 20 : ℝ) ^ 7) * w ^ 7 := by ring
      _ ≤ (1 / 10000 : ℝ) * w ^ 7 := mul_le_mul_of_nonneg_right hconst hw7
  have he3 : |Real.sqrt (1 + ((1 / 180 : ℝ) * w)) - T6 ((1 / 180 : ℝ) * w)| ≤
      (1 / 1000000 : ℝ) * w ^ 7 := by
    have h := sqrt_one_add_approx (t := (1 / 180 : ℝ) * w) (by rw [abs_le]; constructor <;> linarith)
    have hle : |(1 / 180 : ℝ) * w| = (1 / 180 : ℝ) * w := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 180), abs_of_nonneg hw0]
    rw [hle] at h
    have hconst : (1 / 10 : ℝ) * (1 / 180 : ℝ) ^ 7 ≤ 1 / 1000000 := by norm_num
    have hw7 : 0 ≤ w ^ 7 := pow_nonneg hw0 7
    calc _ ≤ (1 / 10 : ℝ) * ((1 / 180 : ℝ) * w) ^ 7 := h
      _ = ((1 / 10 : ℝ) * (1 / 180 : ℝ) ^ 7) * w ^ 7 := by ring
      _ ≤ (1 / 1000000 : ℝ) * w ^ 7 := mul_le_mul_of_nonneg_right hconst hw7
  have he4 : |Real.sqrt (1 + (-(37 / 140 : ℝ) * w)) - T6 (-(37 / 140 : ℝ) * w)| ≤
      (1 / 100000 : ℝ) * w ^ 7 := by
    have h := sqrt_one_add_approx (t := -(37 / 140 : ℝ) * w) (by rw [abs_le]; constructor <;> linarith)
    have hle : |-(37 / 140 : ℝ) * w| = (37 / 140 : ℝ) * w := by
      rw [abs_mul, abs_neg, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 37 / 140), abs_of_nonneg hw0]
    rw [hle] at h
    have hconst : (1 / 10 : ℝ) * (37 / 140 : ℝ) ^ 7 ≤ 1 / 100000 := by norm_num
    have hw7 : 0 ≤ w ^ 7 := pow_nonneg hw0 7
    calc _ ≤ (1 / 10 : ℝ) * ((37 / 140 : ℝ) * w) ^ 7 := h
      _ = ((1 / 10 : ℝ) * (37 / 140 : ℝ) ^ 7) * w ^ 7 := by ring
      _ ≤ (1 / 100000 : ℝ) * w ^ 7 := mul_le_mul_of_nonneg_right hconst hw7
  have he_pair : |Real.sqrt (1 + z + z ^ 2 / 5) + Real.sqrt (1 - z + z ^ 2 / 5) - Qpair w| ≤
      (1 / 400 : ℝ) * w ^ 7 :=
    k3_pair_approx hz0 (by linarith)
  -- Combine using `k3_exact_moment_cancellation w`
  set S_inner : ℝ :=
    28968 * Real.sqrt (1 + (-(11 / 20 : ℝ) * w))
    + 53125 * Real.sqrt (1 + (-(7 / 20 : ℝ) * w))
    + 177147 * Real.sqrt (1 + ((1 / 180 : ℝ) * w))
    - 96040 * Real.sqrt (1 + (-(37 / 140 : ℝ) * w))
    - 81600 * (Real.sqrt (1 + z + z ^ 2 / 5) + Real.sqrt (1 - z + z ^ 2 / 5))
  have hS_eq : (Real.sqrt a1 + Real.sqrt a2 + Real.sqrt a3) -
      (Real.sqrt b1 + Real.sqrt b2 + Real.sqrt b3) = (k : ℝ) * S_inner := by
    rw [hs_a1, hs_a2, hs_a3, hs_b1, hs_b2, hs_b3]; dsimp [S_inner]; ring
  have hS_err : |S_inner - (-(187 / 1792 : ℝ) * w ^ 6)| ≤ 300 * w ^ 7 := by
    have hsplit : S_inner - (-(187 / 1792 : ℝ) * w ^ 6) =
        28968 * (Real.sqrt (1 + (-(11 / 20 : ℝ) * w)) - T6 (-(11 / 20 : ℝ) * w))
        + 53125 * (Real.sqrt (1 + (-(7 / 20 : ℝ) * w)) - T6 (-(7 / 20 : ℝ) * w))
        + 177147 * (Real.sqrt (1 + ((1 / 180 : ℝ) * w)) - T6 ((1 / 180 : ℝ) * w))
        - 96040 * (Real.sqrt (1 + (-(37 / 140 : ℝ) * w)) - T6 (-(37 / 140 : ℝ) * w))
        - 81600 * (Real.sqrt (1 + z + z ^ 2 / 5) + Real.sqrt (1 - z + z ^ 2 / 5) - Qpair w) := by
      rw [← k3_exact_moment_cancellation w]; dsimp [S_inner]; ring
    rw [hsplit]
    have h1 := abs_le.mp he1
    have h2 := abs_le.mp he2
    have h3 := abs_le.mp he3
    have h4 := abs_le.mp he4
    have h5 := abs_le.mp he_pair
    have hw7 : 0 ≤ w ^ 7 := pow_nonneg hw0 7
    rw [abs_le]
    constructor <;> linarith
  -- Since w ≤ 1/10000, 300 * w^7 ≤ 0.03 * w^6 < (1/2) * (187/1792) * w^6
  have hw6_pos : 0 < w ^ 6 := pow_pos (by dsimp [w, z]; positivity) 6
  have h300 : 300 * w ^ 7 ≤ (3 / 100 : ℝ) * w ^ 6 := by
    have h7 : w ^ 7 = w * w ^ 6 := by ring
    rw [h7]
    have := mul_le_mul_of_nonneg_right hw_le (le_of_lt hw6_pos)
    linarith
  have hS_bounds := abs_le.mp hS_err
  have hS_neg : S_inner ≤ -(1 / 20 : ℝ) * w ^ 6 := by linarith
  have hS_lo : -(16 / 100 : ℝ) * w ^ 6 ≤ S_inner := by linarith
  have hdiff_eq : diff3 a1 a2 a3 b1 b2 b3 = (k : ℝ) * (-S_inner) := by
    dsimp [diff3]; rw [hS_eq, abs_mul, abs_of_pos hk_pos, abs_of_neg (by linarith)]
  have hdiff_pos : 0 < diff3 a1 a2 a3 b1 b2 b3 := by
    rw [hdiff_eq]
    exact mul_pos hk_pos (by linarith)
  have hdiff_le : diff3 a1 a2 a3 b1 b2 b3 ≤ (160000000000 : ℝ) / (k : ℝ) ^ 11 := by
    rw [hdiff_eq]
    have hw6_k : (k : ℝ) * w ^ 6 = (1000000000000 : ℝ) / (k : ℝ) ^ 11 := by
      have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_pos
      rw [hw_eq]; field_simp; ring
    have hstep : (k : ℝ) * (-S_inner) ≤ (k : ℝ) * ((16 / 100 : ℝ) * w ^ 6) :=
      mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hk_pos)
    have hstep' : (k : ℝ) * (-S_inner) ≤ (16 / 100 : ℝ) * ((k : ℝ) * w ^ 6) := by linarith
    rw [hw6_k] at hstep'
    have hsimpl : (16 / 100 : ℝ) * ((1000000000000 : ℝ) / (k : ℝ) ^ 11) =
        (160000000000 : ℝ) / (k : ℝ) ^ 11 := by ring
    rwa [hsimpl] at hstep'
  exact ⟨ha1_lo, ha1_hi, ha2_lo, ha2_hi, ha3_lo, ha3_hi,
         hb1_lo, hb1_hi, hb2_lo, hb2_hi, hb3_lo, hb3_hi,
         hdiff_pos, hdiff_le⟩

/-- **Theorem (Global Upper Bound for `k = 3`: $r(n, 3) = O(n^{-11/2})$).**
    Beats Qian & Wang (*IPL* 2006), $r(n, 3) = O(n^{-9/2})$, by a full factor of $n$.
    For every integer $n \ge 31381100000000000$, there exist $1 \le a_1, a_2, a_3, b_1, b_2, b_3 \le n$
    with $0 < \mathrm{diff3}(a_1, a_2, a_3, b_1, b_2, b_3) \le \dfrac{10^{70}}{n^5 \sqrt{n}}$. -/
theorem k3_upper_bound {n : ℕ} (hn : 31381100000000000 ≤ n) :
    ∃ a1 a2 a3 b1 b2 b3 : ℕ,
      1 ≤ a1 ∧ a1 ≤ n ∧ 1 ≤ a2 ∧ a2 ≤ n ∧ 1 ≤ a3 ∧ a3 ≤ n ∧
      1 ≤ b1 ∧ b1 ≤ n ∧ 1 ≤ b2 ∧ b2 ≤ n ∧ 1 ≤ b3 ∧ b3 ≤ n ∧
      0 < diff3 a1 a2 a3 b1 b2 b3 ∧
      diff3 a1 a2 a3 b1 b2 b3 ≤ (10 ^ 70 : ℝ) / ((n : ℝ) ^ 5 * Real.sqrt n) := by
  set M : ℕ := 31381100000
  set k := Nat.sqrt (n / M)
  have hk_ge : 1000 ≤ k := by
    dsimp [k, M]
    rw [Nat.le_sqrt]
    omega
  have hMk2_le : M * k ^ 2 ≤ n := by
    have hk2 : k * k ≤ n / M := Nat.sqrt_le (n / M)
    have : k ^ 2 = k * k := sq k
    dsimp [M] at *
    omega
  have hMk1_gt : n < M * (k + 1) ^ 2 := by
    have hk1 : n / M < (k + 1) * (k + 1) := Nat.lt_succ_sqrt (n / M)
    have : (k + 1) ^ 2 = (k + 1) * (k + 1) := sq (k + 1)
    dsimp [M] at *
    omega
  have hf := k3_upper_bound_family hk_ge
  refine ⟨28968 ^ 2 * (k ^ 2 - 55), 53125 ^ 2 * (k ^ 2 - 35), 59049 ^ 2 * (9 * k ^ 2 + 5),
    13720 ^ 2 * (49 * k ^ 2 - 1295), 81600 ^ 2 * (k ^ 2 + 10 * k + 20), 81600 ^ 2 * (k ^ 2 - 10 * k + 20),
    hf.1, le_trans hf.2.1 hMk2_le,
    hf.2.2.1, le_trans hf.2.2.2.1 hMk2_le,
    hf.2.2.2.2.1, le_trans hf.2.2.2.2.2.1 hMk2_le,
    hf.2.2.2.2.2.2.1, le_trans hf.2.2.2.2.2.2.2.1 hMk2_le,
    hf.2.2.2.2.2.2.2.2.1, le_trans hf.2.2.2.2.2.2.2.2.2.1 hMk2_le,
    hf.2.2.2.2.2.2.2.2.2.2.1, le_trans hf.2.2.2.2.2.2.2.2.2.2.2.1 hMk2_le,
    hf.2.2.2.2.2.2.2.2.2.2.2.2.1, ?_⟩
  have hdiff_k := hf.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hr_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn_pos
  have hn_le_sq : (n : ℝ) ≤ (200000 * (k : ℝ)) ^ 2 := by
    have h1 : (n : ℝ) < (M : ℝ) * ((k : ℝ) + 1) ^ 2 := by exact_mod_cast hMk1_gt
    have hk1000 : (1000 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_ge
    dsimp [M] at h1
    nlinarith only [h1, hk1000]
  have hr_le : Real.sqrt n ≤ 200000 * (k : ℝ) := by
    rw [Real.sqrt_le_left (by positivity)]
    exact hn_le_sq
  have hpow11 : (n : ℝ) ^ 5 * Real.sqrt n ≤ (200000 * (k : ℝ)) ^ 11 := by
    have hr11 : (n : ℝ) ^ 5 * Real.sqrt n = (Real.sqrt n) ^ 11 := by
      have hsq : Real.sqrt n ^ 2 = (n : ℝ) := Real.sq_sqrt (le_of_lt hn_pos)
      calc (n : ℝ) ^ 5 * Real.sqrt n = (Real.sqrt n ^ 2) ^ 5 * Real.sqrt n := by rw [hsq]
        _ = (Real.sqrt n) ^ 11 := by ring
    rw [hr11]
    exact pow_le_pow_left₀ (le_of_lt hr_pos) hr_le 11
  have hstep : (160000000000 : ℝ) / (k : ℝ) ^ 11 ≤ (10 ^ 70 : ℝ) / ((n : ℝ) ^ 5 * Real.sqrt n) := by
    rw [div_le_div_iff₀ (pow_pos hk_pos 11) (mul_pos (pow_pos hn_pos 5) hr_pos)]
    have hconst : (160000000000 : ℝ) * (200000 : ℝ) ^ 11 ≤ (10 ^ 70 : ℝ) := by norm_num
    have hk11 : 0 ≤ (k : ℝ) ^ 11 := by positivity
    calc (160000000000 : ℝ) * ((n : ℝ) ^ 5 * Real.sqrt n)
        ≤ (160000000000 : ℝ) * (200000 * (k : ℝ)) ^ 11 :=
          mul_le_mul_of_nonneg_left hpow11 (by norm_num)
      _ = ((160000000000 : ℝ) * (200000 : ℝ) ^ 11) * (k : ℝ) ^ 11 := by ring
      _ ≤ (10 ^ 70 : ℝ) * (k : ℝ) ^ 11 := mul_le_mul_of_nonneg_right hconst hk11
  exact le_trans hdiff_k hstep

end SumOfSquareRoots
