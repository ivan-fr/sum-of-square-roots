import Mathlib
import SumOfSquareRoots.Basic

namespace SumOfSquareRoots

/-!
# Exact Separation Bounds for $k = 2$: $r(n, 2) = \Theta(n^{-7/2})$

We prove:
1. `k2_lower_bound`: For all $n \ge 1$ and $1 \le a_1, a_2, b_1, b_2 \le n$,
   if $\sqrt{a_1} + \sqrt{a_2} \ne \sqrt{b_1} + \sqrt{b_2}$, then
   $$|\sqrt{a_1} + \sqrt{a_2} - \sqrt{b_1} - \sqrt{b_2}| \ge \frac{1}{4\, n^3 \sqrt{n}},$$
   improving Burnikel--Fleischer--Mehlhorn--Schirra ($4^{-7} n^{-7/2}$) by a factor of $4096\times$.
2. `k2_exact_constant_bound`: The exact limiting constant at $S_1 = S_2$ is $27/8$,
   yielding the sharp asymptotic constant $8/27$.
3. `k2_upper_bound`: Using our constant-norm family
   $a_1(k) = 16 k^2, a_2(k) = 4 k^2 - 24, b_1(k) = 9 k^2 + 18 k - 9, b_2(k) = 9 k^2 - 18 k - 9$
   (algebraic norm identically $82944$), for all $n \ge 144$,
   $$\exists a_1, a_2, b_1, b_2 \in [1, n], \quad 0 < \mathrm{diff2}(a_1, a_2, b_1, b_2) \le \frac{4194304}{n^3 \sqrt{n}}.$$
-/

/-- Exact algebraic norm identity for `k = 2`. -/
lemma k2_norm_identity (a1 a2 b1 b2 : ℕ) :
    let x1 := Real.sqrt a1
    let x2 := Real.sqrt a2
    let y1 := Real.sqrt b1
    let y2 := Real.sqrt b2
    let M : ℤ := (((a1 : ℤ) + a2 - b1 - b2) ^ 2 - 4 * a1 * a2 - 4 * b1 * b2) ^ 2
                  - 64 * a1 * a2 * b1 * b2
    (M : ℝ) = ((x1 + x2) ^ 2 - (y1 + y2) ^ 2) * ((x1 + x2) ^ 2 - (y1 - y2) ^ 2) *
              ((x1 - x2) ^ 2 - (y1 + y2) ^ 2) * ((x1 - x2) ^ 2 - (y1 - y2) ^ 2) := by
  intro x1 x2 y1 y2 M
  have hx1 : x1 ^ 2 = (a1 : ℝ) := Real.sq_sqrt (Nat.cast_nonneg a1)
  have hx2 : x2 ^ 2 = (a2 : ℝ) := Real.sq_sqrt (Nat.cast_nonneg a2)
  have hy1 : y1 ^ 2 = (b1 : ℝ) := Real.sq_sqrt (Nat.cast_nonneg b1)
  have hy2 : y2 ^ 2 = (b2 : ℝ) := Real.sq_sqrt (Nat.cast_nonneg b2)
  set c : ℝ := (a1 : ℝ) + a2 - b1 - b2
  have hc_def : c = (a1 : ℝ) + a2 - b1 - b2 := rfl
  have ha1p : (x1 + x2) ^ 2 - (y1 + y2) ^ 2 = c + 2 * (x1 * x2 - y1 * y2) := by
    linear_combination hx1 + hx2 - hy1 - hy2 - hc_def
  have ha1m : (x1 - x2) ^ 2 - (y1 - y2) ^ 2 = c - 2 * (x1 * x2 - y1 * y2) := by
    linear_combination hx1 + hx2 - hy1 - hy2 - hc_def
  have ha2p : (x1 + x2) ^ 2 - (y1 - y2) ^ 2 = c + 2 * (x1 * x2 + y1 * y2) := by
    linear_combination hx1 + hx2 - hy1 - hy2 - hc_def
  have ha2m : (x1 - x2) ^ 2 - (y1 + y2) ^ 2 = c - 2 * (x1 * x2 + y1 * y2) := by
    linear_combination hx1 + hx2 - hy1 - hy2 - hc_def
  have h1 : ((x1 + x2) ^ 2 - (y1 + y2) ^ 2) * ((x1 - x2) ^ 2 - (y1 - y2) ^ 2) =
      c ^ 2 - 4 * (a1 : ℝ) * a2 - 4 * b1 * b2 + 8 * x1 * x2 * y1 * y2 := by
    rw [ha1p, ha1m]
    linear_combination -4 * x2 ^ 2 * hx1 - 4 * (a1 : ℝ) * hx2
      - 4 * y2 ^ 2 * hy1 - 4 * (b1 : ℝ) * hy2
  have h2 : ((x1 + x2) ^ 2 - (y1 - y2) ^ 2) * ((x1 - x2) ^ 2 - (y1 + y2) ^ 2) =
      c ^ 2 - 4 * (a1 : ℝ) * a2 - 4 * b1 * b2 - 8 * x1 * x2 * y1 * y2 := by
    rw [ha2p, ha2m]
    linear_combination -4 * x2 ^ 2 * hx1 - 4 * (a1 : ℝ) * hx2
      - 4 * y2 ^ 2 * hy1 - 4 * (b1 : ℝ) * hy2
  have hprod : ((x1 + x2) ^ 2 - (y1 + y2) ^ 2) * ((x1 + x2) ^ 2 - (y1 - y2) ^ 2) *
      ((x1 - x2) ^ 2 - (y1 + y2) ^ 2) * ((x1 - x2) ^ 2 - (y1 - y2) ^ 2) =
      (((x1 + x2) ^ 2 - (y1 + y2) ^ 2) * ((x1 - x2) ^ 2 - (y1 - y2) ^ 2)) *
      (((x1 + x2) ^ 2 - (y1 - y2) ^ 2) * ((x1 - x2) ^ 2 - (y1 + y2) ^ 2)) := by ring
  rw [hprod, h1, h2]
  have h64 : (8 * x1 * x2 * y1 * y2) ^ 2 = 64 * (a1 : ℝ) * a2 * b1 * b2 := by
    calc (8 * x1 * x2 * y1 * y2) ^ 2
        = 64 * (x1 ^ 2) * (x2 ^ 2) * (y1 ^ 2) * (y2 ^ 2) := by ring
      _ = 64 * (a1 : ℝ) * a2 * b1 * b2 := by rw [hx1, hx2, hy1, hy2]
  dsimp [M]
  push_cast
  rw [← hc_def]
  linear_combination h64

/-- Exact limiting constant `27/8` at `S1 = S2` (giving the asymptotic floor `8/27`). -/
lemma k2_exact_constant_bound {S : ℝ} (hS1 : 1 ≤ S) (hS2 : S ≤ 2) :
    8 * S ^ 3 * (S - 1) * (2 - S) ^ 2 ≤ 27 / 8 := by
  have h : 27 / 8 - 8 * S ^ 3 * (S - 1) * (2 - S) ^ 2 =
      (2 * S - 3) ^ 2 * (16 * S ^ 3 * (2 - S) + 4 * S ^ 2 + 4 * S + 3) / 8 := by
    ring
  have hS0 : 0 ≤ S := by linarith
  have hpos : 0 ≤ 16 * S ^ 3 * (2 - S) + 4 * S ^ 2 + 4 * S + 3 := by
    have h1 : 0 ≤ 16 * S ^ 3 * (2 - S) := mul_nonneg (by positivity) (by linarith)
    have h2 : 0 ≤ 4 * S ^ 2 + 4 * S + 3 := by positivity
    linarith
  have hsq : 0 ≤ (2 * S - 3) ^ 2 := sq_nonneg _
  have hprod : 0 ≤ (2 * S - 3) ^ 2 * (16 * S ^ 3 * (2 - S) + 4 * S ^ 2 + 4 * S + 3) :=
    mul_nonneg hsq hpos
  linarith

/-- Elementary univariate bound on `S ∈ [5/4, 2]`. -/
private lemma k2_denom_poly_bound {S : ℝ} (h1 : 5 / 4 ≤ S) (h2 : S ≤ 2) :
    2 * S ^ 3 * (S ^ 2 - (2 - S + 1 / 64) ^ 2) * (2 - S + 1 / 64) ^ 2 ≤ 4 := by
  set t := 2 - S
  have ht_eq : t = 2 - S := rfl
  have ht0 : 0 ≤ t := by linarith
  have ht1 : t ≤ 3 / 4 := by linarith
  have hS_eq : S = 2 - t := by linarith
  have hsub : S ^ 2 - (t + 1 / 64) ^ 2 ≤ 4 * (1 - t) := by
    rw [hS_eq]; nlinarith only [ht0, ht1]
  have hS0 : 0 ≤ S := by linarith
  have hS3_pos : 0 ≤ S ^ 3 := by positivity
  have hS3_le : S ^ 3 ≤ 8 := by
    calc S ^ 3 ≤ 2 ^ 3 := pow_le_pow_left₀ hS0 h2 3
      _ = 8 := by norm_num
  have h1t_pos : 0 ≤ 1 - t := by linarith
  have h1t_le : 1 - t ≤ 1 := by linarith
  have ht1t : t * (1 - t) ≤ 1 / 4 := by nlinarith only [sq_nonneg (t - 1 / 2)]
  have hstep1 : 2 * S ^ 3 * (S ^ 2 - (t + 1 / 64) ^ 2) * (t + 1 / 64) ^ 2 ≤
      8 * S ^ 3 * (1 - t) * (t + 1 / 64) ^ 2 := by
    have hmul1 : 2 * S ^ 3 * (S ^ 2 - (t + 1 / 64) ^ 2) ≤ 2 * S ^ 3 * (4 * (1 - t)) :=
      mul_le_mul_of_nonneg_left hsub (by linarith)
    have hmul2 := mul_le_mul_of_nonneg_right hmul1 (sq_nonneg (t + 1 / 64))
    linarith
  have hexp : 8 * S ^ 3 * (1 - t) * (t + 1 / 64) ^ 2 =
      8 * S ^ 3 * (S - 1) * (2 - S) ^ 2 +
      (1 / 4 : ℝ) * S ^ 3 * (t * (1 - t)) +
      (1 / 512 : ℝ) * S ^ 3 * (1 - t) := by
    rw [hS_eq]; ring
  have hmain := k2_exact_constant_bound (by linarith : (1 : ℝ) ≤ S) h2
  have hextra1 : (1 / 4 : ℝ) * S ^ 3 * (t * (1 - t)) ≤ 1 / 2 := by
    have h1 : (1 / 4 : ℝ) * S ^ 3 * (t * (1 - t)) ≤ (1 / 4 : ℝ) * 8 * (1 / 4) := by
      have ha : (1 / 4 : ℝ) * S ^ 3 ≤ (1 / 4 : ℝ) * 8 := by linarith
      exact mul_le_mul ha ht1t (mul_nonneg ht0 h1t_pos) (by norm_num)
    linarith
  have hextra2 : (1 / 512 : ℝ) * S ^ 3 * (1 - t) ≤ 1 / 64 := by
    have ha : (1 / 512 : ℝ) * S ^ 3 ≤ (1 / 512 : ℝ) * 8 := by linarith
    have h1 := mul_le_mul ha h1t_le h1t_pos (by norm_num)
    linarith
  linarith

/-- Normalized denominator bound for `k = 2` when `|S1 - S2| ≤ 1/64`. -/
private lemma k2_normalized_denom_le_four {u1 u2 v1 v2 : ℝ}
    (hu10 : 0 ≤ u1) (hu11 : u1 ≤ 1) (hu20 : 0 ≤ u2) (hu21 : u2 ≤ 1)
    (hv10 : 0 ≤ v1) (hv11 : v1 ≤ 1) (hv20 : 0 ≤ v2) (hv21 : v2 ≤ 1)
    (hclose : |(u1 + u2) - (v1 + v2)| ≤ 1 / 64) :
    (u1 + u2 + (v1 + v2)) *
      |(u1 + u2) ^ 2 - (v1 - v2) ^ 2| *
      |(u1 - u2) ^ 2 - (v1 + v2) ^ 2| *
      |(u1 - u2) ^ 2 - (v1 - v2) ^ 2| ≤ 4 := by
  set S1 := u1 + u2
  set S2 := v1 + v2
  set da := |u1 - u2|
  set db := |v1 - v2|
  set S := max S1 S2
  have hS1_nn : 0 ≤ S1 := by linarith
  have hS2_nn : 0 ≤ S2 := by linarith
  have hS1_le : S1 ≤ S := le_max_left S1 S2
  have hS2_le : S2 ≤ S := le_max_right S1 S2
  have hS_nn : 0 ≤ S := le_trans hS1_nn hS1_le
  have hS_le2 : S ≤ 2 := max_le (by linarith) (by linarith)
  have hcl : -(1 / 64 : ℝ) ≤ S1 - S2 ∧ S1 - S2 ≤ 1 / 64 := abs_le.mp hclose
  have hS1_lo : S - 1 / 64 ≤ S1 := by
    have : S ≤ S1 + 1 / 64 := max_le (by linarith) (by linarith [hcl.1])
    linarith
  have hS2_lo : S - 1 / 64 ≤ S2 := by
    have : S ≤ S2 + 1 / 64 := max_le (by linarith [hcl.2]) (by linarith)
    linarith
  have hda_nn : 0 ≤ da := abs_nonneg _
  have hdb_nn : 0 ≤ db := abs_nonneg _
  have hda_sq : da ^ 2 = (u1 - u2) ^ 2 := sq_abs _
  have hdb_sq : db ^ 2 = (v1 - v2) ^ 2 := sq_abs _
  have hda_le_S1 : da ≤ S1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hdb_le_S2 : db ≤ S2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hda_le_2m : da ≤ 2 - S1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hdb_le_2m : db ≤ 2 - S2 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hda_le_S : da ≤ S := le_trans hda_le_S1 hS1_le
  have hdb_le_S : db ≤ S := le_trans hdb_le_S2 hS2_le
  have hS1_sq : S1 ^ 2 ≤ S ^ 2 := pow_le_pow_left₀ hS1_nn hS1_le 2
  have hS2_sq : S2 ^ 2 ≤ S ^ 2 := pow_le_pow_left₀ hS2_nn hS2_le 2
  have hda2_le : (u1 - u2) ^ 2 ≤ S ^ 2 := by rw [← hda_sq]; exact pow_le_pow_left₀ hda_nn hda_le_S 2
  have hdb2_le : (v1 - v2) ^ 2 ≤ S ^ 2 := by rw [← hdb_sq]; exact pow_le_pow_left₀ hdb_nn hdb_le_S 2
  have hsum_le : S1 + S2 ≤ 2 * S := by linarith
  -- Case 1: S ≤ 21/20
  by_cases hS_small : S ≤ 21 / 20
  · have hf1 : |S1 ^ 2 - (v1 - v2) ^ 2| ≤ S ^ 2 :=
      abs_le.mpr ⟨by linarith [sq_nonneg S1, hdb2_le], by linarith [sq_nonneg (v1 - v2), hS1_sq]⟩
    have hf2 : |(u1 - u2) ^ 2 - S2 ^ 2| ≤ S ^ 2 :=
      abs_le.mpr ⟨by linarith [sq_nonneg (u1 - u2), hS2_sq], by linarith [sq_nonneg S2, hda2_le]⟩
    have hf3 : |(u1 - u2) ^ 2 - (v1 - v2) ^ 2| ≤ S ^ 2 :=
      abs_le.mpr ⟨by linarith [sq_nonneg (u1 - u2), hdb2_le], by linarith [sq_nonneg (v1 - v2), hda2_le]⟩
    have hp1 : (S1 + S2) * |S1 ^ 2 - (v1 - v2) ^ 2| ≤ 2 * S * S ^ 2 :=
      mul_le_mul hsum_le hf1 (abs_nonneg _) (by linarith)
    have hp2 : |(u1 - u2) ^ 2 - S2 ^ 2| * |(u1 - u2) ^ 2 - (v1 - v2) ^ 2| ≤ S ^ 2 * S ^ 2 :=
      mul_le_mul hf2 hf3 (abs_nonneg _) (sq_nonneg S)
    have hp3 : (S1 + S2) * |S1 ^ 2 - (v1 - v2) ^ 2| *
        |(u1 - u2) ^ 2 - S2 ^ 2| * |(u1 - u2) ^ 2 - (v1 - v2) ^ 2| ≤ 2 * S ^ 7 := by
      have h := mul_le_mul hp1 hp2 (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (by positivity)
      linarith [show (2 * S * S ^ 2) * (S ^ 2 * S ^ 2) = 2 * S ^ 7 by ring]
    have hpow : 2 * S ^ 7 ≤ 4 := by
      have h7 : S ^ 7 ≤ (21 / 20 : ℝ) ^ 7 := pow_le_pow_left₀ hS_nn hS_small 7
      have hconst : 2 * (21 / 20 : ℝ) ^ 7 ≤ 4 := by norm_num
      linarith
    linarith
  · -- Case 2: S > 21/20
    push Not at hS_small
    have hda_bnd : da ≤ 2 - S + 1 / 64 := by linarith
    have hdb_bnd : db ≤ 2 - S + 1 / 64 := by linarith
    have hbnd_le_S1 : 2 - S + 1 / 64 ≤ S1 := by linarith
    have hbnd_le_S2 : 2 - S + 1 / 64 ≤ S2 := by linarith
    have hda_le_S2 : da ≤ S2 := le_trans hda_bnd hbnd_le_S2
    have hdb_le_S1 : db ≤ S1 := le_trans hdb_bnd hbnd_le_S1
    have h1_pos : 0 ≤ S1 ^ 2 - (v1 - v2) ^ 2 := by
      rw [← hdb_sq]; linarith [pow_le_pow_left₀ hdb_nn hdb_le_S1 2]
    have h2_pos : 0 ≤ S2 ^ 2 - (u1 - u2) ^ 2 := by
      rw [← hda_sq]; linarith [pow_le_pow_left₀ hda_nn hda_le_S2 2]
    rw [abs_of_nonneg h1_pos]
    have h2_abs : |(u1 - u2) ^ 2 - S2 ^ 2| = S2 ^ 2 - (u1 - u2) ^ 2 := by
      rw [abs_sub_comm, abs_of_nonneg h2_pos]
    rw [h2_abs]
    set D := max ((u1 - u2) ^ 2) ((v1 - v2) ^ 2)
    have hD_nn : 0 ≤ D := le_trans (sq_nonneg _) (le_max_left _ _)
    have hD_le_bnd : D ≤ (2 - S + 1 / 64) ^ 2 := by
      refine max_le ?_ ?_
      · rw [← hda_sq]; exact pow_le_pow_left₀ hda_nn hda_bnd 2
      · rw [← hdb_sq]; exact pow_le_pow_left₀ hdb_nn hdb_bnd 2
    have hD_le_S2 : D ≤ S ^ 2 := max_le hda2_le hdb2_le
    -- Key product bound: (S1^2 - db^2) * (S2^2 - da^2) * |da^2 - db^2| ≤ S^2 * (S^2 - D) * D
    have hprod_D : (S1 ^ 2 - (v1 - v2) ^ 2) * (S2 ^ 2 - (u1 - u2) ^ 2) *
        |(u1 - u2) ^ 2 - (v1 - v2) ^ 2| ≤ S ^ 2 * (S ^ 2 - D) * D := by
      by_cases hcmp : (u1 - u2) ^ 2 ≥ (v1 - v2) ^ 2
      · have hD_eq : D = (u1 - u2) ^ 2 := max_eq_left hcmp
        rw [hD_eq, abs_of_nonneg (by linarith)]
        have hf1 : S1 ^ 2 - (v1 - v2) ^ 2 ≤ S ^ 2 := by linarith [sq_nonneg (v1 - v2), hS1_sq]
        have hf2 : S2 ^ 2 - (u1 - u2) ^ 2 ≤ S ^ 2 - (u1 - u2) ^ 2 := by linarith [hS2_sq]
        have hf3 : (u1 - u2) ^ 2 - (v1 - v2) ^ 2 ≤ (u1 - u2) ^ 2 := by linarith [sq_nonneg (v1 - v2)]
        have hp12 : (S1 ^ 2 - (v1 - v2) ^ 2) * (S2 ^ 2 - (u1 - u2) ^ 2) ≤
            S ^ 2 * (S ^ 2 - (u1 - u2) ^ 2) :=
          mul_le_mul hf1 hf2 h2_pos (sq_nonneg S)
        exact mul_le_mul hp12 hf3 (by linarith) (mul_nonneg (sq_nonneg S) (by linarith [hda2_le]))
      · push Not at hcmp
        have hD_eq : D = (v1 - v2) ^ 2 := max_eq_right (le_of_lt hcmp)
        rw [hD_eq, abs_sub_comm, abs_of_nonneg (by linarith)]
        have hf1 : S1 ^ 2 - (v1 - v2) ^ 2 ≤ S ^ 2 - (v1 - v2) ^ 2 := by linarith [hS1_sq]
        have hf2 : S2 ^ 2 - (u1 - u2) ^ 2 ≤ S ^ 2 := by linarith [sq_nonneg (u1 - u2), hS2_sq]
        have hf3 : (v1 - v2) ^ 2 - (u1 - u2) ^ 2 ≤ (v1 - v2) ^ 2 := by linarith [sq_nonneg (u1 - u2)]
        have hp12 : (S1 ^ 2 - (v1 - v2) ^ 2) * (S2 ^ 2 - (u1 - u2) ^ 2) ≤
            (S ^ 2 - (v1 - v2) ^ 2) * S ^ 2 :=
          mul_le_mul hf1 hf2 h2_pos (by linarith [hdb2_le])
        have hp12' : (S1 ^ 2 - (v1 - v2) ^ 2) * (S2 ^ 2 - (u1 - u2) ^ 2) ≤
            S ^ 2 * (S ^ 2 - (v1 - v2) ^ 2) := by linarith
        exact mul_le_mul hp12' hf3 (by linarith) (mul_nonneg (sq_nonneg S) (by linarith [hdb2_le]))
    have htotal : (S1 + S2) * (S1 ^ 2 - (v1 - v2) ^ 2) *
        (S2 ^ 2 - (u1 - u2) ^ 2) * |(u1 - u2) ^ 2 - (v1 - v2) ^ 2| ≤
        2 * S ^ 3 * (S ^ 2 - D) * D := by
      have h1 := mul_le_mul hsum_le hprod_D
        (mul_nonneg (mul_nonneg h1_pos h2_pos) (abs_nonneg _)) (by linarith)
      linarith [show 2 * S * (S ^ 2 * (S ^ 2 - D) * D) = 2 * S ^ 3 * (S ^ 2 - D) * D by ring]
    -- Subcase 2a: S ≤ 5/4 -> use AM-GM (S^2 - D)*D ≤ S^4 / 4
    by_cases hS_mid : S ≤ 5 / 4
    · have hamgm : (S ^ 2 - D) * D ≤ S ^ 4 / 4 := by
        nlinarith only [sq_nonneg (D - S ^ 2 / 2)]
      have hS3_pos : 0 ≤ S ^ 3 := by positivity
      have hmul : 2 * S ^ 3 * ((S ^ 2 - D) * D) ≤ 2 * S ^ 3 * (S ^ 4 / 4) :=
        mul_le_mul_of_nonneg_left hamgm (by linarith)
      have hS7 : (1 / 2 : ℝ) * S ^ 7 ≤ 4 := by
        have h7 : S ^ 7 ≤ (5 / 4 : ℝ) ^ 7 := pow_le_pow_left₀ hS_nn hS_mid 7
        have hconst : (1 / 2 : ℝ) * (5 / 4 : ℝ) ^ 7 ≤ 4 := by norm_num
        linarith
      linarith [show 2 * S ^ 3 * (S ^ 4 / 4) = (1 / 2 : ℝ) * S ^ 7 by ring,
                show 2 * S ^ 3 * (S ^ 2 - D) * D = 2 * S ^ 3 * ((S ^ 2 - D) * D) by ring]
    · -- Subcase 2b: S > 5/4 -> D ≤ (2 - S + 1/64)^2 ≤ S^2 / 2, so (S^2 - D)*D is increasing in D
      push Not at hS_mid
      have hhalf : (2 - S + 1 / 64) ^ 2 ≤ S ^ 2 / 2 := by
        nlinarith only [hS_mid, hS_le2]
      have hinc : (S ^ 2 - D) * D ≤
          (S ^ 2 - (2 - S + 1 / 64) ^ 2) * (2 - S + 1 / 64) ^ 2 := by
        have hdiff : (S ^ 2 - (2 - S + 1 / 64) ^ 2) * (2 - S + 1 / 64) ^ 2 - (S ^ 2 - D) * D =
            ((2 - S + 1 / 64) ^ 2 - D) * (S ^ 2 - (2 - S + 1 / 64) ^ 2 - D) := by ring
        have hprod_nn : 0 ≤ ((2 - S + 1 / 64) ^ 2 - D) * (S ^ 2 - (2 - S + 1 / 64) ^ 2 - D) :=
          mul_nonneg (by linarith) (by linarith)
        linarith
      have hS3_pos : 0 ≤ S ^ 3 := by positivity
      have hmul := mul_le_mul_of_nonneg_left hinc (by linarith : 0 ≤ 2 * S ^ 3)
      have hpoly := k2_denom_poly_bound (le_of_lt hS_mid) hS_le2
      linarith [show 2 * S ^ 3 * (S ^ 2 - D) * D = 2 * S ^ 3 * ((S ^ 2 - D) * D) by ring,
                show 2 * S ^ 3 * ((S ^ 2 - (2 - S + 1 / 64) ^ 2) * (2 - S + 1 / 64) ^ 2) =
                     2 * S ^ 3 * (S ^ 2 - (2 - S + 1 / 64) ^ 2) * (2 - S + 1 / 64) ^ 2 by ring]

/-- **Theorem (Sharp Lower Bound for `k = 2`).**
    For all `n ≥ 1` and `1 ≤ a1, a2, b1, b2 ≤ n`, whenever
    `√a1 + √a2 ≠ √b1 + √b2`, we have
    `|√a1 + √a2 - √b1 - √b2| ≥ 1 / (4 * n^3 * √n)`. -/
theorem k2_lower_bound {n a1 a2 b1 b2 : ℕ}
    (ha1_lo : 1 ≤ a1) (ha1_hi : a1 ≤ n)
    (ha2_lo : 1 ≤ a2) (ha2_hi : a2 ≤ n)
    (hb1_lo : 1 ≤ b1) (hb1_hi : b1 ≤ n)
    (hb2_lo : 1 ≤ b2) (hb2_hi : b2 ≤ n)
    (hne : diff2 a1 a2 b1 b2 ≠ 0) :
    (1 / 4 : ℝ) / ((n : ℝ) ^ 3 * Real.sqrt n) ≤ diff2 a1 a2 b1 b2 := by
  have hn_ge2 : 2 ≤ n := by
    by_contra h
    push Not at h
    have hn1 : n = 1 := by omega
    subst hn1
    have : a1 = 1 := by omega
    have : a2 = 1 := by omega
    have : b1 = 1 := by omega
    have : b2 = 1 := by omega
    subst_vars
    simp [diff2] at hne
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hr_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn_pos
  have hr_sq : Real.sqrt n ^ 2 = (n : ℝ) := Real.sq_sqrt (le_of_lt hn_pos)
  set x1 := Real.sqrt a1
  set x2 := Real.sqrt a2
  set y1 := Real.sqrt b1
  set y2 := Real.sqrt b2
  have hx1_ge1 : 1 ≤ x1 := by
    rw [Real.le_sqrt (by norm_num) (Nat.cast_nonneg a1)]
    exact_mod_cast ha1_lo
  have hx2_ge1 : 1 ≤ x2 := by
    rw [Real.le_sqrt (by norm_num) (Nat.cast_nonneg a2)]
    exact_mod_cast ha2_lo
  have hy1_ge1 : 1 ≤ y1 := by
    rw [Real.le_sqrt (by norm_num) (Nat.cast_nonneg b1)]
    exact_mod_cast hb1_lo
  have hy2_ge1 : 1 ≤ y2 := by
    rw [Real.le_sqrt (by norm_num) (Nat.cast_nonneg b2)]
    exact_mod_cast hb2_lo
  have hx1_le : x1 ≤ Real.sqrt n := Real.sqrt_le_sqrt (by exact_mod_cast ha1_hi)
  have hx2_le : x2 ≤ Real.sqrt n := Real.sqrt_le_sqrt (by exact_mod_cast ha2_hi)
  have hy1_le : y1 ≤ Real.sqrt n := Real.sqrt_le_sqrt (by exact_mod_cast hb1_hi)
  have hy2_le : y2 ≤ Real.sqrt n := Real.sqrt_le_sqrt (by exact_mod_cast hb2_hi)
  have hsum_pos : 0 < x1 + x2 + (y1 + y2) := by linarith
  have hsum_le : x1 + x2 + (y1 + y2) ≤ 4 * Real.sqrt n := by linarith
  have hA1_ne_B1 : (x1 + x2) ^ 2 - (y1 + y2) ^ 2 ≠ 0 := by
    intro h
    have hfac : (x1 + x2) ^ 2 - (y1 + y2) ^ 2 = ((x1 + x2) - (y1 + y2)) * (x1 + x2 + (y1 + y2)) := by ring
    rw [hfac] at h
    rcases mul_eq_zero.mp h with h0 | h0
    · exact hne (by simp [diff2, x1, x2, y1, y2, h0])
    · linarith
  set M : ℤ := (((a1 : ℤ) + a2 - b1 - b2) ^ 2 - 4 * a1 * a2 - 4 * b1 * b2) ^ 2
                - 64 * a1 * a2 * b1 * b2
  have hM_id : (M : ℝ) = ((x1 + x2) ^ 2 - (y1 + y2) ^ 2) * ((x1 + x2) ^ 2 - (y1 - y2) ^ 2) *
      ((x1 - x2) ^ 2 - (y1 + y2) ^ 2) * ((x1 - x2) ^ 2 - (y1 - y2) ^ 2) :=
    k2_norm_identity a1 a2 b1 b2
  by_cases hM0 : M = 0
  · -- Degenerate case M = 0: one of the other three conjugate factors vanishes -> |A1 - B1| ≥ 2!
    rw [hM0, Int.cast_zero] at hM_id
    have hzero : ((x1 + x2) ^ 2 - (y1 - y2) ^ 2 = 0) ∨
        ((x1 - x2) ^ 2 - (y1 + y2) ^ 2 = 0) ∨
        ((x1 - x2) ^ 2 - (y1 - y2) ^ 2 = 0) := by
      rcases mul_eq_zero.mp hM_id.symm with h123 | h4
      · rcases mul_eq_zero.mp h123 with h12 | h3
        · rcases mul_eq_zero.mp h12 with h1 | h2
          · exact absurd h1 hA1_ne_B1
          · exact Or.inl h2
        · exact Or.inr (Or.inl h3)
      · exact Or.inr (Or.inr h4)
    have hgap2 : 2 ≤ |(x1 + x2) ^ 2 - (y1 + y2) ^ 2| := by
      rcases hzero with h2 | h3 | h4
      · have hdiff : (y1 + y2) ^ 2 - (x1 + x2) ^ 2 = 4 * y1 * y2 := by linear_combination -h2
        have h4ge : 4 ≤ (y1 + y2) ^ 2 - (x1 + x2) ^ 2 := by
          have : 1 ≤ y1 * y2 := one_le_mul_of_one_le_of_one_le hy1_ge1 hy2_ge1
          linarith
        rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
      · have hdiff : (x1 + x2) ^ 2 - (y1 + y2) ^ 2 = 4 * x1 * x2 := by linear_combination h3
        have h4ge : 4 ≤ (x1 + x2) ^ 2 - (y1 + y2) ^ 2 := by
          have : 1 ≤ x1 * x2 := one_le_mul_of_one_le_of_one_le hx1_ge1 hx2_ge1
          linarith
        rw [abs_of_nonneg (by linarith)]; linarith
      · have hx1sq : x1 ^ 2 = (a1 : ℝ) := Real.sq_sqrt (Nat.cast_nonneg a1)
        have hx2sq : x2 ^ 2 = (a2 : ℝ) := Real.sq_sqrt (Nat.cast_nonneg a2)
        have hy1sq : y1 ^ 2 = (b1 : ℝ) := Real.sq_sqrt (Nat.cast_nonneg b1)
        have hy2sq : y2 ^ 2 = (b2 : ℝ) := Real.sq_sqrt (Nat.cast_nonneg b2)
        set c_int : ℤ := (a1 : ℤ) + a2 - b1 - b2
        have h2c : (x1 + x2) ^ 2 - (y1 + y2) ^ 2 = 2 * (c_int : ℝ) := by
          have hsum : ((x1 + x2) ^ 2 - (y1 + y2) ^ 2) + ((x1 - x2) ^ 2 - (y1 - y2) ^ 2) =
              2 * (c_int : ℝ) := by
            dsimp [c_int]; push_cast
            linear_combination 2 * hx1sq + 2 * hx2sq - 2 * hy1sq - 2 * hy2sq
          linarith
        have hc_ne : c_int ≠ 0 := by
          intro hc0
          rw [hc0, Int.cast_zero, mul_zero] at h2c
          exact hA1_ne_B1 h2c
        have hc_abs : (1 : ℝ) ≤ |(c_int : ℝ)| := by
          have : (1 : ℤ) ≤ |c_int| := Int.one_le_abs hc_ne
          exact_mod_cast this
        rw [h2c, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        linarith
    have hdiff_eq : diff2 a1 a2 b1 b2 * (x1 + x2 + (y1 + y2)) =
        |(x1 + x2) ^ 2 - (y1 + y2) ^ 2| := by
      dsimp [diff2, x1, x2, y1, y2]
      rw [← abs_of_pos hsum_pos, ← abs_mul]
      congr 1; ring
    have hge_half : (1 / 2 : ℝ) / Real.sqrt n ≤ diff2 a1 a2 b1 b2 := by
      rw [div_le_iff₀ hr_pos]
      have hmul : diff2 a1 a2 b1 b2 * (x1 + x2 + (y1 + y2)) ≤
          diff2 a1 a2 b1 b2 * (4 * Real.sqrt n) :=
        mul_le_mul_of_nonneg_left hsum_le (abs_nonneg _)
      linarith
    have hn3_ge1 : (1 : ℝ) ≤ (n : ℝ) ^ 3 := by
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
      exact one_le_pow₀ hn1
    have hcomp : (1 / 4 : ℝ) / ((n : ℝ) ^ 3 * Real.sqrt n) ≤ (1 / 2 : ℝ) / Real.sqrt n := by
      rw [div_le_div_iff₀ (mul_pos (pow_pos hn_pos 3) hr_pos) hr_pos]
      have : (1 / 4 : ℝ) * Real.sqrt n ≤ (1 / 2 : ℝ) * ((n : ℝ) ^ 3 * Real.sqrt n) := by
        have h1 : (1 / 4 : ℝ) * Real.sqrt n ≤ (1 / 2 : ℝ) * Real.sqrt n := by linarith
        have h2 : (1 / 2 : ℝ) * Real.sqrt n ≤ (1 / 2 : ℝ) * ((n : ℝ) ^ 3 * Real.sqrt n) := by
          have := mul_le_mul_of_nonneg_right hn3_ge1 (le_of_lt hr_pos)
          linarith
        linarith
      exact this
    exact le_trans hcomp hge_half
  · -- Main non-degenerate case M ≠ 0: |M| ≥ 1!
    by_contra hlt
    push Not at hlt
    have hM_ge1 : (1 : ℝ) ≤ |(M : ℝ)| := by
      have : (1 : ℤ) ≤ |M| := Int.one_le_abs hM0
      exact_mod_cast this
    -- Rescale to u1, u2, v1, v2 ∈ [0, 1] by dividing by r = √n
    set r := Real.sqrt n
    set u1 := x1 / r
    set u2 := x2 / r
    set v1 := y1 / r
    set v2 := y2 / r
    have hclose : |(u1 + u2) - (v1 + v2)| ≤ 1 / 64 := by
      have heq : |(u1 + u2) - (v1 + v2)| = diff2 a1 a2 b1 b2 / r := by
        dsimp [diff2, u1, u2, v1, v2, x1, x2, y1, y2]
        rw [← add_div, ← add_div, ← sub_div, abs_div, abs_of_pos hr_pos]
      rw [heq]
      have hn2r : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn_ge2
      have hn4 : (16 : ℝ) ≤ (n : ℝ) ^ 4 := by
        calc (16 : ℝ) = 2 ^ 4 := by norm_num
          _ ≤ (n : ℝ) ^ 4 := pow_le_pow_left₀ (by norm_num) hn2r 4
      have hstep : diff2 a1 a2 b1 b2 / r < (1 / 4 : ℝ) / ((n : ℝ) ^ 4) := by
        have : (1 / 4 : ℝ) / ((n : ℝ) ^ 3 * r) / r = (1 / 4 : ℝ) / (n : ℝ) ^ 4 := by
          rw [div_div]
          have : (n : ℝ) ^ 3 * r * r = (n : ℝ) ^ 4 := by
            calc (n : ℝ) ^ 3 * r * r = (n : ℝ) ^ 3 * r ^ 2 := by ring
              _ = (n : ℝ) ^ 3 * (n : ℝ) := by rw [hr_sq]
              _ = (n : ℝ) ^ 4 := by ring
          rw [this]
        rw [← this]
        exact div_lt_div_of_pos_right hlt hr_pos
      have h64 : (1 / 4 : ℝ) / (n : ℝ) ^ 4 ≤ 1 / 64 := by
        rw [div_le_iff₀ (pow_pos hn_pos 4)]; linarith
      linarith
    have hden_le4 : (u1 + u2 + (v1 + v2)) *
        |(u1 + u2) ^ 2 - (v1 - v2) ^ 2| *
        |(u1 - u2) ^ 2 - (v1 + v2) ^ 2| *
        |(u1 - u2) ^ 2 - (v1 - v2) ^ 2| ≤ 4 :=
      k2_normalized_denom_le_four
        (div_nonneg (by linarith) (le_of_lt hr_pos)) ((div_le_one hr_pos).mpr hx1_le)
        (div_nonneg (by linarith) (le_of_lt hr_pos)) ((div_le_one hr_pos).mpr hx2_le)
        (div_nonneg (by linarith) (le_of_lt hr_pos)) ((div_le_one hr_pos).mpr hy1_le)
        (div_nonneg (by linarith) (le_of_lt hr_pos)) ((div_le_one hr_pos).mpr hy2_le)
        hclose
    have hr7 : r ^ 7 = (n : ℝ) ^ 3 * r := by
      calc r ^ 7 = (r ^ 2) ^ 3 * r := by ring
        _ = (n : ℝ) ^ 3 * r := by rw [hr_sq]
    have hM_abs : |(M : ℝ)| = diff2 a1 a2 b1 b2 * ((n : ℝ) ^ 3 * r) *
        ((u1 + u2 + (v1 + v2)) *
         |(u1 + u2) ^ 2 - (v1 - v2) ^ 2| *
         |(u1 - u2) ^ 2 - (v1 + v2) ^ 2| *
         |(u1 - u2) ^ 2 - (v1 - v2) ^ 2|) := by
      rw [hM_id, ← hr7]
      have hfac1 : (x1 + x2) ^ 2 - (y1 + y2) ^ 2 = ((x1 + x2) - (y1 + y2)) * (x1 + x2 + (y1 + y2)) := by ring
      rw [hfac1, abs_mul, abs_mul, abs_mul, abs_mul]
      have h1 : x1 + x2 + (y1 + y2) = r * (u1 + u2 + (v1 + v2)) := by
        dsimp [u1, u2, v1, v2]; field_simp
      have h2 : (x1 + x2) ^ 2 - (y1 - y2) ^ 2 = r ^ 2 * ((u1 + u2) ^ 2 - (v1 - v2) ^ 2) := by
        dsimp [u1, u2, v1, v2]; field_simp
      have h3 : (x1 - x2) ^ 2 - (y1 + y2) ^ 2 = r ^ 2 * ((u1 - u2) ^ 2 - (v1 + v2) ^ 2) := by
        dsimp [u1, u2, v1, v2]; field_simp
      have h4 : (x1 - x2) ^ 2 - (y1 - y2) ^ 2 = r ^ 2 * ((u1 - u2) ^ 2 - (v1 - v2) ^ 2) := by
        dsimp [u1, u2, v1, v2]; field_simp
      rw [h1, h2, h3, h4, abs_of_pos (mul_pos hr_pos (by
        have : 0 < u1 + u2 + (v1 + v2) := by
          have := hsum_pos; rw [h1] at this; exact (mul_pos_iff_of_pos_left hr_pos).mp this
        exact this)),
        abs_mul, abs_mul, abs_mul, abs_of_pos (pow_pos hr_pos 2)]
      dsimp [diff2, x1, x2, y1, y2]
      ring
    have hden_nn : 0 ≤ (u1 + u2 + (v1 + v2)) *
        |(u1 + u2) ^ 2 - (v1 - v2) ^ 2| *
        |(u1 - u2) ^ 2 - (v1 + v2) ^ 2| *
        |(u1 - u2) ^ 2 - (v1 - v2) ^ 2| := by
      have : 0 ≤ u1 + u2 + (v1 + v2) :=
        add_nonneg (add_nonneg (div_nonneg (by linarith) (le_of_lt hr_pos))
          (div_nonneg (by linarith) (le_of_lt hr_pos)))
          (add_nonneg (div_nonneg (by linarith) (le_of_lt hr_pos))
          (div_nonneg (by linarith) (le_of_lt hr_pos)))
      exact mul_nonneg (mul_nonneg (mul_nonneg this (abs_nonneg _)) (abs_nonneg _)) (abs_nonneg _)
    have hprod_lt : diff2 a1 a2 b1 b2 * ((n : ℝ) ^ 3 * r) < 1 / 4 :=
      (lt_div_iff₀ (mul_pos (pow_pos hn_pos 3) hr_pos)).mp hlt
    have hprod_nn : 0 ≤ diff2 a1 a2 b1 b2 * ((n : ℝ) ^ 3 * r) :=
      mul_nonneg (abs_nonneg _) (le_of_lt (mul_pos (pow_pos hn_pos 3) hr_pos))
    have hM_lt1 : |(M : ℝ)| < 1 := by
      rw [hM_abs]
      calc diff2 a1 a2 b1 b2 * ((n : ℝ) ^ 3 * r) * _
          ≤ diff2 a1 a2 b1 b2 * ((n : ℝ) ^ 3 * r) * 4 :=
            mul_le_mul_of_nonneg_left hden_le4 hprod_nn
        _ < (1 / 4 : ℝ) * 4 := by linarith
        _ = 1 := by norm_num
    linarith

/-- **Theorem (Explicit Constant-Norm Upper Bound Family for `k = 2`).**
    For every `k ≥ 3`, the explicit quadratic family
    `a1 = 16*k^2, a2 = 4*k^2 - 24, b1 = 9*k^2 + 18*k - 9, b2 = 9*k^2 - 18*k - 9`
    has constant algebraic norm `M = 82944` and satisfies `0 < diff2 ≤ 27 / k^7`. -/
theorem k2_upper_bound_family {k : ℕ} (hk : 3 ≤ k) :
    let a1 := 16 * k ^ 2
    let a2 := 4 * k ^ 2 - 24
    let b1 := 9 * k ^ 2 + 18 * k - 9
    let b2 := 9 * k ^ 2 - 18 * k - 9
    1 ≤ a1 ∧ a1 ≤ 16 * k ^ 2 ∧
    1 ≤ a2 ∧ a2 ≤ 16 * k ^ 2 ∧
    1 ≤ b1 ∧ b1 ≤ 16 * k ^ 2 ∧
    1 ≤ b2 ∧ b2 ≤ 16 * k ^ 2 ∧
    0 < diff2 a1 a2 b1 b2 ∧
    diff2 a1 a2 b1 b2 ≤ (27 : ℝ) / (k : ℝ) ^ 7 := by
  intro a1 a2 b1 b2
  have hk2 : 9 ≤ k ^ 2 := by nlinarith only [hk]
  have h18k : 18 * k ≤ 6 * k ^ 2 := by nlinarith only [hk]
  have hk_r : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk_pos : (0 : ℝ) < (k : ℝ) := by linarith
  have ha1_lo : 1 ≤ a1 := by dsimp [a1]; omega
  have ha2_lo : 1 ≤ a2 := by dsimp [a2]; omega
  have hb1_lo : 1 ≤ b1 := by dsimp [b1]; omega
  have hb2_lo : 1 ≤ b2 := by dsimp [b2]; omega
  have ha2_hi : a2 ≤ 16 * k ^ 2 := by dsimp [a2]; omega
  have hb1_hi : b1 ≤ 16 * k ^ 2 := by dsimp [b1]; omega
  have hb2_hi : b2 ≤ 16 * k ^ 2 := by dsimp [b2]; omega
  -- Exact cast to ℝ of a1, a2, b1, b2
  have ca1 : (a1 : ℝ) = 16 * (k : ℝ) ^ 2 := by dsimp [a1]; push_cast; ring
  have ca2 : (a2 : ℝ) = 4 * (k : ℝ) ^ 2 - 24 := by
    dsimp [a2]
    rw [Nat.cast_sub (by omega : 24 ≤ 4 * k ^ 2)]; push_cast; ring
  have cb1 : (b1 : ℝ) = 9 * (k : ℝ) ^ 2 + 18 * (k : ℝ) - 9 := by
    dsimp [b1]
    rw [Nat.cast_sub (by omega : 9 ≤ 9 * k ^ 2 + 18 * k)]; push_cast; ring
  have cb2 : (b2 : ℝ) = 9 * (k : ℝ) ^ 2 - 18 * (k : ℝ) - 9 := by
    dsimp [b2]
    have h9 : 9 ≤ 9 * k ^ 2 - 18 * k := by omega
    have h18 : 18 * k ≤ 9 * k ^ 2 := by omega
    rw [Nat.cast_sub h9, Nat.cast_sub h18]; push_cast; ring
  -- Exact norm M = 82944!
  set M : ℤ := (((a1 : ℤ) + a2 - b1 - b2) ^ 2 - 4 * a1 * a2 - 4 * b1 * b2) ^ 2
                - 64 * a1 * a2 * b1 * b2
  have hM_val : (M : ℝ) = 82944 := by
    dsimp [M]; push_cast; rw [ca1, ca2, cb1, cb2]; ring
  set x1 := Real.sqrt a1
  set x2 := Real.sqrt a2
  set y1 := Real.sqrt b1
  set y2 := Real.sqrt b2
  have hM_id : (82944 : ℝ) = ((x1 + x2) ^ 2 - (y1 + y2) ^ 2) * ((x1 + x2) ^ 2 - (y1 - y2) ^ 2) *
      ((x1 - x2) ^ 2 - (y1 + y2) ^ 2) * ((x1 - x2) ^ 2 - (y1 - y2) ^ 2) := by
    rw [← hM_val]; exact k2_norm_identity a1 a2 b1 b2
  have hdiff_pos : 0 < diff2 a1 a2 b1 b2 := by
    by_contra h
    have h0 : diff2 a1 a2 b1 b2 = 0 := le_antisymm (not_lt.mp h) (abs_nonneg _)
    have heq : x1 + x2 = y1 + y2 := sub_eq_zero.mp (abs_eq_zero.mp h0)
    rw [heq] at hM_id
    norm_num at hM_id
  -- Simple bounds on x1, x2, y1, y2 for k ≥ 3
  have hx1_eq : x1 = 4 * (k : ℝ) := by
    dsimp [x1]; rw [ca1]
    have : 16 * (k : ℝ) ^ 2 = (4 * (k : ℝ)) ^ 2 := by ring
    rw [this, Real.sqrt_sq (by linarith)]
  have hx2_lo : (k : ℝ) ≤ x2 := by
    dsimp [x2]; rw [ca2, Real.le_sqrt (by linarith) (by nlinarith only [hk_r])]; nlinarith only [hk_r]
  have hx2_hi : x2 ≤ 2 * (k : ℝ) := by
    dsimp [x2]; rw [ca2, Real.sqrt_le_left (by linarith)]; nlinarith only [hk_r]
  have hy1_lo : 3 * (k : ℝ) ≤ y1 := by
    dsimp [y1]; rw [cb1, Real.le_sqrt (by linarith) (by nlinarith only [hk_r])]; nlinarith only [hk_r]
  have hy1_hi : y1 ≤ 4 * (k : ℝ) := by
    dsimp [y1]; rw [cb1, Real.sqrt_le_left (by linarith)]; nlinarith only [hk_r]
  have hy2_lo : (4 / 3 : ℝ) * (k : ℝ) ≤ y2 := by
    dsimp [y2]; rw [cb2, Real.le_sqrt (by linarith) (by nlinarith only [hk_r])]; nlinarith only [hk_r]
  have hy2_hi : y2 ≤ 3 * (k : ℝ) := by
    dsimp [y2]; rw [cb2, Real.sqrt_le_left (by linarith)]; nlinarith only [hk_r]
  -- Bound the 4 factors from below
  have hf_sum : (9 : ℝ) * (k : ℝ) ≤ x1 + x2 + (y1 + y2) := by linarith
  have hy_diff_le : |y1 - y2| ≤ (8 / 3 : ℝ) * (k : ℝ) := abs_le.mpr ⟨by linarith, by linarith⟩
  have hy_diff_sq : (y1 - y2) ^ 2 ≤ (64 / 9 : ℝ) * (k : ℝ) ^ 2 := by
    rw [← sq_abs]
    have := pow_le_pow_left₀ (abs_nonneg (y1 - y2)) hy_diff_le 2
    linarith [show ((8 / 3 : ℝ) * (k : ℝ)) ^ 2 = (64 / 9 : ℝ) * (k : ℝ) ^ 2 by ring]
  have hf2 : (17 : ℝ) * (k : ℝ) ^ 2 ≤ (x1 + x2) ^ 2 - (y1 - y2) ^ 2 := by
    have hx_sum : 5 * (k : ℝ) ≤ x1 + x2 := by linarith
    have hx_sq : (25 : ℝ) * (k : ℝ) ^ 2 ≤ (x1 + x2) ^ 2 := by
      have := pow_le_pow_left₀ (by linarith) hx_sum 2
      linarith [show (5 * (k : ℝ)) ^ 2 = 25 * (k : ℝ) ^ 2 by ring]
    linarith
  have hf3 : (9 : ℝ) * (k : ℝ) ^ 2 ≤ (y1 + y2) ^ 2 - (x1 - x2) ^ 2 := by
    have hy_sum : (13 / 3 : ℝ) * (k : ℝ) ≤ y1 + y2 := by linarith
    have hy_sq : (169 / 9 : ℝ) * (k : ℝ) ^ 2 ≤ (y1 + y2) ^ 2 := by
      have := pow_le_pow_left₀ (by linarith) hy_sum 2
      linarith [show ((13 / 3 : ℝ) * (k : ℝ)) ^ 2 = (169 / 9 : ℝ) * (k : ℝ) ^ 2 by ring]
    have hxd_lo : 0 ≤ x1 - x2 := by linarith
    have hxd_hi : x1 - x2 ≤ 3 * (k : ℝ) := by linarith
    have hxd_sq : (x1 - x2) ^ 2 ≤ 9 * (k : ℝ) ^ 2 := by
      have := pow_le_pow_left₀ hxd_lo hxd_hi 2
      linarith [show (3 * (k : ℝ)) ^ 2 = 9 * (k : ℝ) ^ 2 by ring]
    linarith
  have hf4 : (7 / 3 : ℝ) * (k : ℝ) ^ 2 ≤ (x1 - x2) ^ 2 - (y1 - y2) ^ 2 := by
    have hsq1 : x1 ^ 2 = (a1 : ℝ) := Real.sq_sqrt (Nat.cast_nonneg a1)
    have hsq2 : x2 ^ 2 = (a2 : ℝ) := Real.sq_sqrt (Nat.cast_nonneg a2)
    have hsq3 : y1 ^ 2 = (b1 : ℝ) := Real.sq_sqrt (Nat.cast_nonneg b1)
    have hsq4 : y2 ^ 2 = (b2 : ℝ) := Real.sq_sqrt (Nat.cast_nonneg b2)
    have hid : (x1 - x2) ^ 2 - (y1 - y2) ^ 2 = 2 * (k : ℝ) ^ 2 - 6 + 2 * (y1 * y2 - x1 * x2) := by
      have hdiff_ab : (a1 : ℝ) + a2 - b1 - b2 = 2 * (k : ℝ) ^ 2 - 6 := by
        rw [ca1, ca2, cb1, cb2]; ring
      linear_combination hsq1 + hsq2 - hsq3 - hsq4 + hdiff_ab
    have h98 : (9 / 8 : ℝ) * (x1 * x2) ≤ y1 * y2 := by
      have hsq : ((9 / 8 : ℝ) * (x1 * x2)) ^ 2 ≤ (y1 * y2) ^ 2 := by
        have h1 : (x1 * x2) ^ 2 = 64 * (k : ℝ) ^ 4 - 384 * (k : ℝ) ^ 2 := by
          rw [mul_pow, hsq1, hsq2, ca1, ca2]; ring
        have h2 : (y1 * y2) ^ 2 = 81 * (k : ℝ) ^ 4 - 486 * (k : ℝ) ^ 2 + 81 := by
          rw [mul_pow, hsq3, hsq4, cb1, cb2]; ring
        rw [mul_pow, h1, h2]
        linarith
      have hnn1 : 0 ≤ (9 / 8 : ℝ) * (x1 * x2) :=
        mul_nonneg (by norm_num) (mul_nonneg (Real.sqrt_nonneg a1) (Real.sqrt_nonneg a2))
      have hnn2 : 0 ≤ y1 * y2 := mul_nonneg (Real.sqrt_nonneg b1) (Real.sqrt_nonneg b2)
      nlinarith only [hsq, hnn1, hnn2]
    have hxy_lo : 4 * (k : ℝ) ^ 2 ≤ x1 * x2 := by
      rw [hx1_eq]
      have := mul_le_mul_of_nonneg_left hx2_lo (by linarith : (0 : ℝ) ≤ 4 * (k : ℝ))
      linarith [show 4 * (k : ℝ) * (k : ℝ) = 4 * (k : ℝ) ^ 2 by ring]
    have hk2_r : (9 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith only [hk_r]
    linarith
  have hden_ge : (3213 : ℝ) * (k : ℝ) ^ 7 ≤
      (x1 + x2 + (y1 + y2)) *
      |(x1 + x2) ^ 2 - (y1 - y2) ^ 2| *
      |(x1 - x2) ^ 2 - (y1 + y2) ^ 2| *
      |(x1 - x2) ^ 2 - (y1 - y2) ^ 2| := by
    have hk2_pos : 0 ≤ (k : ℝ) ^ 2 := sq_nonneg _
    have h2pos : 0 ≤ (x1 + x2) ^ 2 - (y1 - y2) ^ 2 := by linarith
    have h3pos : 0 ≤ (y1 + y2) ^ 2 - (x1 - x2) ^ 2 := by linarith
    have h4pos : 0 ≤ (x1 - x2) ^ 2 - (y1 - y2) ^ 2 := by linarith
    rw [abs_of_nonneg h2pos, abs_sub_comm ((x1 - x2) ^ 2), abs_of_nonneg h3pos, abs_of_nonneg h4pos]
    have hp1 : (9 * (k : ℝ)) * (17 * (k : ℝ) ^ 2) ≤
        (x1 + x2 + (y1 + y2)) * ((x1 + x2) ^ 2 - (y1 - y2) ^ 2) :=
      mul_le_mul hf_sum hf2 (by positivity) (by linarith)
    have hp2 : (9 * (k : ℝ) ^ 2) * ((7 / 3 : ℝ) * (k : ℝ) ^ 2) ≤
        ((y1 + y2) ^ 2 - (x1 - x2) ^ 2) * ((x1 - x2) ^ 2 - (y1 - y2) ^ 2) :=
      mul_le_mul hf3 hf4 (by positivity) (by positivity)
    have hp3 := mul_le_mul hp1 hp2 (by positivity) (by positivity)
    linarith [show ((9 * (k : ℝ)) * (17 * (k : ℝ) ^ 2)) *
        ((9 * (k : ℝ) ^ 2) * ((7 / 3 : ℝ) * (k : ℝ) ^ 2)) = 3213 * (k : ℝ) ^ 7 by ring]
  have hM_abs : (82944 : ℝ) = diff2 a1 a2 b1 b2 *
      ((x1 + x2 + (y1 + y2)) *
       |(x1 + x2) ^ 2 - (y1 - y2) ^ 2| *
       |(x1 - x2) ^ 2 - (y1 + y2) ^ 2| *
       |(x1 - x2) ^ 2 - (y1 - y2) ^ 2|) := by
    have h1 := congrArg abs hM_id
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 82944)] at h1
    have hfac1 : (x1 + x2) ^ 2 - (y1 + y2) ^ 2 =
        ((x1 + x2) - (y1 + y2)) * (x1 + x2 + (y1 + y2)) := by ring
    rw [hfac1, abs_mul, abs_mul, abs_mul, abs_mul,
        abs_of_pos (by linarith : 0 < x1 + x2 + (y1 + y2))] at h1
    dsimp [diff2, x1, x2, y1, y2]
    linarith
  have hdiff_le : diff2 a1 a2 b1 b2 ≤ (27 : ℝ) / (k : ℝ) ^ 7 := by
    rw [le_div_iff₀ (pow_pos hk_pos 7)]
    have h1 : diff2 a1 a2 b1 b2 * ((3213 : ℝ) * (k : ℝ) ^ 7) ≤ 82944 := by
      rw [hM_abs]
      exact mul_le_mul_of_nonneg_left hden_ge (abs_nonneg _)
    linarith [show diff2 a1 a2 b1 b2 * ((3213 : ℝ) * (k : ℝ) ^ 7) =
        3213 * (diff2 a1 a2 b1 b2 * (k : ℝ) ^ 7) by ring]
  exact ⟨ha1_lo, le_refl _, ha2_lo, ha2_hi, hb1_lo, hb1_hi, hb2_lo, hb2_hi, hdiff_pos, hdiff_le⟩

/-- **Theorem (Global Upper Bound for `k = 2`).**
    For every `n ≥ 144`, there exist `1 ≤ a1, a2, b1, b2 ≤ n` such that
    `0 < diff2 a1 a2 b1 b2 ≤ 2^22 / (n^3 * √n)`. -/
theorem k2_upper_bound {n : ℕ} (hn : 144 ≤ n) :
    ∃ a1 a2 b1 b2 : ℕ,
      1 ≤ a1 ∧ a1 ≤ n ∧ 1 ≤ a2 ∧ a2 ≤ n ∧
      1 ≤ b1 ∧ b1 ≤ n ∧ 1 ≤ b2 ∧ b2 ≤ n ∧
      0 < diff2 a1 a2 b1 b2 ∧
      diff2 a1 a2 b1 b2 ≤ (4194304 : ℝ) / ((n : ℝ) ^ 3 * Real.sqrt n) := by
  set k := Nat.sqrt (n / 16)
  have hk_ge3 : 3 ≤ k := by
    dsimp [k]
    rw [Nat.le_sqrt]
    omega
  have h16k2_le : 16 * k ^ 2 ≤ n := by
    have hk2 : k * k ≤ n / 16 := Nat.sqrt_le (n / 16)
    have : k ^ 2 = k * k := sq k
    omega
  have h16k1_gt : n < 16 * (k + 1) ^ 2 := by
    have hk1 : n / 16 < (k + 1) * (k + 1) := Nat.lt_succ_sqrt (n / 16)
    have : (k + 1) ^ 2 = (k + 1) * (k + 1) := sq (k + 1)
    omega
  have hf := k2_upper_bound_family hk_ge3
  refine ⟨16 * k ^ 2, 4 * k ^ 2 - 24, 9 * k ^ 2 + 18 * k - 9, 9 * k ^ 2 - 18 * k - 9,
    hf.1, le_trans hf.2.1 h16k2_le,
    hf.2.2.1, le_trans hf.2.2.2.1 h16k2_le,
    hf.2.2.2.2.1, le_trans hf.2.2.2.2.2.1 h16k2_le,
    hf.2.2.2.2.2.2.1, le_trans hf.2.2.2.2.2.2.2.1 h16k2_le,
    hf.2.2.2.2.2.2.2.2.1, ?_⟩
  have hdiff_k := hf.2.2.2.2.2.2.2.2.2
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
  have hr_pos : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn_pos
  have hn_le_sharp : (n : ℝ) ≤ (256 / 9 : ℝ) * (k : ℝ) ^ 2 := by
    have h1 : (n : ℝ) < 16 * ((k : ℝ) + 1) ^ 2 := by exact_mod_cast h16k1_gt
    have hk3 : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_ge3
    nlinarith only [h1, hk3]
  have hr_le_sharp : Real.sqrt n ≤ (16 / 3 : ℝ) * (k : ℝ) := by
    rw [Real.sqrt_le_left (by positivity)]
    linarith [show ((16 / 3 : ℝ) * (k : ℝ)) ^ 2 = (256 / 9 : ℝ) * (k : ℝ) ^ 2 by ring]
  have hpow7 : (n : ℝ) ^ 3 * Real.sqrt n ≤ ((16 / 3 : ℝ) * (k : ℝ)) ^ 7 := by
    have hr7 : (n : ℝ) ^ 3 * Real.sqrt n = (Real.sqrt n) ^ 7 := by
      have hsq : Real.sqrt n ^ 2 = (n : ℝ) := Real.sq_sqrt (le_of_lt hn_pos)
      calc (n : ℝ) ^ 3 * Real.sqrt n = (Real.sqrt n ^ 2) ^ 3 * Real.sqrt n := by rw [hsq]
        _ = (Real.sqrt n) ^ 7 := by ring
    rw [hr7]
    exact pow_le_pow_left₀ (le_of_lt hr_pos) hr_le_sharp 7
  have hstep : (27 : ℝ) / (k : ℝ) ^ 7 ≤ (4194304 : ℝ) / ((n : ℝ) ^ 3 * Real.sqrt n) := by
    rw [div_le_div_iff₀ (pow_pos hk_pos 7) (mul_pos (pow_pos hn_pos 3) hr_pos)]
    have hnum : (27 : ℝ) * ((16 / 3 : ℝ) * (k : ℝ)) ^ 7 ≤ 4194304 * (k : ℝ) ^ 7 := by
      have hk7 : 0 ≤ (k : ℝ) ^ 7 := by positivity
      have hconst : (27 : ℝ) * (16 / 3 : ℝ) ^ 7 ≤ 4194304 := by norm_num
      calc (27 : ℝ) * ((16 / 3 : ℝ) * (k : ℝ)) ^ 7
          = ((27 : ℝ) * (16 / 3 : ℝ) ^ 7) * (k : ℝ) ^ 7 := by ring
        _ ≤ 4194304 * (k : ℝ) ^ 7 := mul_le_mul_of_nonneg_right hconst hk7
    linarith [mul_le_mul_of_nonneg_left hpow7 (by norm_num : (0 : ℝ) ≤ 27)]
  exact le_trans hdiff_k hstep

end SumOfSquareRoots
