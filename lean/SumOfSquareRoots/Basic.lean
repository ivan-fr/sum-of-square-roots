import Mathlib

namespace SumOfSquareRoots

/-- Separation between two sums of 2 square roots of natural numbers. -/
noncomputable def diff2 (a1 a2 b1 b2 : ℕ) : ℝ :=
  |(Real.sqrt a1 + Real.sqrt a2) - (Real.sqrt b1 + Real.sqrt b2)|

/-- Separation between two sums of 3 square roots of natural numbers. -/
noncomputable def diff3 (a1 a2 a3 b1 b2 b3 : ℕ) : ℝ :=
  |(Real.sqrt a1 + Real.sqrt a2 + Real.sqrt a3) -
   (Real.sqrt b1 + Real.sqrt b2 + Real.sqrt b3)|

/-- Degree-6 Taylor polynomial of `sqrt (1 + t)` around `t = 0`. -/
noncomputable def T6 (t : ℝ) : ℝ :=
  1 + (1 / 2 : ℝ) * t - (1 / 8 : ℝ) * t ^ 2 + (1 / 16 : ℝ) * t ^ 3
    - (5 / 128 : ℝ) * t ^ 4 + (7 / 256 : ℝ) * t ^ 5 - (21 / 1024 : ℝ) * t ^ 6

/-- Elementary polynomial enclosure for `sqrt (1 + t)` on `|t| ≤ 1/4`:
    `|sqrt (1 + t) - T6 t| ≤ (1 / 10) * |t| ^ 7`.
    Proved purely by squaring and algebraic factorization (zero calculus). -/
lemma sqrt_one_add_approx {t : ℝ} (ht : |t| ≤ 1 / 4) :
    |Real.sqrt (1 + t) - T6 t| ≤ (1 / 10 : ℝ) * |t| ^ 7 := by
  have ht_lo : -(1 / 4 : ℝ) ≤ t := (abs_le.mp ht).1
  have ht_hi : t ≤ 1 / 4 := (abs_le.mp ht).2
  have h1t : 0 ≤ 1 + t := by linarith
  have hsq_id : T6 t ^ 2 - (1 + t) =
      t ^ 7 * (441 * t ^ 5 - 1176 * t ^ 4 + 2464 * t ^ 3
        - 4928 * t ^ 2 + 10560 * t - 33792) / 1048576 := by
    unfold T6; ring
  have hR_bound : |441 * t ^ 5 - 1176 * t ^ 4 + 2464 * t ^ 3
      - 4928 * t ^ 2 + 10560 * t - 33792| ≤ 40000 := by
    have h2 : |t| ^ 2 ≤ (1 / 4 : ℝ) ^ 2 := by nlinarith [abs_nonneg t]
    have h3 : |t| ^ 3 ≤ (1 / 4 : ℝ) ^ 3 := by nlinarith [abs_nonneg t]
    have h4 : |t| ^ 4 ≤ (1 / 4 : ℝ) ^ 4 := by nlinarith [abs_nonneg t]
    have h5 : |t| ^ 5 ≤ (1 / 4 : ℝ) ^ 5 := by nlinarith [abs_nonneg t]
    have htri : |441 * t ^ 5 - 1176 * t ^ 4 + 2464 * t ^ 3
        - 4928 * t ^ 2 + 10560 * t - 33792| ≤
        441 * |t| ^ 5 + 1176 * |t| ^ 4 + 2464 * |t| ^ 3
        + 4928 * |t| ^ 2 + 10560 * |t| + 33792 := by
      have ha1 := abs_sub (441 * t ^ 5 - 1176 * t ^ 4 + 2464 * t ^ 3 - 4928 * t ^ 2 + 10560 * t) 33792
      have ha2 := abs_add_le (441 * t ^ 5 - 1176 * t ^ 4 + 2464 * t ^ 3 - 4928 * t ^ 2) (10560 * t)
      have ha3 := abs_sub (441 * t ^ 5 - 1176 * t ^ 4 + 2464 * t ^ 3) (4928 * t ^ 2)
      have ha4 := abs_add_le (441 * t ^ 5 - 1176 * t ^ 4) (2464 * t ^ 3)
      have ha5 := abs_sub (441 * t ^ 5) (1176 * t ^ 4)
      simp only [abs_mul, abs_pow, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 441),
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1176),
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2464),
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4928),
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 10560),
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 33792)] at ha1 ha2 ha3 ha4 ha5
      linarith
    linarith
  have hT6_lo : (3 / 4 : ℝ) ≤ T6 t := by
    unfold T6
    have h2 : t ^ 2 ≤ 1 / 16 := by nlinarith
    have h3_lo : -(1 / 64 : ℝ) ≤ t ^ 3 := by
      have : |t ^ 3| ≤ 1 / 64 := by
        rw [abs_pow]
        calc |t| ^ 3 ≤ (1 / 4 : ℝ) ^ 3 := pow_le_pow_left₀ (abs_nonneg t) ht 3
          _ = 1 / 64 := by norm_num
      exact (abs_le.mp this).1
    have h4 : t ^ 4 ≤ 1 / 256 := by nlinarith [sq_nonneg t]
    have h5_lo : -(1 / 1024 : ℝ) ≤ t ^ 5 := by
      have : |t ^ 5| ≤ 1 / 1024 := by
        rw [abs_pow]
        calc |t| ^ 5 ≤ (1 / 4 : ℝ) ^ 5 := pow_le_pow_left₀ (abs_nonneg t) ht 5
          _ = 1 / 1024 := by norm_num
      exact (abs_le.mp this).1
    have h6 : t ^ 6 ≤ 1 / 4096 := by nlinarith [sq_nonneg t, sq_nonneg (t ^ 2)]
    nlinarith
  have hsqrt_lo : (3 / 4 : ℝ) ≤ Real.sqrt (1 + t) := by
    rw [Real.le_sqrt (by norm_num) h1t]; linarith
  have hsum_lo : (3 / 2 : ℝ) ≤ Real.sqrt (1 + t) + T6 t := by linarith
  have hdiff_sq : |Real.sqrt (1 + t) - T6 t| * (Real.sqrt (1 + t) + T6 t) =
      |T6 t ^ 2 - (1 + t)| := by
    have hpos : 0 ≤ Real.sqrt (1 + t) + T6 t := by linarith
    rw [← abs_of_nonneg hpos, ← abs_mul]
    have h1 : (Real.sqrt (1 + t) - T6 t) * (Real.sqrt (1 + t) + T6 t) =
        -(T6 t ^ 2 - (1 + t)) := by
      nlinarith [Real.sq_sqrt h1t]
    rw [h1, abs_neg]
  have habs_rem : |T6 t ^ 2 - (1 + t)| ≤ (40000 / 1048576 : ℝ) * |t| ^ 7 := by
    rw [hsq_id, abs_div, abs_mul, abs_pow, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1048576)]
    have h7 : 0 ≤ |t| ^ 7 := pow_nonneg (abs_nonneg t) 7
    nlinarith
  nlinarith [abs_nonneg (Real.sqrt (1 + t) - T6 t), pow_nonneg (abs_nonneg t) 7]

end SumOfSquareRoots
