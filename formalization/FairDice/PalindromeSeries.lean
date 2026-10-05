import Mathlib

namespace FairDice

/-- The length series in the short-support calculation. -/
theorem palindrome_length_series (z : ℝ) (hz : |z| < 1) :
    (∑' j : ℕ, ((j+3 : ℕ) : ℝ) * z^(j+3)) = z^3 * (3-2*z) / (1-z)^2 := by
  have hs := hasSum_coe_mul_geometric_of_norm_lt_one (r := z) (by simpa using hz)
  have hh := hs.summable.sum_add_tsum_nat_add 3
  rw [hs.tsum_eq] at hh
  have he : (∑ j ∈ Finset.range 3, (j : ℝ) * z^j) = z + 2*z^2 := by
    norm_num [Finset.sum_range_succ]
  rw [he] at hh
  have hd : 1-z ≠ 0 := by have := (abs_lt.mp hz).2; linarith
  have hcalc : z + 2*z^2 + z^3*(3-2*z)/(1-z)^2 = z/(1-z)^2 := by
    field_simp
    ring
  exact add_left_cancel (hh.trans hcalc.symm)

theorem palindrome_length_series_bound (z : ℝ) (hz0 : 0 ≤ z) (hz : z ≤ 1/2) :
    (∑' j : ℕ, ((j+3 : ℕ) : ℝ) * z^(j+3)) ≤ 8*z^3 := by
  rw [palindrome_length_series z (by rw [abs_of_nonneg hz0]; linarith)]
  have hd : (0 : ℝ) < (1-z)^2 := sq_pos_of_pos (by linarith)
  apply (div_le_iff₀ hd).mpr
  have hh : 3-2*z ≤ 8*(1-z)^2 := by
    nlinarith [mul_nonneg (show 0 ≤ 1-2*z by linarith) (show 0 ≤ 5-4*z by linarith)]
  nlinarith [mul_le_mul_of_nonneg_left hh (pow_nonneg hz0 3)]

/-- The geometric majorant used when each entire block is one variable. -/
theorem palindrome_block_series (z : ℝ) (hz : |z| < 1) :
    (∑' j : ℕ, 2*z^(j+3)) = 2*z^3/(1-z) := by
  have hs := hasSum_geometric_of_abs_lt_one hz
  simp_rw [pow_add]
  rw [tsum_mul_left, tsum_mul_right, hs.tsum_eq]
  ring

theorem palindrome_block_series_bound (z : ℝ) (hz0 : 0 ≤ z) (hz : z ≤ 1/2) :
    (∑' j : ℕ, 2*z^(j+3)) ≤ 4*z^3 := by
  rw [palindrome_block_series z (by rw [abs_of_nonneg hz0]; linarith)]
  apply (div_le_iff₀ (by linarith : (0 : ℝ) < 1-z)).mpr
  nlinarith [mul_nonneg (show 0 ≤ 1-2*z by linarith) (pow_nonneg hz0 3)]

/-- The Cauchy--Schwarz estimate used to sum the long-support chaos terms,
first for finite partial sums. -/
theorem factorial_sqrt_series_partial (A : ℝ) (M : ℕ) :
    (∑ j ∈ Finset.range M, A^j / Real.sqrt (j.factorial : ℝ)) ≤
      Real.sqrt 2 * Real.exp (A^2) := by
  let f : ℕ → ℝ := fun j => 1 / Real.sqrt ((2 : ℝ)^j)
  let g : ℕ → ℝ := fun j => Real.sqrt ((2 : ℝ)^j) * A^j / Real.sqrt (j.factorial : ℝ)
  have hf (j : ℕ) : (f j)^2 = (1/2 : ℝ)^j := by
    simp [f, Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2^j)]
  have hg (j : ℕ) : (g j)^2 = (2*A^2)^j / (j.factorial : ℝ) := by
    simp only [g, div_pow, mul_pow,
      Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2^j),
      Real.sq_sqrt (Nat.cast_nonneg j.factorial)]
    rw [show (A^j)^2 = (A^2)^j by rw [← pow_mul, ← pow_mul, Nat.mul_comm]]
  have hfg (j : ℕ) : f j * g j = A^j / Real.sqrt (j.factorial : ℝ) := by
    dsimp [f, g]
    have h : Real.sqrt ((2 : ℝ)^j) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
    field_simp
  have hs := hasSum_geometric_of_abs_lt_one (r := (1/2 : ℝ)) (by norm_num)
  have hfs : (∑ j ∈ Finset.range M, (f j)^2) ≤ 2 := by
    simp_rw [hf]
    have hh := hs.summable.sum_le_tsum (Finset.range M) (fun j _ => by positivity)
    rw [hs.tsum_eq] at hh
    norm_num at hh
    exact hh
  have hgs : (∑ j ∈ Finset.range M, (g j)^2) ≤ Real.exp (2*A^2) := by
    simp_rw [hg]
    exact Real.sum_le_exp_of_nonneg (by positivity) M
  have hc := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range M) f g
  simp_rw [hfg] at hc
  have hnn : 0 ≤ ∑ j ∈ Finset.range M, (g j)^2 := Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have hsq : (∑ j ∈ Finset.range M, A^j / Real.sqrt (j.factorial : ℝ))^2 ≤
      2 * Real.exp (2*A^2) :=
    hc.trans ((mul_le_mul_of_nonneg_right hfs hnn).trans
      (mul_le_mul_of_nonneg_left hgs (by norm_num)))
  have hr : (Real.sqrt 2 * Real.exp (A^2))^2 = 2 * Real.exp (2*A^2) := by
    rw [mul_pow, Real.sq_sqrt (by norm_num)]
    rw [show 2*A^2 = A^2+A^2 by ring, Real.exp_add]
    ring
  have hn : 0 ≤ Real.sqrt 2 * Real.exp (A^2) := by positivity
  nlinarith

theorem factorial_sqrt_series_bound (A : ℝ) (hA : 0 ≤ A) :
    (∑' j : ℕ, A^j / Real.sqrt (j.factorial : ℝ)) ≤ Real.sqrt 2 * Real.exp (A^2) :=
  Real.tsum_le_of_sum_range_le (fun j => by positivity) (factorial_sqrt_series_partial A)

end FairDice
