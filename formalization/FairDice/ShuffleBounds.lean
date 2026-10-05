import FairDice.Probability

namespace FairDice

noncomputable def shuffleRatio (n m d : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n, (1 + ((k : ℝ) - d) / m)

theorem sum_range_cast (n : ℕ) :
    (∑ k ∈ Finset.range n, (k : ℝ)) = (n : ℝ) * (n - 1 : ℝ) / 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

theorem exp_half_le_one_add {ε : ℝ} (hε : 0 ≤ ε) (hε1 : ε ≤ 1) :
    Real.exp (ε / 2) ≤ 1 + ε := by
  apply (Real.exp_le_two_add_div_two_sub (by positivity : 0 ≤ ε / 2)
    (by linarith)).trans
  apply (div_le_iff₀ (by linarith : 0 < 2 - ε / 2)).mpr
  nlinarith [sq_nonneg ε, mul_nonneg hε (sub_nonneg.mpr hε1)]

/-- The analytic estimate used in the pointwise inverse-shuffle theorem.
The lower estimate uses Bernoulli's inequality; the upper estimate sums the
positive shifts before applying the exponential bound. -/
theorem shuffleRatio_bounds {n m d : ℕ} (hn : 2 ≤ n) (hm : 0 < m)
    (hd : d < n) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hsize : (n : ℝ) * (n - 1 : ℝ) / ε ≤ m) :
    1 - ε ≤ shuffleRatio n m d ∧ shuffleRatio n m d ≤ 1 + ε := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hdR : (d : ℝ) ≤ n - 1 := by
    have : (d : ℝ) + 1 ≤ n := by exact_mod_cast (show d + 1 ≤ n by omega)
    linarith
  have hsize' : (n : ℝ) * (n - 1 : ℝ) ≤ ε * m := by
    have := (div_le_iff₀ hε).mp hsize
    nlinarith
  have hsmall : (n - 1 : ℝ) / m ≤ 1 := by
    apply (div_le_iff₀ hmR).mpr
    nlinarith [mul_le_mul_of_nonneg_right hε1 hmR.le]
  have hnonneg (k : ℕ) : 0 ≤ 1 + ((k : ℝ) - d) / m := by
    have := (div_le_div_iff_of_pos_right hmR).mpr hdR
    have hk : (0 : ℝ) ≤ k := by positivity
    have hk' : 0 ≤ (k : ℝ) / m := by positivity
    rw [sub_div]
    linarith
  constructor
  · calc
      1 - ε ≤ 1 + n * (-(n - 1 : ℝ) / m) := by
        have := (div_le_iff₀ hmR).mpr hsize'
        rw [neg_div, mul_neg, ← mul_div_assoc]
        linarith
      _ ≤ (1 + (-(n - 1 : ℝ) / m))^n := one_add_mul_le_pow (by rw [neg_div]; linarith) n
      _ = ∏ _k ∈ Finset.range n, (1 + (-(n - 1 : ℝ) / m)) := by simp
      _ ≤ shuffleRatio n m d := by
        apply Finset.prod_le_prod (fun _ _ => by rw [neg_div]; linarith)
        intro k _
        apply add_le_add_right
        apply (div_le_div_iff_of_pos_right hmR).mpr
        have : (0 : ℝ) ≤ k := by positivity
        linarith
  · calc
      shuffleRatio n m d ≤ ∏ k ∈ Finset.range n, (1 + (k : ℝ) / m) := by
        apply Finset.prod_le_prod (fun k _ => hnonneg k)
        intro k _
        gcongr
        exact sub_le_self _ (by positivity)
      _ ≤ Real.exp (∑ k ∈ Finset.range n, (k : ℝ) / m) :=
        Real.prod_one_add_le_exp_sum _ (fun _ => by positivity)
      _ = Real.exp ((n : ℝ) * (n - 1 : ℝ) / (2 * m)) := by
        rw [← Finset.sum_div, sum_range_cast]
        congr 1
        ring
      _ ≤ Real.exp (ε / 2) := by
        apply Real.exp_le_exp.mpr
        apply (div_le_iff₀ (by positivity : 0 < (2 : ℝ) * m)).mpr
        nlinarith
      _ ≤ 1 + ε := exp_half_le_one_add hε.le hε1

theorem choose_eq_shuffleRatio {n m d : ℕ} (hn : 0 < n) (hm : n ≤ m) (hd : d < n) :
    (n.factorial : ℝ) * ((m + n - 1 - d).choose n : ℝ) / (m : ℝ)^n =
      shuffleRatio n m d := by
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  rw [← Nat.cast_mul, ← Nat.descFactorial_eq_factorial_mul_choose,
    Nat.descFactorial_eq_prod_range, Nat.cast_prod]
  unfold shuffleRatio
  rw [← Finset.prod_range_reflect (fun k => (1 + ((k : ℝ) - d) / m)) n]
  have hconst : (m : ℝ)^n = ∏ _k ∈ Finset.range n, (m : ℝ) := by simp
  rw [hconst, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro k hk
  have hk' := Finset.mem_range.mp hk
  rw [Nat.cast_sub (by omega : k ≤ m + n - 1 - d),
    Nat.cast_sub (by omega : d ≤ m + n - 1),
    Nat.cast_sub (by omega : 1 ≤ m + n), Nat.cast_add,
    Nat.cast_sub (by omega : k ≤ n - 1), Nat.cast_sub (by omega : 1 ≤ n)]
  push_cast
  field_simp
  ring

end FairDice
