import FairDice.Approximation

namespace FairDice

theorem descents_of_decreasing {n : ℕ} (p : List (Fin n))
    (hp : p.Pairwise (fun a b => b < a)) : descents p = p.length - 1 := by
  induction p using descents.induct with
  | case1 => simp [descents]
  | case2 a => simp [descents]
  | case3 a b p ih =>
    have hab : b < a := (List.pairwise_cons.mp hp).1 b (by simp)
    have htail := (List.pairwise_cons.mp hp).2
    simp only [descents, if_pos hab, ih htail, List.length_cons]
    omega

theorem decreasing_descents (n : ℕ) : descents (List.finRange n).reverse = n - 1 := by
  have hp : (List.finRange n).reverse.Pairwise (fun a b => b < a) := by
    rw [List.pairwise_reverse]
    exact (List.sortedLT_finRange n).pairwise
  simpa using descents_of_decreasing _ hp

theorem decreasing_probability (hext : PPartitionExternal) {n m : ℕ} (hn : 0 < n) :
    patternProbability (periodicWord n m) (List.finRange n).reverse =
      (m.choose n : ℚ) / (m : ℚ)^n := by
  rw [periodic_probability_formula hext hn _ (by simp [List.nodup_finRange]) (by simp), decreasing_descents]
  have he : m + n - 1 - (n - 1) = m := by omega
  rw [he]

theorem decreasingRatio_upper {n m : ℕ} (hn : 0 < n) (hm : n ≤ m) :
    shuffleRatio n m (n - 1) ≤ Real.exp (-(n : ℝ) * (n - 1 : ℝ) / (2 * m)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnmR : (n : ℝ) ≤ m := by exact_mod_cast hm
  have hshift : ((n - 1 : ℕ) : ℝ) = n - 1 := by simpa using (Nat.cast_sub (R := ℝ) hn)
  calc
    _ ≤ ∏ k ∈ Finset.range n, Real.exp (((k : ℝ) - (n - 1 : ℕ)) / m) := by
      apply Finset.prod_le_prod
      · intro k _
        rw [hshift]
        have hk : (0 : ℝ) ≤ k := by positivity
        have he : 1 + ((k : ℝ) - (n - 1 : ℝ)) / m = (m + k - (n - 1 : ℝ)) / m := by
          field_simp
          ring
        rw [he]
        exact div_nonneg (by nlinarith) hmR.le
      · intro k _
        simpa [add_comm] using Real.add_one_le_exp (((k : ℝ) - (n - 1 : ℕ)) / m)
    _ = Real.exp (∑ k ∈ Finset.range n, (((k : ℝ) - (n - 1 : ℕ)) / m)) :=
      (Real.exp_sum _ _).symm
    _ = _ := by
      congr 1
      rw [← Finset.sum_div, Finset.sum_sub_distrib, sum_range_cast, hshift]
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring

/-- The logarithmic necessary bound for this particular periodic family.
Only the decreasing permutation is needed to force it. -/
theorem periodic_faces_necessary (hext : PPartitionExternal) {n m : ℕ}
    (hn : 2 ≤ n) (hm : 0 < m) {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1)
    (happrox : |(patternProbability (periodicWord n m) (List.finRange n).reverse : ℝ) -
      1 / (n.factorial : ℝ)| ≤ ε / (n.factorial : ℝ)) :
    n ≤ m ∧ (n : ℝ) * (n - 1 : ℝ) / (2 * (-Real.log (1 - ε))) ≤ m := by
  have hn0 : 0 < n := by omega
  have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hlow : 1 - ε ≤ (n.factorial : ℝ) *
      (patternProbability (periodicWord n m) (List.finRange n).reverse : ℝ) := by
    have hh := (abs_le.mp happrox).1
    have hmul := mul_le_mul_of_nonneg_right hh hfac.le
    field_simp at hmul
    nlinarith
  have hnm : n ≤ m := by
    by_contra hbad
    rw [decreasing_probability hext hn0, Nat.choose_eq_zero_of_lt (by omega)] at hlow
    norm_num at hlow
    linarith
  refine ⟨hnm, ?_⟩
  have hratio : (n.factorial : ℝ) *
      (patternProbability (periodicWord n m) (List.finRange n).reverse : ℝ) =
      shuffleRatio n m (n - 1) := by
    rw [periodic_probability_formula hext hn0 _ (by simp [List.nodup_finRange]) (by simp), decreasing_descents]
    push_cast
    rw [← mul_div_assoc]
    exact choose_eq_shuffleRatio hn0 hnm (by omega)
  rw [hratio] at hlow
  have hexp := hlow.trans (decreasingRatio_upper hn0 hnm)
  have hlog := Real.log_le_log (show 0 < 1 - ε by linarith) hexp
  rw [Real.log_exp] at hlog
  have hlogneg : Real.log (1 - ε) < 0 := by
    have := Real.log_lt_log (show 0 < 1 - ε by linarith) (show 1 - ε < 1 by linarith)
    simpa using this
  apply (div_le_iff₀ (by linarith : 0 < 2 * -Real.log (1 - ε))).mpr
  have hh := (le_div_iff₀ (by positivity : 0 < (2 : ℝ) * m)).mp hlog
  nlinarith

/-- The explicit quadratic scale claimed below the logarithmic bound. -/
theorem periodic_faces_quadratic_necessary (hext : PPartitionExternal) {n m : ℕ}
    (hn : 2 ≤ n) (hm : 0 < m) {ε : ℝ} (hε : 0 < ε) (hεhalf : ε ≤ 1 / 2)
    (happrox : |(patternProbability (periodicWord n m) (List.finRange n).reverse : ℝ) -
      1 / (n.factorial : ℝ)| ≤ ε / (n.factorial : ℝ)) :
    (n : ℝ)^2 / (8 * ε) ≤ m := by
  have hε1 : ε < 1 := by linarith
  have hb := (periodic_faces_necessary hext hn hm hε hε1 happrox).2
  have hpos : 0 < 1 - ε := by linarith
  have hl := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
  rw [Real.log_inv] at hl
  have hi : (1 - ε)⁻¹ - 1 ≤ 2 * ε := by
    apply (sub_le_iff_le_add).mpr
    rw [inv_eq_one_div, div_le_iff₀ hpos]
    nlinarith
  have hlogneg := Real.log_neg hpos (show 1 - ε < 1 by linarith)
  have hb' := (div_le_iff₀ (by linarith : 0 < 2 * -Real.log (1 - ε))).mp hb
  have hmR : (0 : ℝ) ≤ m := by positivity
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  apply (div_le_iff₀ (by positivity : 0 < 8 * ε)).mpr
  nlinarith [mul_le_mul_of_nonneg_left (hl.trans hi) hmR]

end FairDice
