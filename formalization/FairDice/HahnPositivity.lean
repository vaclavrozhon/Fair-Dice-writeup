import FairDice.Hahn

namespace FairDice

def gridSize (n : ℕ) : ℕ := n * (n + 2)

theorem gridSize_add_one (n : ℕ) : gridSize n + 1 = (n + 1)^2 := by
  unfold gridSize
  ring

theorem le_gridSize (n : ℕ) : n ≤ gridSize n := by
  unfold gridSize
  nlinarith

theorem hahn_nodal_bound (h : HahnExternal) {n k : ℕ} (hk : k ≤ n)
    (i : Fin (gridSize n + 1)) : |(hahn (gridSize n) k).eval (i.val : ℚ)| ≤ 1 := by
  apply h.zaremba
  unfold gridSize
  nlinarith

/-- The numerical consequence of Wilson's estimate used by the paper. -/
theorem hahn_integral_bound (h : HahnExternal) {n k : ℕ}
    (hkpos : 1 ≤ k) (hkn : k ≤ n) : |hahnIntegral (gridSize n) k| < 3 / 2 := by
  by_cases hodd : Odd k
  · rw [h.wilson_odd _ _ (hkn.trans (le_gridSize n)) hodd]
    norm_num
  have heven : Even k := (Nat.even_or_odd k).resolve_right hodd
  have hk2 : 2 ≤ k := by
    obtain ⟨j, hj⟩ := heven
    omega
  have hn2 : 2 ≤ n := hk2.trans hkn
  have hN8 : 8 ≤ gridSize n := by unfold gridSize; nlinarith
  have hN1 : 1 ≤ gridSize n := by omega
  have hsquare : (k + 1)^2 ≤ gridSize n + 1 := by
    rw [gridSize_add_one]
    exact Nat.pow_le_pow_left (by omega) _
  obtain ⟨hneg, hupper⟩ := h.wilson_even _ _ hN1 hk2
    (hkn.trans (le_gridSize n)) heven hsquare
  rw [abs_of_neg (by linarith)]
  have hNpos : (0 : ℚ) < gridSize n := by exact_mod_cast (show 0 < gridSize n by omega)
  have hNm1 : (0 : ℚ) < gridSize n - 1 := by
    have : (8 : ℚ) ≤ gridSize n := by exact_mod_cast hN8
    linarith
  have hratio : ((gridSize n : ℚ) + 1) / gridSize n ≤ 9 / 8 := by
    apply (div_le_iff₀ hNpos).mpr
    have : (8 : ℚ) ≤ gridSize n := by exact_mod_cast hN8
    linarith
  have hnum : ((k : ℚ) - 1) * (k + 2) < gridSize n - 1 := by
    have hkn' : (k : ℚ) ≤ n := by exact_mod_cast hkn
    have hn2' : (2 : ℚ) ≤ n := by exact_mod_cast hn2
    have hgrid : (gridSize n : ℚ) = (n : ℚ) * (n + 2) := by simp [gridSize]
    nlinarith [mul_nonneg (sub_nonneg.mpr hkn') (show (0 : ℚ) ≤ n + k + 1 by positivity)]
  have hfrac : ((k : ℚ) - 1) * (k + 2) / (4 * (gridSize n - 1 : ℚ)) < 1 / 4 := by
    apply (div_lt_iff₀ (mul_pos (by norm_num) hNm1)).mpr
    linarith
  have hratio0 : (0 : ℚ) < ((gridSize n : ℚ) + 1) / gridSize n := by positivity
  nlinarith

/-- Sum of the bounds for the even, nonconstant Hahn coefficients. -/
def evenLinearSum (n : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), if 0 < k ∧ Even k then 2 * k + 1 else 0

theorem evenLinearSum_even (m : ℕ) : evenLinearSum (2 * m) = 2 * m^2 + 3 * m := by
  induction m with
  | zero => simp [evenLinearSum]
  | succ m ih =>
    have hlen : 2 * (m + 1) + 1 = (2 * m + 1) + 1 + 1 := by omega
    rw [evenLinearSum, hlen, Finset.sum_range_succ, Finset.sum_range_succ]
    change evenLinearSum (2 * m) + _ + _ = _
    rw [ih]
    simp [show ¬Even (2 * m + 1) from (Nat.not_even_iff_odd).mpr ⟨m, rfl⟩,
      show Even (2 * m + 1 + 1) from ⟨m + 1, by omega⟩]
    ring

theorem evenLinearSum_odd (m : ℕ) : evenLinearSum (2 * m + 1) = 2 * m^2 + 3 * m := by
  have h := evenLinearSum_even m
  unfold evenLinearSum at h ⊢
  rw [Finset.sum_range_succ, h]
  simp [show ¬Even (2 * m + 1) from (Nat.not_even_iff_odd).mpr ⟨m, rfl⟩]

theorem evenLinearSum_bound (n : ℕ) : 2 * evenLinearSum n ≤ n * (n + 3) := by
  rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
  · have hn : n = 2 * m := by omega
    rw [hn, evenLinearSum_even]
    nlinarith
  · rw [hm, evenLinearSum_odd]
    nlinarith

theorem hahn_term_bound (h : HahnExternal) {n k : ℕ} (hkpos : 1 ≤ k) (hkn : k ≤ n)
    (i : Fin (gridSize n + 1)) :
    |hahnIntegral (gridSize n) k / hahnNorm (gridSize n) k *
      (hahn (gridSize n) k).eval (i.val : ℚ)| ≤
      3 / (2 * ((gridSize n : ℚ) + 1)) * (2 * k + 1) := by
  have hkN := hkn.trans (le_gridSize n)
  have hH := hahnNorm_pos h hkN
  have hlower := hahnNorm_lower h hkN
  have hI := (hahn_integral_bound h hkpos hkn).le
  have hQ := hahn_nodal_bound h hkn i
  have hd : (0 : ℚ) < ((gridSize n : ℚ) + 1) / (2 * k + 1) := by positivity
  rw [abs_mul, abs_div, abs_of_pos hH]
  calc
    _ ≤ (3 / 2) / hahnNorm (gridSize n) k * 1 :=
      mul_le_mul (div_le_div_of_nonneg_right hI hH.le) hQ (abs_nonneg _) (by positivity)
    _ ≤ (3 / 2) / (((gridSize n : ℚ) + 1) / (2 * k + 1)) := by
      rw [mul_one]
      exact div_le_div_of_nonneg_left (by norm_num) hd hlower
    _ = _ := by field_simp

/-- A lower bound obtained by summing the even coefficient bounds. -/
theorem hahnWeight_lower (h : HahnExternal) (n : ℕ) (i : Fin (gridSize n + 1)) :
    ((gridSize n : ℚ) - 3 / 2 * evenLinearSum n) / ((gridSize n : ℚ) + 1) ≤
      hahnWeight (gridSize n) n i := by
  let N := gridSize n
  let c : ℚ := 3 / (2 * ((N : ℚ) + 1))
  let baseline : ℚ := N / ((N : ℚ) + 1)
  have hterm (k : ℕ) (hk : k ∈ Finset.range (n + 1)) :
      (if k = 0 then baseline else 0) -
        c * ((if 0 < k ∧ Even k then 2 * k + 1 else 0 : ℕ) : ℚ) ≤
      hahnIntegral N k / hahnNorm N k * (hahn N k).eval (i.val : ℚ) := by
    have hkn : k ≤ n := by simpa using Finset.mem_range.mp hk
    by_cases hk0 : k = 0
    · subst k; simp [baseline]
    · by_cases heven : Even k
      · have ht := hahn_term_bound h (by omega) hkn i
        have hneg := (abs_le.mp ht).1
        simpa [hk0, heven, show 0 < k by omega, c, N] using hneg
      · have hodd := (Nat.even_or_odd k).resolve_left heven
        simp [hk0, heven, h.wilson_odd N k (hkn.trans (le_gridSize n)) hodd]
  have hsum := Finset.sum_le_sum hterm
  have hleft :
      (∑ k ∈ Finset.range (n + 1), ((if k = 0 then baseline else 0) -
        c * ((if 0 < k ∧ Even k then 2 * k + 1 else 0 : ℕ) : ℚ))) =
      baseline - c * evenLinearSum n := by
    simp [Finset.sum_sub_distrib, Finset.mul_sum, evenLinearSum, Nat.cast_sum]
  rw [hleft] at hsum
  have hright : (∑ k ∈ Finset.range (n + 1),
      hahnIntegral N k / hahnNorm N k * (hahn N k).eval (i.val : ℚ)) =
      hahnWeight N n i := by
    exact (Fin.sum_univ_eq_sum_range (fun k =>
      hahnIntegral N k / hahnNorm N k * (hahn N k).eval (i.val : ℚ)) (n + 1)).symm
  rw [hright] at hsum
  have halgebra : baseline - c * evenLinearSum n =
      ((N : ℚ) - 3 / 2 * evenLinearSum n) / ((N : ℚ) + 1) := by
    dsimp [baseline, c]
    field_simp
  rwa [halgebra] at hsum

/-- Strict positivity in Proposition 3.4. The hypothesis consists only of
the explicitly cited classical Hahn facts. -/
theorem hahnWeight_pos (h : HahnExternal) {n : ℕ} (hn : 1 ≤ n)
    (i : Fin (gridSize n + 1)) : 0 < hahnWeight (gridSize n) n i := by
  by_cases hn1 : n = 1
  · subst n
    have hI : hahnIntegral 3 1 = 0 := h.wilson_odd 3 1 (by omega) (by decide)
    change 0 < ∑ k : Fin 2, hahnIntegral 3 k.val / hahnNorm 3 k.val *
      (hahn 3 k.val).eval (i.val : ℚ)
    rw [Fin.sum_univ_two]
    norm_num [hI]
  · have hn2 : 2 ≤ n := by omega
    have hsum : (2 : ℚ) * evenLinearSum n ≤ (n : ℚ) * (n + 3) := by
      exact_mod_cast evenLinearSum_bound n
    have hn2' : (2 : ℚ) ≤ n := by exact_mod_cast hn2
    have hgrid : (gridSize n : ℚ) = (n : ℚ) * (n + 2) := by simp [gridSize]
    have hnum : (0 : ℚ) < gridSize n - 3 / 2 * evenLinearSum n := by
      nlinarith [sq_nonneg ((n : ℚ) - 1)]
    exact lt_of_lt_of_le (div_pos hnum (by positivity)) (hahnWeight_lower h n i)

end FairDice
