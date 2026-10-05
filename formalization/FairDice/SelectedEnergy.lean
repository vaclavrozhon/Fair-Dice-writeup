import FairDice.SelectedOccupancy
import FairDice.PalindromeLattice

namespace FairDice

/-- Summing the squares of the actual selected-gap marginal weights gives
exactly a scalar prefactor times the multinomial collision probability. -/
theorem selected_gap_squared_sum {ell : ℕ} (m s d M : ℕ) (k : Fin ell → ℕ)
    (g : Fin (ell+1) → ℕ) (hm : 0 < m) (hM : 0 < M) :
    (∑ a ∈ Finset.piAntidiag (Finset.univ : Finset (Fin (ell+1))) d,
      (selectedGapMass m s d k g a)^2) =
      (((s+d).descFactorial s : ℝ)/((m : ℝ)^s*(∏ j, (k j).factorial : ℝ)))^2*
        ((M : ℝ)/m)^(2*d)*multinomialCollision d (fun j => (g j : ℝ)/M) := by
  unfold multinomialCollision
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  rw [selected_gap_mass_formula m s d M k g a hm hM (Finset.mem_piAntidiag.mp ha).1]
  rw [mul_pow,mul_pow,show (((M : ℝ)/m)^d)^2=((M : ℝ)/m)^(2*d) by
    rw [← pow_mul,Nat.mul_comm]]

/-- The lattice bound is now applied to the squared coefficients obtained
by marginalizing actual occupancy weights. -/
theorem selected_lattice_squared_bound (H : PoissonEstimates) (ell m s d M : ℕ)
    (k : Fin ell → ℕ) (hell : 1 ≤ ell) (hm : 0 < m) (hM : d+1 ≤ M) :
    (∑ g ∈ Finset.piAntidiag (Finset.univ : Finset (Fin (ell+1))) M,
      ∑ a ∈ Finset.piAntidiag (Finset.univ : Finset (Fin (ell+1))) d,
        (selectedGapMass m s d k g a)^2) ≤
      (((s+d).descFactorial s : ℝ)/((m : ℝ)^s*(∏ j, (k j).factorial : ℝ)))^2*
        ((M : ℝ)/m)^(2*d)*(108*M/Real.sqrt (d+1 : ℝ))^ell := by
  simp_rw [selected_gap_squared_sum m s d M k _ hm (by omega : 0 < M)]
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (palindrome_lattice_bound H ell d M hell hM) (by positivity)

/-- For short total support the lattice constant becomes `160*m/sqrt n`.
The estimate `108*sqrt 2 < 160` is verified from squared inequalities. -/
theorem short_lattice_constant (n d m M : ℕ) (hn : 0 < n) (hd : n ≤ 2*d)
    (hMm : M ≤ m) : 108*M/Real.sqrt (d+1 : ℝ) ≤ 160*m/Real.sqrt (n : ℝ) := by
  have hn0 : (0 : ℝ)<n := by exact_mod_cast hn
  have hd0 : (0 : ℝ)<d+1 := by positivity
  have hnS := Real.sq_sqrt hn0.le
  have hdS := Real.sq_sqrt hd0.le
  have hcmp : 108*Real.sqrt (n : ℝ) ≤ 160*Real.sqrt (d+1 : ℝ) := by
    have hdn : (n : ℝ) ≤ 2*d := by exact_mod_cast hd
    nlinarith [Real.sqrt_nonneg (n : ℝ),Real.sqrt_nonneg (d+1 : ℝ)]
  apply (div_le_div_iff₀ (Real.sqrt_pos.mpr hd0) (Real.sqrt_pos.mpr hn0)).mpr
  have hmR : (M : ℝ) ≤ m := by exact_mod_cast hMm
  have hh := mul_le_mul_of_nonneg_left hcmp (by positivity : (0 : ℝ) ≤ M)
  have hh' := mul_le_mul_of_nonneg_right hmR (by positivity : (0 : ℝ) ≤ 160*Real.sqrt (d+1 : ℝ))
  nlinarith

end FairDice
