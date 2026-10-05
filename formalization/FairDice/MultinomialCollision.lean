import Mathlib

namespace FairDice

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def multinomialMass (_d : ℕ) (u : ι → ℝ) (a : ι → ℕ) : ℝ :=
  (Nat.multinomial Finset.univ a : ℝ) * ∏ j, u j ^ a j

noncomputable def multinomialCollision (d : ℕ) (u : ι → ℝ) : ℝ :=
  ∑ a ∈ Finset.piAntidiag Finset.univ d, (multinomialMass d u a)^2

omit [DecidableEq ι] in
theorem multinomialMass_nonneg (d : ℕ) (u : ι → ℝ) (hu : ∀ j, 0 ≤ u j) (a : ι → ℕ) :
    0 ≤ multinomialMass d u a := by
  exact mul_nonneg (Nat.cast_nonneg _) (Finset.prod_nonneg (fun j _ => pow_nonneg (hu j) _))

theorem multinomialMass_sum (d : ℕ) (u : ι → ℝ) (hu : ∑ j, u j = 1) :
    (∑ a ∈ Finset.piAntidiag Finset.univ d, multinomialMass d u a) = 1 := by
  unfold multinomialMass
  rw [← Finset.sum_pow_eq_sum_piAntidiag, hu, one_pow]

omit [DecidableEq ι] in
theorem multinomialMass_factorial (d : ℕ) (u : ι → ℝ) (a : ι → ℕ)
    (ha : ∑ j, a j = d) :
    multinomialMass d u a = (d.factorial : ℝ) / (∏ j, (a j).factorial : ℝ) * ∏ j, u j ^ a j := by
  have hspec := Nat.multinomial_spec Finset.univ a
  rw [ha] at hspec
  have hfac : (0 : ℝ) < (∏ j, (a j).factorial : ℝ) := by
    exact_mod_cast Finset.prod_pos (fun j _ => Nat.factorial_pos (a j))
  unfold multinomialMass
  congr 1
  apply (eq_div_iff (ne_of_gt hfac)).mpr
  have hh : (∏ j, (a j).factorial : ℝ) * (Nat.multinomial Finset.univ a : ℝ) = d.factorial := by
    exact_mod_cast hspec
  nlinarith

/-- Collision probability is bounded by any bound on the individual masses. -/
theorem multinomialCollision_le_max (d : ℕ) (u : ι → ℝ)
    (hu0 : ∀ j, 0 ≤ u j) (hu : ∑ j, u j = 1) (B : ℝ)
    (hB : ∀ a ∈ Finset.piAntidiag Finset.univ d, multinomialMass d u a ≤ B) :
    multinomialCollision d u ≤ B := by
  unfold multinomialCollision
  calc
    _ ≤ ∑ a ∈ Finset.piAntidiag Finset.univ d, B * multinomialMass d u a := by
      apply Finset.sum_le_sum
      intro a ha
      rw [sq]
      exact mul_le_mul_of_nonneg_right (hB a ha) (multinomialMass_nonneg d u hu0 a)
    _ = B := by rw [← Finset.mul_sum, multinomialMass_sum d u hu, mul_one]

theorem multinomialCollision_le_one (d : ℕ) (u : ι → ℝ)
    (hu0 : ∀ j, 0 ≤ u j) (hu : ∑ j, u j = 1) : multinomialCollision d u ≤ 1 := by
  apply multinomialCollision_le_max d u hu0 hu 1
  intro a ha
  rw [← multinomialMass_sum d u hu]
  exact Finset.single_le_sum (fun b _ => multinomialMass_nonneg d u hu0 b) ha

noncomputable def poissonMass (rate : ℝ) (k : ℕ) : ℝ := Real.exp (-rate) * rate^k / k.factorial

omit [DecidableEq ι] in
/-- The conditioning identity underlying the paper's collision estimate,
proved from the literal multinomial and Poisson mass formulae. -/
theorem poisson_multinomial_identity (d : ℕ) (u : ι → ℝ)
    (hu : ∑ j, u j = 1) (a : ι → ℕ) (ha : ∑ j, a j = d) :
    (∏ j, poissonMass (d * u j) (a j)) =
      poissonMass d d * multinomialMass d u a := by
  have he : (∏ j, Real.exp (-(d * u j))) = Real.exp (-(d : ℝ)) := by
    rw [← Real.exp_sum]
    congr 1
    calc
      (∑ j, -(d * u j)) = -(d : ℝ) * (∑ j, u j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = -(d : ℝ) := by rw [hu, mul_one]
  have hp : (∏ j, (d : ℝ)^(a j)) = (d : ℝ)^d := by
    rw [Finset.prod_pow_eq_pow_sum, ha]
  have hprod : (∏ j, poissonMass (d * u j) (a j)) =
      (∏ j, Real.exp (-(d * u j))) * (∏ j, (d : ℝ)^(a j)) *
        (∏ j, u j ^ a j) / (∏ j, (a j).factorial : ℝ) := by
    simp [poissonMass, Finset.prod_mul_distrib, Finset.prod_div_distrib, mul_pow]
    ring
  rw [hprod, he, hp, multinomialMass_factorial d u a ha]
  unfold poissonMass
  have hf : (d.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (Nat.factorial_pos d)
  field_simp

end FairDice
