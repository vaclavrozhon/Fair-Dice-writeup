import FairDice.Quadrature

namespace FairDice

open Polynomial
open scoped Matrix

theorem polynomialIntegral_square_pos (p : ℚ[X]) (hp : p ≠ 0) :
    0 < polynomialIntegral 1 (p * p) := by
  let q := p.map (Rat.castHom ℝ)
  have hq : q ≠ 0 := by simpa [q] using hp
  have hx : ∃ x ∈ Set.Icc (0 : ℝ) 1, q.eval x ≠ 0 := by
    by_contra h
    push Not at h
    apply hq
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply (Set.Icc_infinite (by norm_num : (0 : ℝ) < 1)).mono
    intro x hx
    exact h x hx
  obtain ⟨x, hx, hval⟩ := hx
  have hpos := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (by norm_num : (0 : ℝ) < 1) continuous_const.continuousOn
    (q.continuous.mul q.continuous).continuousOn
    (fun y _ => mul_self_nonneg (q.eval y)) ⟨x, hx, mul_self_pos.mpr hval⟩
  simp only [intervalIntegral.integral_zero] at hpos
  change 0 < ∫ y in (0 : ℝ)..1, q.eval y * q.eval y at hpos
  have he : (polynomialIntegral 1 (p * p) : ℝ) = ∫ y in (0 : ℝ)..1, q.eval y * q.eval y := by
    rw [polynomialIntegral_eq_integral]
    simp [q]
  rw [← he] at hpos
  exact_mod_cast hpos

noncomputable def coefficientPolynomial {r : ℕ} (v : Fin r → ℚ) : ℚ[X] :=
  ∑ i : Fin r, monomial i.val (v i)

theorem coefficientPolynomial_coeff {r : ℕ} (v : Fin r → ℚ) (i : Fin r) :
    (coefficientPolynomial v).coeff i.val = v i := by
  classical
  simp only [coefficientPolynomial, finsetSum_coeff, coeff_monomial]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    have hv : j.val ≠ i.val := fun he => hji (Fin.ext he)
    simp [hv]
  · simp

theorem coefficientPolynomial_ne_zero {r : ℕ} {v : Fin r → ℚ} (hv : v ≠ 0) :
    coefficientPolynomial v ≠ 0 := by
  intro h
  apply hv
  funext i
  have hc := coefficientPolynomial_coeff v i
  rw [h] at hc
  simpa using hc.symm

noncomputable def hilbertMatrix (r : ℕ) : Matrix (Fin r) (Fin r) ℚ :=
  fun i j => 1 / (i.val + j.val + 1 : ℚ)

theorem hilbert_quadratic_form {r : ℕ} (v : Fin r → ℚ) :
    star v ⬝ᵥ (hilbertMatrix r *ᵥ v) =
      polynomialIntegral 1 (coefficientPolynomial v * coefficientPolynomial v) := by
  classical
  simp only [coefficientPolynomial, Finset.sum_mul, Finset.mul_sum, map_sum,
    monomial_mul_monomial, polynomialIntegral_monomial, one_pow, mul_one,
    dotProduct, Matrix.mulVec, hilbertMatrix, Pi.star_apply, star_trivial,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  push_cast
  ring

theorem hilbertMatrix_posDef (r : ℕ) : (hilbertMatrix r).PosDef := by
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  constructor
  · ext i j
    simp [hilbertMatrix, Matrix.conjTranspose_apply, add_comm]
  · intro v hv
    rw [hilbert_quadratic_form]
    exact polynomialIntegral_square_pos _ (coefficientPolynomial_ne_zero hv)

/-- A monomial-moment version of the full-rank beta-flattening argument.
The two bases are related by invertible Bernstein basis transformations. -/
theorem hilbertMatrix_rank (r : ℕ) : (hilbertMatrix r).rank = r := by
  simpa using Matrix.rank_of_isUnit _ (hilbertMatrix_posDef r).isUnit

end FairDice
