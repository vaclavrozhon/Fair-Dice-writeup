import Mathlib

namespace FairDice

open Polynomial

/-- The rational integral from zero to `N`, defined coefficient by coefficient.
Keeping this functional rational makes common-denominator claims literal. -/
noncomputable def polynomialIntegral (N : ℚ) : ℚ[X] →ₗ[ℚ] ℚ :=
  Polynomial.lsum fun j => (N ^ (j + 1) / (j + 1 : ℚ)) • LinearMap.id

@[simp] theorem polynomialIntegral_monomial (N a : ℚ) (j : ℕ) :
    polynomialIntegral N (monomial j a) = a * N ^ (j + 1) / (j + 1 : ℚ) := by
  simp [polynomialIntegral, Polynomial.lsum_apply, Polynomial.sum_monomial_index]
  ring

@[simp] theorem polynomialIntegral_one (N : ℚ) : polynomialIntegral N 1 = N := by
  simpa using polynomialIntegral_monomial N 1 0

/-- The rational coefficient functional is the usual real interval integral. -/
theorem polynomialIntegral_eq_integral (N : ℚ) (p : ℚ[X]) :
    (polynomialIntegral N p : ℝ) =
      ∫ x in (0 : ℝ)..(N : ℝ), (p.map (Rat.castHom ℝ)).eval x := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, Rat.cast_add, Polynomial.map_add, eval_add]
    rw [intervalIntegral.integral_add
      ((p.map (Rat.castHom ℝ)).continuous.intervalIntegrable 0 (N : ℝ))
      ((q.map (Rat.castHom ℝ)).continuous.intervalIntegrable 0 (N : ℝ)), hp, hq]
  | monomial j a =>
    simp [intervalIntegral.integral_const_mul, mul_div_assoc]

/-- The discrete projection weights in Equation (3.10). -/
noncomputable def projectionWeight {ι η : Type*} [Fintype ι]
    (Q : ι → ℚ[X]) (node : η → ℚ) (H : ι → ℚ) (L : ℚ[X] →ₗ[ℚ] ℚ)
    (i : η) : ℚ := ∑ k, L (Q k) / H k * (Q k).eval (node i)

variable {ι η : Type*} [Fintype ι] [Fintype η] [DecidableEq ι]

/-- Discrete orthogonality makes the projection exact on each basis element. -/
theorem projection_exact_basis (Q : ι → ℚ[X]) (node : η → ℚ) (H : ι → ℚ)
    (L : ℚ[X] →ₗ[ℚ] ℚ) (hH : ∀ k, H k ≠ 0)
    (horth : ∀ k l, ∑ i, (Q k).eval (node i) * (Q l).eval (node i) =
      if k = l then H k else 0) (l : ι) :
    ∑ i, projectionWeight Q node H L i * (Q l).eval (node i) = L (Q l) := by
  simp only [projectionWeight, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [mul_assoc, ← Finset.mul_sum, horth]
  simp [hH]

/-- Exactness extends to the entire span. This proves the algebraic part of
Proposition 3.4 without assuming its conclusion. -/
theorem projection_exact_span (Q : ι → ℚ[X]) (node : η → ℚ) (H : ι → ℚ)
    (L : ℚ[X] →ₗ[ℚ] ℚ) (hH : ∀ k, H k ≠ 0)
    (horth : ∀ k l, ∑ i, (Q k).eval (node i) * (Q l).eval (node i) =
      if k = l then H k else 0)
    (p : ℚ[X]) (hp : p ∈ Submodule.span ℚ (Set.range Q)) :
    ∑ i, projectionWeight Q node H L i * p.eval (node i) = L p := by
  induction hp using Submodule.span_induction with
  | mem p hp =>
    obtain ⟨k, rfl⟩ := hp
    exact projection_exact_basis Q node H L hH horth k
  | zero => simp
  | add p q _ _ hp hq => simp [mul_add, Finset.sum_add_distrib, hp, hq]
  | smul a p _ hp =>
    simp only [eval_smul, smul_eq_mul, map_smul]
    simpa only [Finset.mul_sum, mul_assoc, mul_left_comm] using congrArg (a * ·) hp

omit [Fintype η] [DecidableEq ι] in
/-- Clearing denominators of the individual projection terms clears their sum. -/
theorem clear_projection_denominator (Q : ι → ℚ[X]) (node : η → ℚ) (H : ι → ℚ)
    (L : ℚ[X] →ₗ[ℚ] ℚ) (M : ℕ)
    (h : ∀ k i, ∃ z : ℤ, (M : ℚ) * (L (Q k) / H k * (Q k).eval (node i)) = z) :
    ∀ i, ∃ z : ℤ, (M : ℚ) * projectionWeight Q node H L i = z := by
  classical
  intro i
  choose z hz using fun k => h k i
  refine ⟨∑ k, z k, ?_⟩
  simp only [projectionWeight, Finset.mul_sum, hz, Int.cast_sum]

/-- A strictly positive rational number that becomes integral after scaling
is represented by a positive natural number. -/
theorem positive_integer_weight {M : ℕ} (hM : 0 < M) {w : ℚ} (hw : 0 < w)
    (h : ∃ z : ℤ, (M : ℚ) * w = z) : ∃ k : ℕ, 0 < k ∧ (k : ℚ) = M * w := by
  obtain ⟨z, hz⟩ := h
  have hzpos : 0 < z := by exact_mod_cast (hz ▸ mul_pos (Nat.cast_pos.mpr hM) hw)
  refine ⟨z.toNat, by omega, ?_⟩
  have hi : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hzpos.le
  have hiq : (z.toNat : ℚ) = (z : ℚ) := by exact_mod_cast hi
  exact hiq.trans hz.symm

end FairDice
