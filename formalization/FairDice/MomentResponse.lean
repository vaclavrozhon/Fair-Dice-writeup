import FairDice.Bernstein

namespace FairDice

open Polynomial

/-- Equality on the monomials is enough on the bounded-degree subspace. -/
theorem polynomial_functionals_ext {R : Type*} [Field R]
    (L B : R[X] →ₗ[R] R) (m : ℕ)
    (h : ∀ k ≤ m, L (X^k) = B (X^k))
    (p : R[X]) (hp : p.natDegree ≤ m) : L p = B p := by
  rw [p.as_sum_range_C_mul_X_pow]
  simp only [map_sum]
  apply Finset.sum_congr rfl
  intro k hk
  have hkm : k ≤ m := by have := Finset.mem_range.mp hk; omega
  rw [← smul_eq_C_mul, map_smul, map_smul, h k hkm]

/-- The equal-weight evaluation functional at the rational approximating nodes. -/
noncomputable def nodeAverage {K : ℕ} (t : Fin K → ℚ) : ℚ[X] →ₗ[ℚ] ℚ :=
  (1 / (K : ℚ)) • ∑ q, Polynomial.leval (t q)

@[simp] theorem nodeAverage_apply {K : ℕ} (t : Fin K → ℚ) (p : ℚ[X]) :
    nodeAverage t p = (∑ q, p.eval (t q)) / K := by
  simp [nodeAverage, Polynomial.leval_apply, div_eq_mul_inv, mul_comm]

@[simp] theorem nodeAverage_one {K : ℕ} (t : Fin K → ℚ) (hK : 0 < K) :
    nodeAverage t 1 = 1 := by
  simp [nodeAverage_apply, Nat.ne_of_gt hK]

/-- The correction system `individual-correction-system` repairs all
degree-`m` polynomials, rather than only its specified monomials. -/
theorem derivative_moment_correction {K m : ℕ} (t : Fin K → ℚ) (hK : 0 < K)
    (B : ℚ[X] →ₗ[ℚ] ℚ)
    (hB : ∀ s, 1 ≤ s → s ≤ m →
      B (X^(s-1)) = (1 / (s + 1 : ℚ) - nodeAverage t (X^s)) / s)
    (p : ℚ[X]) (hp : p.natDegree ≤ m) :
    B p.derivative = polynomialIntegral 1 p - nodeAverage t p := by
  let L : ℚ[X] →ₗ[ℚ] ℚ := B.comp Polynomial.derivative -
    (polynomialIntegral 1 - nodeAverage t)
  have hL (s : ℕ) (hs : s ≤ m) : L (X^s) = 0 := by
    change B (derivative (X^s)) - (polynomialIntegral 1 (X^s) - nodeAverage t (X^s)) = 0
    cases s with
    | zero => simp [nodeAverage_one t hK]
    | succ s =>
      have hh := hB (s+1) (by omega) hs
      simp only [Nat.add_sub_cancel] at hh
      rw [derivative_X_pow, ← smul_eq_C_mul, map_smul, Nat.add_sub_cancel, hh]
      simp only [smul_eq_mul]
      have hint : polynomialIntegral 1 (X^(s+1)) = 1 / (s+1+1 : ℚ) := by
        rw [← monomial_one_right_eq_X_pow, polynomialIntegral_monomial]
        simp
      rw [hint]
      have hsQ : (s + 1 : ℚ) ≠ 0 := by positivity
      field_simp
      push_cast
      ring
  have hh := polynomial_functionals_ext L 0 m (by simpa using hL) p hp
  change B p.derivative - (polynomialIntegral 1 p - nodeAverage t p) = 0 at hh
  linarith

/-- If the order-response formula has been proved for the densities, the
moment correction gives the desired uniform value at every rank. This
lemma does not assume existence of densities or the response formula. -/
theorem corrected_rank_probability {K m k : ℕ} (t : Fin K → ℚ) (hK : 0 < K)
    (hk : k ≤ m) (B : ℚ[X] →ₗ[ℚ] ℚ)
    (hB : ∀ s, 1 ≤ s → s ≤ m →
      B (X^(s-1)) = (1 / (s + 1 : ℚ) - nodeAverage t (X^s)) / s) :
    nodeAverage t (rankPolynomial 1 m k) + B (rankPolynomial 1 m k).derivative =
      1 / ((m+1).factorial : ℚ) := by
  rw [derivative_moment_correction t hK B hB _ (rankPolynomial_degree 1 hk)]
  rw [add_sub_cancel, polynomialIntegral_rank 1 (by norm_num) hk, one_pow]

/-- The rational Vandermonde system at distinct nodes always has a
rational solution, for any rational moment discrepancies. -/
theorem rational_vandermonde_correction {m K : ℕ} (hK : 0 < K)
    (t : Fin m → ℚ) (ht : Function.Injective t) (a : Fin m → ℚ) :
    ∃ δ : Fin m → ℚ, ∀ r : Fin m,
      (∑ q, δ q * t q ^ r.val) / K = a r := by
  classical
  let M := (Matrix.vandermonde t).transpose
  have hdet : M.det ≠ 0 := by
    simpa [M] using Matrix.det_vandermonde_ne_zero_iff.mpr ht
  have hunit : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).mpr (isUnit_iff_ne_zero.mpr hdet)
  obtain ⟨δ, hδ⟩ := (Matrix.mulVec_surjective_iff_isUnit.mpr hunit) (fun r => K * a r)
  refine ⟨δ, fun r => ?_⟩
  have hh := congrFun hδ r
  change (∑ q, t q ^ r.val * δ q) = K * a r at hh
  rw [Finset.sum_congr rfl (fun q _ => mul_comm _ _)] at hh
  apply (div_eq_iff (by exact_mod_cast Nat.ne_of_gt hK)).mpr
  simpa [mul_comm] using hh

end FairDice
