import FairDice.MomentJacobian
import Mathlib.Analysis.Calculus.ImplicitContDiff

namespace FairDice

noncomputable def rawMomentMap {m K : ℕ} (t : Fin K → ℝ) (r : Fin m) : ℝ :=
  (∑ q, t q^(r.val+1))/(K : ℝ)

noncomputable def rawMomentDifferential {m K : ℕ} (u : Fin K → ℝ) :
    (Fin K → ℝ) →L[ℝ] (Fin m → ℝ) :=
  ContinuousLinearMap.pi (fun r => (K : ℝ)⁻¹ •
    ∑ q, (((r.val+1 : ℝ)*u q^r.val) • ContinuousLinearMap.proj q))

/-- Analyticity of the literal finite moment map, including repeated nodes. -/
theorem rawMomentMap_contDiff {m K : ℕ} : ContDiff ℝ ⊤ (rawMomentMap (m := m) (K := K)) := by
  unfold rawMomentMap
  fun_prop

/-- The matrix used in the article is the derivative of the actual moments. -/
theorem rawMomentMap_hasFDerivAt {m K : ℕ} (u : Fin K → ℝ) :
    HasFDerivAt (rawMomentMap (m := m) (K := K)) (rawMomentDifferential u) u := by
  apply hasFDerivAt_pi.mpr
  intro r
  have hq (q : Fin K) : HasFDerivAt (fun t : Fin K → ℝ => t q^(r.val+1))
      (((r.val+1 : ℝ)*u q^r.val) •
        (ContinuousLinearMap.proj q : (Fin K → ℝ) →L[ℝ] ℝ)) u := by
    simpa [nsmul_eq_mul, Nat.cast_add] using
      (hasFDerivAt_apply (𝕜 := ℝ) q u).pow (r.val+1)
  have hd := (HasFDerivAt.fun_sum (u := Finset.univ)
    (fun q _ => hq q)).const_mul ((K : ℝ)⁻¹)
  simpa [rawMomentMap, rawMomentDifferential, ContinuousLinearMap.pi_apply,
    div_eq_mul_inv, mul_comm, Nat.cast_add, nsmul_eq_mul] using hd

noncomputable def pivotLift {m K : ℕ} (e : Fin m ↪ Fin K) :
    (Fin m → ℝ) →L[ℝ] (Fin K → ℝ) :=
  ∑ j, (ContinuousLinearMap.proj j).smulRight (Pi.single (e j) 1)

@[simp] theorem pivotLift_apply {m K : ℕ} (e : Fin m ↪ Fin K) (v : Fin m → ℝ) (q : Fin K) :
    pivotLift e v q = ∑ j, v j * if e j=q then 1 else 0 := by
  simp [pivotLift, Pi.single_apply, smul_eq_mul, eq_comm]

/-- Restricting the moment differential to the selected pivot directions
gives exactly the scaled Vandermonde Jacobian already proved invertible. -/
theorem pivot_differential_eq {m K : ℕ} (e : Fin m ↪ Fin K) (u : Fin K → ℝ)
    (v : Fin m → ℝ) :
    rawMomentDifferential (m := m) u (pivotLift e v) =
      (momentJacobian (K := K) (fun j => u (e j))).mulVec v := by
  funext r
  simp only [rawMomentDifferential, ContinuousLinearMap.pi_apply,
    smul_apply, sum_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, pivotLift_apply,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  simp only [Matrix.mulVec, dotProduct, momentJacobian, div_eq_mul_inv]
  apply Finset.sum_congr rfl
  intro j _
  ring

end FairDice
