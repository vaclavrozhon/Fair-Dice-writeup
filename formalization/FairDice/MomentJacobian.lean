import FairDice.RealRulePivots
import FairDice.MomentResponse

namespace FairDice

noncomputable def momentJacobian {m K : ℕ} (u : Fin m → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  fun r q => ((r.val+1 : ℝ) / K) * u q ^ r.val

/-- The moment Jacobian at distinct pivots is an invertible scaled
Vandermonde matrix. -/
theorem momentJacobian_isUnit {m K : ℕ} (hK : 0 < K) (u : Fin m → ℝ)
    (hu : Function.Injective u) : IsUnit (momentJacobian (K := K) u) := by
  classical
  let D := Matrix.diagonal (fun r : Fin m => (r.val+1 : ℝ)/K)
  let V := (Matrix.vandermonde u).transpose
  have hD : D.det ≠ 0 := by
    rw [Matrix.det_diagonal]
    apply Finset.prod_ne_zero_iff.mpr
    intro r _
    exact div_ne_zero (by positivity) (by exact_mod_cast Nat.ne_of_gt hK)
  have hV : V.det ≠ 0 := by
    simpa [V] using Matrix.det_vandermonde_ne_zero_iff.mpr hu
  have he : momentJacobian (K := K) u = D*V := by
    ext r q
    simp [momentJacobian, D, V, Matrix.diagonal_mul, Matrix.vandermonde]
  rw [he]
  exact ((Matrix.isUnit_iff_isUnit_det D).mpr (isUnit_iff_ne_zero.mpr hD)).mul
    ((Matrix.isUnit_iff_isUnit_det V).mpr (isUnit_iff_ne_zero.mpr hV))

/-- Equal Jacobian columns force the matching pivot to move with
derivative `-1` when a coinciding free node moves with derivative `1`.
This is the algebraic part of collision avoidance in `individual-real-rule`. -/
theorem matching_pivot_response {m K : ℕ} (hK : 0 < K) (u : Fin m → ℝ)
    (hu : Function.Injective u) (j : Fin m) (v : Fin m → ℝ)
    (hv : (momentJacobian (K := K) u).mulVec v =
      fun r => -(((r.val+1 : ℝ)/K)*u j^r.val)) :
    v = -Pi.single j 1 := by
  have hinj := Matrix.mulVec_injective_iff_isUnit.mpr (momentJacobian_isUnit hK u hu)
  apply hinj
  rw [hv, Matrix.mulVec_neg, Matrix.mulVec_single_one]
  rfl

theorem matching_pivot_collision_derivative {m K : ℕ} (hK : 0 < K) (u : Fin m → ℝ)
    (hu : Function.Injective u) (j : Fin m) (v : Fin m → ℝ)
    (hv : (momentJacobian (K := K) u).mulVec v =
      fun r => -(((r.val+1 : ℝ)/K)*u j^r.val)) :
    v j - 1 = -2 := by
  rw [matching_pivot_response hK u hu j v hv]
  norm_num

end FairDice
