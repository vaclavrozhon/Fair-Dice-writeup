import FairDice.MomentMap
import FairDice.AnalyticAvoidance

namespace FairDice

open Filter
open scoped Topology

/-- The actual moment differential is invertible in the pivot directions. -/
theorem pivot_differential_isInvertible {m K : ℕ} (hK : 0 < K) (e : Fin m ↪ Fin K)
    (u : Fin K → ℝ) (hu : Function.Injective (fun j => u (e j))) :
    ((rawMomentDifferential (m := m) u).comp (pivotLift e)).IsInvertible := by
  let M := momentJacobian (K := K) (fun j => u (e j))
  obtain ⟨hM⟩ := (momentJacobian_isUnit hK _ hu).nonempty_invertible
  let A := (M.toLinearEquiv' hM).toContinuousLinearEquiv
  refine ⟨A, ?_⟩
  ext v r
  change M.mulVec v r = rawMomentDifferential u (pivotLift e v) r
  exact (congrFun (pivot_differential_eq e u v) r).symm

/-- A literal analytic compensating map supplied by mathlib's implicit
function theorem. Its parameters perturb all coordinates; pivot changes
compensate to preserve the first `m` moments exactly near zero. -/
structure MomentPerturbation {m K : ℕ} (e : Fin m ↪ Fin K) (u : Fin K → ℝ) where
  response : (Fin K → ℝ) → (Fin m → ℝ)
  base : response 0 = 0
  analytic : AnalyticAt ℝ response 0
  exact_near : ∀ᶠ t in nhds 0,
    rawMomentMap (m := m) (u+t+pivotLift e (response t)) = rawMomentMap (m := m) u
  derivative : HasFDerivAt response
    (-((rawMomentDifferential (m := m) u).comp (pivotLift e)).inverse |>.comp
      (rawMomentDifferential u)) 0

/-- The implicit-function step in `individual-real-rule` is applied to the
actual polynomial moment map; analyticity and nonsingularity are proved,
rather than supplied as external dice-specific assumptions. -/
theorem moment_perturbation_exists {m K : ℕ} (hK : 0 < K) (e : Fin m ↪ Fin K)
    (u : Fin K → ℝ) (hu : Function.Injective (fun j => u (e j))) :
    Nonempty (MomentPerturbation e u) := by
  let F : (Fin K → ℝ) × (Fin m → ℝ) → (Fin m → ℝ) :=
    fun z => rawMomentMap (u+z.1+pivotLift e z.2)
  let D : ((Fin K → ℝ) × (Fin m → ℝ)) →L[ℝ] (Fin K → ℝ) :=
    ContinuousLinearMap.fst ℝ _ _ + (pivotLift e).comp (ContinuousLinearMap.snd ℝ _ _)
  have hg : HasFDerivAt (fun z : (Fin K → ℝ) × (Fin m → ℝ) => u+z.1+pivotLift e z.2)
      D (0,0) := by
    have hfst : HasFDerivAt (Prod.fst : (Fin K → ℝ) × (Fin m → ℝ) → (Fin K → ℝ))
        (ContinuousLinearMap.fst ℝ _ _) (0,0) := hasFDerivAt_fst
    have hsnd : HasFDerivAt (Prod.snd : (Fin K → ℝ) × (Fin m → ℝ) → (Fin m → ℝ))
        (ContinuousLinearMap.snd ℝ _ _) (0,0) := hasFDerivAt_snd
    have hh := ((hasFDerivAt_const u (0 : (Fin K → ℝ) × (Fin m → ℝ))).add hfst).add
      ((pivotLift e).hasFDerivAt.comp (0,0) hsnd)
    convert hh using 1 <;> first | rfl | simp [D]
  have hF : HasFDerivAt F ((rawMomentDifferential (m := m) u).comp D) (0,0) := by
    have hh := (rawMomentMap_hasFDerivAt (m := m) (u+0+pivotLift e 0)).comp (0,0) hg
    simpa [F] using hh
  have hcdf : ContDiffAt ℝ ⊤ F (0,0) := by
    apply (rawMomentMap_contDiff (m := m) (K := K)).contDiffAt.comp (0,0)
    exact (contDiff_const.add contDiff_fst |>.add ((pivotLift e).contDiff.comp contDiff_snd)).contDiffAt
  have h₁ : (fderiv ℝ F (0,0)).comp (ContinuousLinearMap.inl ℝ _ _) = rawMomentDifferential u := by
    rw [hF.fderiv]
    ext v r
    simp [D]
  have h₂ : (fderiv ℝ F (0,0)).comp (ContinuousLinearMap.inr ℝ _ _) =
      (rawMomentDifferential u).comp (pivotLift e) := by
    rw [hF.fderiv]
    ext v r
    simp [D]
  have hi : ((fderiv ℝ F (0,0)).comp (ContinuousLinearMap.inr ℝ _ _)).IsInvertible := by
    rw [h₂]
    exact pivot_differential_isInvertible hK e u hu
  let ψ := hcdf.implicitFunction (by simp) hi
  refine ⟨{ response := ψ
            base := hcdf.implicitFunction_apply_self (by simp) hi
            analytic := (hcdf.contDiffAt_implicitFunction (by simp) hi).analyticAt
            exact_near := ?_
            derivative := ?_ }⟩
  · simpa [F] using hcdf.eventually_apply_implicitFunction (by simp) hi
  · simpa [h₁,h₂] using (hcdf.hasStrictFDerivAt_implicitFunction (by simp) hi).hasFDerivAt

end FairDice
