import FairDice.PerturbationTangents
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.Pi

namespace FairDice

open Set Filter
open scoped Topology

/-- Directions that move every initial endpoint strictly inward. -/
def inwardCone {K : ℕ} (u : Fin K → ℝ) : Set (Fin K → ℝ) :=
  {v | ∀ q, (u q=0 → 0<v q) ∧ (u q=1 → v q<0)}

theorem inwardCone_open {K : ℕ} (u : Fin K → ℝ) : IsOpen (inwardCone u) := by
  have hq (q : Fin K) : IsOpen {v : Fin K → ℝ | (u q=0 → 0<v q) ∧ (u q=1 → v q<0)} := by
    by_cases h0 : u q=0 <;> by_cases h1 : u q=1
    · norm_num [h0] at h1
    · simpa [h0,h1] using (isOpen_lt (continuous_const : Continuous (fun _ : Fin K → ℝ => (0 : ℝ))) (continuous_apply q))
    · simpa [h0,h1] using (isOpen_lt (continuous_apply q) (continuous_const : Continuous (fun _ : Fin K → ℝ => (0 : ℝ))))
    · simp [h0,h1]
  have he : inwardCone u = ⋂ q : Fin K, {v | (u q=0 → 0<v q) ∧ (u q=1 → v q<0)} := by
    ext v
    simp only [inwardCone,mem_setOf_eq,mem_iInter]
  rw [he]
  exact isOpen_iInter_of_finite hq

theorem inwardCone_nonempty {K : ℕ} (u : Fin K → ℝ) : (inwardCone u).Nonempty := by
  classical
  refine ⟨fun q => if u q=0 then 1 else -1, fun q => ⟨?_,?_⟩⟩
  · intro h
    simp [h]
  · intro h
    simp [h]

noncomputable def collisionTangent {m K : ℕ} (e : Fin m ↪ Fin K)
    (u : Fin K → ℝ) (q r : Fin K) : (Fin K → ℝ) →L[ℝ] ℝ :=
  ((ContinuousLinearMap.proj q : (Fin K → ℝ) →L[ℝ] ℝ)-(ContinuousLinearMap.proj r)).comp (nodeTangent e u)

/-- Choose one inward direction that separates every initial collision.
This reduces the analytic perturbation to finitely many scalar curves. -/
theorem separating_inward_direction {m K : ℕ} (hK : 0<K) (e : Fin m ↪ Fin K)
    (u : Fin K → ℝ) (hu : Function.Injective (fun j => u (e j))) :
    ∃ v ∈ inwardCone u, ∀ q r, q≠r → u q=u r → collisionTangent e u q r v ≠ 0 := by
  classical
  let C := {qr : Fin K × Fin K // qr.1≠qr.2 ∧ u qr.1=u qr.2}
  obtain ⟨v,hv,hsep⟩ := analytic_avoid_finite_zeros
    (fun qr : C => collisionTangent e u qr.val.1 qr.val.2)
    (U := Set.univ) isPreconnected_univ
    (fun qr => (collisionTangent e u qr.val.1 qr.val.2).analyticOnNhd Set.univ)
    (fun qr => by
      obtain ⟨v,hv⟩ := coinciding_nodes_tangent_nonzero hK e u hu qr.val.1 qr.val.2
        qr.property.1 qr.property.2
      exact ⟨v,Set.mem_univ v,hv⟩)
    (inwardCone_open u) (inwardCone_nonempty u) (Set.subset_univ _)
  exact ⟨v,hv,fun q r hqr hval => hsep ⟨(q,r),hqr,hval⟩⟩

end FairDice
