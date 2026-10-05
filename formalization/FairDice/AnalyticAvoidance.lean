import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.ContDiff.Defs

namespace FairDice

open Set Filter
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A nonzero derivative rules out identically vanishing on any specified
neighborhood. This is the nontriviality check for a pivot/free collision. -/
theorem derivative_nontrivial_on_neighborhood {f : E → ℝ} {a : E} {L : E →L[ℝ] ℝ}
    (hf : HasFDerivAt f L a) (hL : L ≠ 0) {U : Set E} (hU : U ∈ nhds a) :
    ∃ x ∈ U, f x ≠ 0 := by
  by_contra hn
  push Not at hn
  have he : (fun _ : E => (0 : ℝ)) =ᶠ[nhds a] f :=
    Filter.mem_of_superset hU (fun x hx => (hn x hx).symm)
  have hh := hf.congr_of_eventuallyEq he
  exact hL (hh.unique (hasFDerivAt_const (0 : ℝ) a))

private theorem analytic_nonzero_in_open {f : E → ℝ} {U T : Set E}
    (hf : AnalyticOnNhd ℝ f U) (hU : IsPreconnected U)
    (hnot : ∃ x ∈ U, f x ≠ 0) (hTo : IsOpen T) (hT : T.Nonempty) (hTU : T ⊆ U) :
    ∃ x ∈ T, f x ≠ 0 := by
  by_contra hn
  push Not at hn
  obtain ⟨z,hz⟩ := hT
  have he : f =ᶠ[nhds z] 0 := Filter.mem_of_superset (hTo.mem_nhds hz) (fun x hx => hn x hx)
  have hzero := hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hU (hTU hz) he
  obtain ⟨x,hx,hfx⟩ := hnot
  exact hfx (hzero hx)

/-- A finite union of proper analytic zero sets cannot cover a nonempty
open subset of a connected analytic neighborhood. The collision avoidance
step is proved here using mathlib's analytic identity principle. -/
theorem analytic_avoid_finite_zeros {ι : Type*} [Fintype ι]
    (f : ι → E → ℝ) {U T : Set E} (hU : IsPreconnected U)
    (hf : ∀ i, AnalyticOnNhd ℝ (f i) U)
    (hnot : ∀ i, ∃ x ∈ U, f i x ≠ 0)
    (hTo : IsOpen T) (hT : T.Nonempty) (hTU : T ⊆ U) :
    ∃ x ∈ T, ∀ i, f i x ≠ 0 := by
  classical
  have hh (S : Finset ι) : ∀ T : Set E, IsOpen T → T.Nonempty → T ⊆ U →
      ∃ x ∈ T, ∀ i ∈ S, f i x ≠ 0 := by
    induction S using Finset.induction_on with
    | empty =>
      intro T _ hT _
      obtain ⟨x,hx⟩ := hT
      exact ⟨x,hx,by simp⟩
    | @insert i S hi ih =>
      intro T hTo hT hTU
      obtain ⟨x,hx,hfx⟩ := analytic_nonzero_in_open (hf i) hU (hnot i) hTo hT hTU
      let W : Set E := T ∩ {x | f i x ≠ 0}
      have hWo : IsOpen W := isOpen_iff_mem_nhds.mpr (fun y hy =>
        inter_mem (hTo.mem_nhds hy.1) ((hf i y (hTU hy.1)).continuousAt.eventually_ne hy.2))
      obtain ⟨y,hy,hys⟩ := ih W hWo ⟨x,hx,hfx⟩ (fun y hy => hTU hy.1)
      refine ⟨y,hy.1,fun j hj => ?_⟩
      rcases Finset.mem_insert.mp hj with hji | hj
      · subst j
        exact hy.2
      · exact hys j hj
  obtain ⟨x,hx,h⟩ := hh Finset.univ T hTo hT hTU
  exact ⟨x,hx,fun i => h i (Finset.mem_univ i)⟩

end FairDice
