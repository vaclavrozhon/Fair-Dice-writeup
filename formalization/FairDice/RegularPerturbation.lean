import FairDice.PerturbationDirection
import Mathlib.Analysis.Calculus.Deriv.Prod

namespace FairDice

open Set Filter
open scoped Topology

/-- The analytic compensating map admits distinct interior nodes while
preserving its first moments. Endpoint motion and every collision are
checked for the actual map, not taken as an additional assumption. -/
theorem regular_moment_perturbation {m K : ℕ} (hK : 0<K) (e : Fin m ↪ Fin K)
    (u : Fin K → ℝ) (hu : Function.Injective (fun j => u (e j)))
    (hpiv : ∀ j, 0<u (e j) ∧ u (e j)<1)
    (hunit : ∀ q, 0≤u q ∧ u q≤1) :
    ∃ w : Fin K → ℝ, Function.Injective w ∧ (∀ q, 0<w q ∧ w q<1) ∧
      rawMomentMap (m := m) w = rawMomentMap (m := m) u := by
  obtain ⟨P⟩ := moment_perturbation_exists hK e u hu
  obtain ⟨v,hv,hsep⟩ := separating_inward_direction hK e u hu
  let w : ℝ → Fin K → ℝ := fun a => P.nodes (a • v)
  have hd : HasDerivAt w (nodeTangent e u v) 0 := by
    simpa [w,Function.comp_def] using P.nodes_hasFDerivAt.comp_hasDerivAt_of_eq 0
      ((hasDerivAt_id (0 : ℝ)).smul_const v) (by simp)
  have hdq (q : Fin K) : HasDerivAt (fun a => w a q) (nodeTangent e u v q) 0 :=
    hasDerivAt_pi.mp hd q
  have hw0 : w 0=u := by simp [w]
  have hpair (q r : Fin K) : ∀ᶠ a in nhdsWithin 0 (Ioi (0 : ℝ)), q≠r → w a q≠w a r := by
    by_cases hqr : q=r
    · exact Filter.Eventually.of_forall (fun _ h => (h hqr).elim)
    by_cases hval : u q=u r
    · have hs : nodeTangent e u v q-nodeTangent e u v r ≠ 0 := hsep q r hqr hval
      have hh := (hdq q |>.sub (hdq r)).eventually_ne (c := 0) hs
      have hf : nhdsWithin (0 : ℝ) (Ioi 0) ≤ nhdsWithin 0 {0}ᶜ :=
        nhdsWithin_mono _ (fun a ha => by simpa using ne_of_gt ha)
      filter_upwards [hh.filter_mono hf] with a ha _
      exact sub_ne_zero.mp ha
    · have hn : w 0 q-w 0 r≠0 := by simpa [hw0] using sub_ne_zero.mpr hval
      have hh := ((hdq q).continuousAt.sub (hdq r).continuousAt).eventually_ne hn
      filter_upwards [hh.filter_mono nhdsWithin_le_nhds] with a ha _
      exact sub_ne_zero.mp ha
  have hinside (q : Fin K) : ∀ᶠ a in nhdsWithin 0 (Ioi (0 : ℝ)), 0<w a q ∧ w a q<1 := by
    have hlo : ∀ᶠ a in nhdsWithin 0 (Ioi (0 : ℝ)), 0<w a q := by
      by_cases h0 : u q=0
      · have hfree : q ∉ Set.range e := by
          rintro ⟨j,hj⟩
          have hh := (hpiv j).1
          rw [hj,h0] at hh
          exact (lt_irrefl 0) hh
        filter_upwards [self_mem_nhdsWithin] with a ha
        have he : w a q=a*v q := by simp [w,MomentPerturbation.nodes,h0,pivotLift_free e _ q hfree]
        rw [he]
        exact mul_pos ha ((hv q).1 h0)
      · have hh : 0<w 0 q := by rw [hw0]; exact lt_of_le_of_ne (hunit q).1 (Ne.symm h0)
        exact ((hdq q).continuousAt.eventually (eventually_gt_nhds hh)).filter_mono nhdsWithin_le_nhds
    have hhi : ∀ᶠ a in nhdsWithin 0 (Ioi (0 : ℝ)), w a q<1 := by
      by_cases h1 : u q=1
      · have hfree : q ∉ Set.range e := by
          rintro ⟨j,hj⟩
          have hh := (hpiv j).2
          rw [hj,h1] at hh
          exact (lt_irrefl 1) hh
        filter_upwards [self_mem_nhdsWithin] with a ha
        have he : w a q=1+a*v q := by simp [w,MomentPerturbation.nodes,h1,pivotLift_free e _ q hfree]
        rw [he]
        have hn := mul_neg_of_pos_of_neg ha ((hv q).2 h1)
        linarith
      · have hh : w 0 q<1 := by rw [hw0]; exact lt_of_le_of_ne (hunit q).2 h1
        exact ((hdq q).continuousAt.eventually (eventually_lt_nhds hh)).filter_mono nhdsWithin_le_nhds
    exact hlo.and hhi
  have hm : ∀ᶠ a in nhdsWithin 0 (Ioi (0 : ℝ)), rawMomentMap (m := m) (w a)=rawMomentMap u := by
    have ht : Tendsto (fun a : ℝ => a • v) (nhds 0) (nhds 0) := by
      have hc : Continuous (fun a : ℝ => a • v) := by fun_prop
      simpa only [zero_smul] using hc.tendsto (0 : ℝ)
    exact (ht.eventually P.exact_near).filter_mono nhdsWithin_le_nhds
  have hh := ((Filter.eventually_all.mpr (fun q => Filter.eventually_all.mpr (hpair q))).and
    (Filter.eventually_all.mpr hinside)).and hm
  obtain ⟨a,ha⟩ := hh.exists
  exact ⟨w a,fun q r he => by_contra fun h => ha.1.1 q r h he,ha.1.2,ha.2⟩

end FairDice
