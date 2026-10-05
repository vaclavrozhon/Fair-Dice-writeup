import FairDice.TensorCancellation
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.MeasureTheory.Integral.DominatedConvergence

namespace FairDice

open MeasureTheory Set

noncomputable def correctionPrimitive (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..t, f x

theorem local_interval_integrable {f : ℝ → ℝ} (hf : LocallyIntegrable f volume)
    (a b : ℝ) : IntervalIntegrable f volume a b :=
  intervalIntegrable_iff.mpr ((hf.integrableOn_isCompact isCompact_uIcc).mono_set uIoc_subset_uIcc)

theorem correctionPrimitive_continuous {f : ℝ → ℝ} (hf : LocallyIntegrable f volume) :
    Continuous (correctionPrimitive f) :=
  intervalIntegral.continuous_primitive (local_interval_integrable hf) 0

theorem correctionPrimitive_local {f : ℝ → ℝ} (hf : LocallyIntegrable f volume) :
    LocallyIntegrable (correctionPrimitive f) volume :=
  (correctionPrimitive_continuous hf).locallyIntegrable

theorem local_mul_continuous {f g : ℝ → ℝ} (hf : LocallyIntegrable f volume)
    (hg : Continuous g) : LocallyIntegrable (fun x => f x*g x) volume := by
  rw [← locallyIntegrableOn_univ] at hf ⊢
  exact hf.mul_continuousOn hg.continuousOn isClosed_univ.isLocallyClosed

theorem local_const_mul {f : ℝ → ℝ} (hf : LocallyIntegrable f volume) (c : ℝ) :
    LocallyIntegrable (fun x => c*f x) volume := by
  convert local_mul_continuous hf (continuous_const : Continuous (fun _ : ℝ => c)) using 1
  funext x
  ring

@[simp] theorem correctionPrimitive_zero (f : ℝ → ℝ) : correctionPrimitive f 0=0 := by
  simp [correctionPrimitive]

/-- Integration by parts for the primitive of an integrable correction.
This avoids any smoothness assumption on its piecewise constant density. -/
theorem correctionPrimitive_moment {f : ℝ → ℝ} (hf : LocallyIntegrable f volume)
    (t : ℝ) (k : ℕ) :
    (k+1 : ℝ)*(∫ x in (0 : ℝ)..t, correctionPrimitive f x*x^k) =
      correctionPrimitive f t*t^(k+1) - (∫ x in (0 : ℝ)..t, f x*x^(k+1)) := by
  have hF := (local_interval_integrable hf 0 t).absolutelyContinuousOnInterval_intervalIntegral
    (c := 0) (by simp)
  have hg : AbsolutelyContinuousOnInterval (fun x : ℝ => x^(k+1)) 0 t :=
    (contDiff_id.pow (k+1)).contDiffOn.absolutelyContinuousOnInterval
  have hd (x : ℝ) : deriv (fun x : ℝ => x^(k+1)) x=(k+1 : ℝ)*x^k := by
    simpa using ((hasDerivAt_id x).pow (k+1)).deriv
  have hh := hF.integral_mul_deriv_eq_deriv_mul hg
  simp only [hd,intervalIntegral.integral_same,zero_mul,sub_zero] at hh
  have hder : (∫ x in (0 : ℝ)..t, deriv (correctionPrimitive f) x*x^(k+1)) =
      ∫ x in (0 : ℝ)..t, f x*x^(k+1) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [LocallyIntegrable.ae_hasDerivAt_integral hf] with x hx _
    change deriv (fun x => ∫ (v : ℝ) in (0 : ℝ)..x, f v) x*x^(k+1)=f x*x^(k+1)
    rw [(hx 0).deriv]
  change (∫ x in (0 : ℝ)..t, correctionPrimitive f x*((k+1 : ℝ)*x^k)) =
    correctionPrimitive f t*t^(k+1) -
      (∫ x in (0 : ℝ)..t, deriv (correctionPrimitive f) x*x^(k+1)) at hh
  rw [hder] at hh
  have he (x : ℝ) : correctionPrimitive f x*((k+1 : ℝ)*x^k)=
      (k+1 : ℝ)*(correctionPrimitive f x*x^k) := by ring
  simp_rw [he] at hh
  rwa [intervalIntegral.integral_const_mul] at hh

/-- Full vanishing moments pass to the primitive with one degree lost. -/
theorem correctionPrimitive_moment_zero {f : ℝ → ℝ} (hf : LocallyIntegrable f volume)
    (t : ℝ) (k : ℕ) (h0 : correctionPrimitive f t=0)
    (hk : (∫ x in (0 : ℝ)..t, f x*x^(k+1))=0) :
    (∫ x in (0 : ℝ)..t, correctionPrimitive f x*x^k)=0 := by
  have hh := correctionPrimitive_moment hf t k
  rw [h0,hk] at hh
  have hpos : (0 : ℝ)<k+1 := by positivity
  nlinarith

/-- A centered compact correction retains its support when integrated.
Consequently products with corrections in other disjoint intervals vanish. -/
theorem correctionPrimitive_support {f : ℝ → ℝ} {L R : ℝ}
    (hL : 0 ≤ L) (hR : R ≤ 1) (hLR : L < R)
    (hs : Function.support f ⊆ Ioo L R)
    (hzero : (∫ x in (0 : ℝ)..1, f x)=0) :
    Function.support (correctionPrimitive f) ⊆ Ioo L R := by
  intro t ht
  by_contra hnot
  have hz : correctionPrimitive f t=0 := by
    by_cases hbefore : t ≤ L
    · unfold correctionPrimitive
      calc
        _ = ∫ x in (0 : ℝ)..t, (0 : ℝ) := intervalIntegral.integral_congr (by
          intro x hx
          by_contra hxf
          have hxs := hs hxf
          have hxL : x ≤ L := hx.2.trans (max_le hL hbefore)
          exact (not_lt_of_ge hxL) hxs.1)
        _ = 0 := by simp
    · have htR : R ≤ t := by
        simp only [mem_Ioo] at hnot
        push Not at hnot
        exact hnot (by linarith)
      have hs1 : Function.support f ⊆ Ioc 0 1 := fun x hx =>
        ⟨hL.trans_lt (hs hx).1,(hs hx).2.le.trans hR⟩
      have hst : Function.support f ⊆ Ioc 0 t := fun x hx =>
        ⟨hL.trans_lt (hs hx).1,(hs hx).2.le.trans htR⟩
      unfold correctionPrimitive
      rw [intervalIntegral.integral_eq_integral_of_support_subset hst,
        ← intervalIntegral.integral_eq_integral_of_support_subset hs1]
      exact hzero
  exact ht hz

/-- At a cut where the original moments are evaluation at that cut, the
primitive has zero polynomial moments. This eliminates every uniform
coordinate between a correction and the distinguished face. -/
theorem correctionPrimitive_cut_moment {f : ℝ → ℝ} (hf : LocallyIntegrable f volume)
    (t c : ℝ) (k : ℕ) (h0 : correctionPrimitive f t=c)
    (hk : (∫ x in (0 : ℝ)..t, f x*x^(k+1))=c*t^(k+1)) :
    (∫ x in (0 : ℝ)..t, correctionPrimitive f x*x^k)=0 := by
  have hh := correctionPrimitive_moment hf t k
  rw [h0,hk,sub_self] at hh
  have hpos : (0 : ℝ)<k+1 := by positivity
  nlinarith

end FairDice
