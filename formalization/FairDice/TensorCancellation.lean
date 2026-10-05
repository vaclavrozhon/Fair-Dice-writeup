import FairDice.DensityCorrection
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.Algebra.MvPolynomial.Degrees

namespace FairDice

open MeasureTheory

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A low-degree multivariate polynomial integrates to zero against a
product of functions if one coordinate annihilates every required moment.
This is the full-support cancellation used for multi-bump terms. -/
theorem tensor_polynomial_cancellation (μ : ι → Measure ℝ) [∀ i, SigmaFinite (μ i)]
    (h : ι → ℝ → ℝ) (p : MvPolynomial ι ℝ) (r : ι) (m : ℕ)
    (hdeg : p.totalDegree < m)
    (hint : ∀ d ∈ p.support, ∀ i, Integrable (fun x => h i x*x^(d i)) (μ i))
    (hmom : ∀ k < m, (∫ x, h r x*x^k ∂μ r)=0) :
    (∫ x : ι → ℝ, (∏ i, h i (x i))*MvPolynomial.eval x p ∂Measure.pi μ)=0 := by
  have he (x : ι → ℝ) : (∏ i, h i (x i))*MvPolynomial.eval x p =
      ∑ d ∈ p.support, p.coeff d*∏ i, h i (x i)*x i^(d i) := by
    rw [MvPolynomial.eval_eq',Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro d _
    rw [Finset.prod_mul_distrib]
    ring
  simp_rw [he]
  rw [integral_finsetSum _ (fun d hd => (Integrable.fintype_prod_dep (hint d hd)).const_mul (p.coeff d))]
  apply Finset.sum_eq_zero
  intro d hd
  rw [integral_const_mul,integral_fintype_prod_eq_prod (fun i x => h i x*x^(d i))]
  have hr : d r < m := by
    have hs := MvPolynomial.le_totalDegree hd
    have hh : d r ≤ d.sum (fun _ n => n) := Finsupp.single_eval_le_sum (g := fun n : ℕ => n) d rfl (fun n => Nat.zero_le n) r
    exact hh.trans_lt (hs.trans_lt hdeg)
  rw [Finset.prod_eq_zero (Finset.mem_univ r) (hmom (d r) hr),mul_zero]

/-- Integrability against a polynomial is verified for the actual compactly
supported step bump, so tensor cancellation can be applied without a new
regularity assumption on the corrections. -/
theorem CorrectionIntervals.bump_polynomial_integrable {m : ℕ} (I : CorrectionIntervals m)
    (t : ℝ) (p : Polynomial ℝ) :
    Integrable (fun x => I.bump t x*p.eval x) volume := by
  have hL := momentStep_integrable I.leftA I.leftB (I.leftCoefficients t)
    (fun j => by exact_mod_cast (I.left_pos j).le) p
  have hR := momentStep_integrable I.rightA I.rightB (I.rightCoefficients t)
    (fun j => by exact_mod_cast (I.right_pos j).le) p
  convert hL.sub hR using 1
  ext x
  simp [CorrectionIntervals.bump,sub_mul]

/-- Literal integration of several bumps against their reduced polynomial
kernel vanishes as soon as one selected coordinate is uncut. Other
coordinates may be cut on either side of the distinguished value. -/
theorem multi_bump_polynomial_zero {m : ℕ} (I : ι → CorrectionIntervals m)
    (t lo hi : ι → ℝ) (r : ι) (ht : (I r).admissible (t r))
    (hlo : lo r=0) (hhi : hi r=1) (p : MvPolynomial ι ℝ) (hdeg : p.totalDegree < m) :
    (∫ x : ι → ℝ, (∏ i, (I i).bump (t i) (x i))*MvPolynomial.eval x p
      ∂Measure.pi (fun i => volume.restrict (Set.Ioc (lo i) (hi i))))=0 := by
  apply tensor_polynomial_cancellation _ _ p r m hdeg
  · intro d hd i
    change IntegrableOn (fun x => (I i).bump (t i) x*x^(d i)) (Set.Ioc (lo i) (hi i)) volume
    simpa using ((I i).bump_polynomial_integrable (t i) (Polynomial.X^(d i))).integrableOn
  · intro k hk
    rw [hlo,hhi]
    rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
    simpa using (I r).full_moments (t r) ht (Polynomial.X^k) (by simpa using hk)

end FairDice
