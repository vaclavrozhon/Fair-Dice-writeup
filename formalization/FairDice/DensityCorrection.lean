import FairDice.MomentJacobian
import FairDice.RationalIntervals

namespace FairDice

open Polynomial MeasureTheory

noncomputable def momentDiscrepancy {m K : ℕ} (t : Fin K → ℝ) (r : Fin m) : ℝ :=
  (1/(r.val+2 : ℝ) - (∑ q, t q^(r.val+1))/(K : ℝ))/(r.val+1 : ℝ)

noncomputable def selectedMomentMatrix {m K : ℕ} (e : Fin m ↪ Fin K)
    (t : Fin K → ℝ) : Matrix (Fin m) (Fin m) ℝ :=
  (Matrix.vandermonde (fun j => t (e j))).transpose

noncomputable def densityCoefficients {m K : ℕ} (e : Fin m ↪ Fin K)
    (t : Fin K → ℝ) : Fin m → ℝ :=
  (selectedMomentMatrix e t)⁻¹.mulVec (fun r => K * momentDiscrepancy t r)

theorem momentDiscrepancy_continuous {m K : ℕ} (r : Fin m) :
    Continuous (fun t : Fin K → ℝ => momentDiscrepancy t r) := by
  unfold momentDiscrepancy
  fun_prop

theorem momentDiscrepancy_zero {m K : ℕ} (hK : 0 < K) (Q : EqualWeightRealRule K m)
    (r : Fin m) : momentDiscrepancy Q.node r = 0 := by
  have hh := Q.exactness (X^(r.val+1)) (by simp)
  simp only [eval_pow, eval_X, realPolynomialIntegral_X_pow] at hh
  unfold momentDiscrepancy
  rw [hh]
  have hKr : (K : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hK
  push_cast
  field_simp
  ring

theorem densityCoefficients_zero {m K : ℕ} (hK : 0 < K) (Q : EqualWeightRealRule K m)
    (e : Fin m ↪ Fin K) : densityCoefficients e Q.node = 0 := by
  unfold densityCoefficients
  funext q
  simp [momentDiscrepancy_zero hK Q, Matrix.mulVec, dotProduct]

theorem selectedMomentMatrix_continuous {m K : ℕ} (e : Fin m ↪ Fin K) :
    Continuous (selectedMomentMatrix e) := by
  unfold selectedMomentMatrix Matrix.vandermonde
  fun_prop

theorem selectedMomentMatrix_isUnit {m K : ℕ} (e : Fin m ↪ Fin K)
    (t : Fin K → ℝ) (ht : Function.Injective t) : IsUnit (selectedMomentMatrix e t) := by
  have hd : (selectedMomentMatrix e t).det ≠ 0 := by
    simpa [selectedMomentMatrix, Function.comp_def] using Matrix.det_vandermonde_ne_zero_iff.mpr (ht.comp e.injective)
  exact (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hd)

theorem densityCoefficients_continuousAt {m K : ℕ} (e : Fin m ↪ Fin K)
    (u : Fin K → ℝ) (hu : Function.Injective u) (q : Fin m) :
    ContinuousAt (fun t => densityCoefficients e t q) u := by
  have hdet := ((Matrix.isUnit_iff_isUnit_det _).mp (selectedMomentMatrix_isUnit e u hu)).ne_zero
  have hRi : ContinuousAt Ring.inverse (selectedMomentMatrix e u).det := by
    have heq : (Ring.inverse : ℝ → ℝ) = Inv.inv := funext Ring.inverse_eq_inv
    rw [heq]
    exact continuousAt_inv₀ hdet
  have hInv := (continuousAt_matrix_inv _ hRi).comp (selectedMomentMatrix_continuous e).continuousAt
  have hEntry (r : Fin m) : ContinuousAt (fun t => (selectedMomentMatrix e t)⁻¹ q r) u :=
    (continuous_apply r).continuousAt.comp ((continuous_apply q).continuousAt.comp hInv)
  unfold densityCoefficients Matrix.mulVec dotProduct
  exact tendsto_finsetSum _ (fun r _ =>
    (hEntry r).mul (continuousAt_const.mul (momentDiscrepancy_continuous r).continuousAt))

/-- The actual inverse formula solves the correction system; no solution
or vanishing discrepancy is assumed at the rational approximating nodes. -/
theorem densityCoefficients_moments {m K : ℕ} (hK : 0 < K) (e : Fin m ↪ Fin K)
    (t : Fin K → ℝ) (ht : Function.Injective t) (r : Fin m) :
    (∑ q, densityCoefficients e t q * t (e q)^r.val)/(K : ℝ) = momentDiscrepancy t r := by
  have h := congrFun (show (selectedMomentMatrix e t).mulVec (densityCoefficients e t) =
      (fun r => K * momentDiscrepancy t r) by
        unfold densityCoefficients
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
          ((Matrix.isUnit_iff_isUnit_det _).mp (selectedMomentMatrix_isUnit e t ht)), Matrix.one_mulVec]) r
  have he : (∑ q, densityCoefficients e t q * t (e q)^r.val) = K * momentDiscrepancy t r := by
    simpa [Matrix.mulVec, dotProduct, selectedMomentMatrix, Matrix.vandermonde, mul_comm] using h
  rw [he]
  have hKr : (K : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hK
  field_simp

/-- The coefficients from the real inverse formula are rational at rational
distinct nodes. -/
theorem densityCoefficients_rational {m K : ℕ} (hK : 0 < K) (e : Fin m ↪ Fin K)
    (t : Fin K → ℚ) (ht : Function.Injective t) :
    ∃ c : Fin m → ℚ, ∀ q, densityCoefficients e (fun q => (t q : ℝ)) q = c q := by
  let a : Fin m → ℚ := fun r =>
    (1/(r.val+2 : ℚ) - (∑ q, t q^(r.val+1))/(K : ℚ))/(r.val+1 : ℚ)
  obtain ⟨c, hc⟩ := rational_vandermonde_correction hK (fun q => t (e q)) (ht.comp e.injective) a
  have htR : Function.Injective (fun q => (t q : ℝ)) := by
    intro i j hij
    apply ht
    change (t i : ℝ) = (t j : ℝ) at hij
    exact_mod_cast hij
  have ha (r : Fin m) : momentDiscrepancy (fun q => (t q : ℝ)) r = (a r : ℝ) := by
    simp [momentDiscrepancy, a]
  have hinj := Matrix.mulVec_injective_iff_isUnit.mpr
    (selectedMomentMatrix_isUnit e (fun q => (t q : ℝ)) htR)
  have heq : densityCoefficients e (fun q => (t q : ℝ)) = fun q => (c q : ℝ) := by
    apply hinj
    funext r
    change (∑ q, (t (e q) : ℝ)^r.val * densityCoefficients e (fun q => (t q : ℝ)) q) =
      ∑ q, (t (e q) : ℝ)^r.val * (c q : ℝ)
    have h₁ := densityCoefficients_moments hK e (fun q => (t q : ℝ)) htR r
    have h₂ : (∑ q, (c q : ℝ) * (t (e q) : ℝ)^r.val)/(K : ℝ) = (a r : ℝ) := by
      exact_mod_cast hc r
    rw [ha] at h₁
    have hKr : (K : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hK
    have hEq := (div_left_inj' hKr).mp (h₁.trans h₂.symm)
    simpa [mul_comm] using hEq
  exact ⟨c, fun q => congrFun heq q⟩

noncomputable def correctedDensity {m K : ℕ} (e : Fin m ↪ Fin K)
    (I : Fin K → CorrectionIntervals m) (t : Fin K → ℝ) (x : ℝ) : ℝ :=
  1 + ∑ q, densityCoefficients e t q * (I (e q)).bump (t (e q)) x

noncomputable def densityErrorBound {m K : ℕ} (e : Fin m ↪ Fin K)
    (I : Fin K → CorrectionIntervals m) (t : Fin K → ℝ) : ℝ :=
  ∑ q, |densityCoefficients e t q| * (I (e q)).coefficientBound (t (e q))

theorem correctedDensity_error_bound {m K : ℕ} (e : Fin m ↪ Fin K)
    (I : Fin K → CorrectionIntervals m) (t : Fin K → ℝ) (x : ℝ) :
    |correctedDensity e I t x - 1| ≤ densityErrorBound e I t := by
  simp only [correctedDensity, add_sub_cancel_left]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro q _
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left ((I (e q)).bump_bound _ _) (abs_nonneg _)

theorem densityErrorBound_continuousAt {m K : ℕ} (e : Fin m ↪ Fin K)
    (I : Fin K → CorrectionIntervals m) (u : Fin K → ℝ) (hu : Function.Injective u) :
    ContinuousAt (densityErrorBound e I) u := by
  exact tendsto_finsetSum _ (fun q _ =>
    (densityCoefficients_continuousAt e u hu q).abs.mul
      ((I (e q)).coefficientBound_continuous.comp (continuous_apply (e q))).continuousAt)

theorem densityErrorBound_zero {m K : ℕ} (hK : 0 < K) (Q : EqualWeightRealRule K m)
    (e : Fin m ↪ Fin K) (I : Fin K → CorrectionIntervals m) : densityErrorBound e I Q.node = 0 := by
  simp [densityErrorBound, densityCoefficients_zero hK Q e]

/-- Simultaneously approximate all starting nodes by rationals while keeping
every corrected density at least one half. The approximation can be chosen
in any specified open neighborhood (for order, support and node distinctness). -/
theorem positive_rational_density_approximation {ι : Type*} [Fintype ι]
    {m K : ℕ} (hK : 0 < K) (Q : EqualWeightRealRule K m) (hu : Function.Injective Q.node)
    (e : ι → (Fin m ↪ Fin K)) (I : Fin K → CorrectionIntervals m)
    (V : Set (Fin K → ℝ)) (hV : IsOpen V) (huV : Q.node ∈ V) :
    ∃ t : Fin K → ℚ, (fun q => (t q : ℝ)) ∈ V ∧
      ∀ j : ι, ∀ x : ℝ, (1/2 : ℝ) ≤ correctedDensity (e j) I (fun q => (t q : ℝ)) x := by
  have hnear (j : ι) : ∀ᶠ t in nhds Q.node, densityErrorBound (e j) I t < (1/2 : ℝ) :=
    (densityErrorBound_continuousAt (e j) I Q.node hu).eventually_lt continuousAt_const
      (by rw [densityErrorBound_zero hK Q]; norm_num)
  have hAll : ∀ᶠ t in nhds Q.node, ∀ j : ι, densityErrorBound (e j) I t < (1/2 : ℝ) :=
    Filter.eventually_all.mpr hnear
  obtain ⟨W, hWsub, hWo, huW⟩ := mem_nhds_iff.mp hAll
  have hdense : DenseRange (fun t : Fin K → ℚ => fun q => (t q : ℝ)) :=
    DenseRange.piMap (fun _ => Rat.denseRange_cast)
  obtain ⟨t, ht⟩ := hdense.exists_mem_open (hV.inter hWo) ⟨Q.node, huV, huW⟩
  refine ⟨t, ht.1, fun j x => ?_⟩
  have hh := hWsub ht.2 j
  have hbound := (correctedDensity_error_bound (e j) I (fun q => (t q : ℝ)) x).trans hh.le
  have hl := (abs_le.mp hbound).1
  linarith

theorem CorrectionIntervals.bump_integrable {m : ℕ} (I : CorrectionIntervals m) (t : ℝ) :
    Integrable (I.bump t) volume := by
  have hL (j : Fin m) : I.leftA j ≤ I.leftB j := by exact_mod_cast (I.left_pos j).le
  have hR (j : Fin m) : I.rightA j ≤ I.rightB j := by exact_mod_cast (I.right_pos j).le
  have h := (momentStep_integrable I.leftA I.leftB (I.leftCoefficients t) hL (1 : ℝ[X])).sub
    (momentStep_integrable I.rightA I.rightB (I.rightCoefficients t) hR (1 : ℝ[X]))
  convert h using 1
  ext x
  simp [CorrectionIntervals.bump]

theorem correctedDensity_intervalIntegrable {m K : ℕ} (e : Fin m ↪ Fin K)
    (I : Fin K → CorrectionIntervals m) (t : Fin K → ℝ) (a b : ℝ) :
    IntervalIntegrable (correctedDensity e I t) volume a b := by
  exact intervalIntegrable_const.add
    (integrable_finsetSum _ (fun q _ =>
      ((I (e q)).bump_integrable (t (e q))).const_mul (densityCoefficients e t q))).intervalIntegrable

/-- The constructed function has total mass one; normalization is a
consequence of the literal bumps, not a premise about a proposed density. -/
theorem correctedDensity_integral {m K : ℕ} (hm : 0 < m) (e : Fin m ↪ Fin K)
    (I : Fin K → CorrectionIntervals m) (t : Fin K → ℝ)
    (ht : ∀ q, (I q).admissible (t q)) :
    (∫ x in (0 : ℝ)..1, correctedDensity e I t x) = 1 := by
  have hz (q : Fin m) : (∫ x in (0 : ℝ)..1, (I (e q)).bump (t (e q)) x) = 0 := by
    simpa using (I (e q)).full_moments _ (ht _) (1 : ℝ[X]) (by simpa using hm)
  unfold correctedDensity
  rw [intervalIntegral.integral_add intervalIntegrable_const
    (integrable_finsetSum _ (fun q _ =>
      ((I (e q)).bump_integrable (t (e q))).const_mul (densityCoefficients e t q))).intervalIntegrable,
    intervalIntegral.integral_finsetSum (fun q _ =>
      ((I (e q)).bump_integrable _).intervalIntegrable.const_mul _)]
  simp only [intervalIntegral.integral_const_mul, hz]
  simp

theorem correctedDensity_rational {m K : ℕ} (hK : 0 < K) (e : Fin m ↪ Fin K)
    (I : Fin K → CorrectionIntervals m) (t : Fin K → ℚ) (ht : Function.Injective t)
    (x : ℝ) : ∃ r : ℚ, correctedDensity e I (fun q => (t q : ℝ)) x = r := by
  obtain ⟨c, hc⟩ := densityCoefficients_rational hK e t ht
  have hb (q : Fin m) := (I (e q)).bump_rational (t (e q)) x
  choose b hb using hb
  refine ⟨1 + ∑ q, c q * b q, ?_⟩
  simp only [correctedDensity, hc, hb, Rat.cast_add, Rat.cast_one, Rat.cast_sum, Rat.cast_mul]

noncomputable def densityMomentFunctional {m K : ℕ} (e : Fin m ↪ Fin K)
    (t : Fin K → ℝ) : ℝ[X] →ₗ[ℝ] ℝ :=
  (1 / (K : ℝ)) • ∑ q, densityCoefficients e t q • Polynomial.leval (t (e q))

@[simp] theorem densityMomentFunctional_apply {m K : ℕ} (e : Fin m ↪ Fin K)
    (t : Fin K → ℝ) (p : ℝ[X]) :
    densityMomentFunctional e t p = (∑ q, densityCoefficients e t q * p.eval (t (e q))) / K := by
  simp [densityMomentFunctional, Polynomial.leval_apply, div_eq_mul_inv, mul_comm]

/-- All selections solve the same functional equation on degree `m-1`. -/
theorem densityMomentFunctional_eq {m K : ℕ} (hK : 0 < K)
    (e f : Fin m ↪ Fin K) (t : Fin K → ℝ) (ht : Function.Injective t)
    (p : ℝ[X]) (hp : p.natDegree < m) :
    densityMomentFunctional e t p = densityMomentFunctional f t p := by
  apply polynomial_functionals_ext _ _ (m-1) ?_ p (by omega)
  intro r hr
  have hm : 0 < m := by omega
  let rr : Fin m := ⟨r, by omega⟩
  simpa only [densityMomentFunctional_apply, eval_pow, eval_X] using
    (densityCoefficients_moments hK e t ht rr).trans (densityCoefficients_moments hK f t ht rr).symm

theorem densityMomentFunctional_derivative {m K : ℕ} (hK : 0 < K)
    (e : Fin m ↪ Fin K) (t : Fin K → ℝ) (ht : Function.Injective t)
    (p : ℝ[X]) (hp : p.natDegree ≤ m) :
    densityMomentFunctional e t p.derivative =
      realPolynomialIntegral p - (∑ q, p.eval (t q)) / K := by
  let A : ℝ[X] →ₗ[ℝ] ℝ := (1/(K : ℝ)) • ∑ q, Polynomial.leval (t q)
  have hA (p : ℝ[X]) : A p = (∑ q, p.eval (t q))/K := by
    simp [A, Polynomial.leval_apply, div_eq_mul_inv, mul_comm]
  let L := (densityMomentFunctional e t).comp Polynomial.derivative - (realPolynomialIntegral - A)
  have hL (s : ℕ) (hs : s ≤ m) : L (X^s) = (0 : ℝ) := by
    change densityMomentFunctional e t (derivative (X^s)) - (realPolynomialIntegral (X^s) - A (X^s)) = 0
    cases s with
    | zero => simp [hA, Nat.ne_of_gt hK]
    | succ r =>
      let rr : Fin m := ⟨r, by omega⟩
      have hh := densityCoefficients_moments hK e t ht rr
      rw [derivative_X_pow, ← smul_eq_C_mul, map_smul, Nat.add_sub_cancel]
      simp only [smul_eq_mul, densityMomentFunctional_apply, eval_pow, eval_X]
      rw [hh, realPolynomialIntegral_X_pow, hA]
      simp only [momentDiscrepancy, rr, eval_pow, eval_X]
      have hr : (r+1 : ℝ) ≠ 0 := by positivity
      push_cast
      field_simp
      ring
  have hh := polynomial_functionals_ext L 0 m (by simpa using hL) p hp
  change densityMomentFunctional e t p.derivative - (realPolynomialIntegral p - A p) = 0 at hh
  rw [hA] at hh
  linarith

end FairDice
