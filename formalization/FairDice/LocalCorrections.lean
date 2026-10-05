import FairDice.IntervalMomentMatrix
import FairDice.MonotoneMoments

namespace FairDice

open Polynomial MeasureTheory Set

noncomputable def realPolynomialInterval (a b : ℝ) : ℝ[X] →ₗ[ℝ] ℝ :=
  Polynomial.lsum fun r => ((b^(r+1) - a^(r+1)) / (r+1 : ℝ)) • LinearMap.id

@[simp] theorem realPolynomialInterval_X_pow (a b : ℝ) (r : ℕ) :
    realPolynomialInterval a b (X^r) = (b^(r+1) - a^(r+1)) / (r+1 : ℝ) := by
  rw [← monomial_one_right_eq_X_pow]
  simp [realPolynomialInterval, Polynomial.lsum_apply, Polynomial.sum_monomial_index]

theorem realPolynomialInterval_eq_integral (a b : ℝ) (p : ℝ[X]) :
    realPolynomialInterval a b p = ∫ x in a..b, p.eval x := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, eval_add]
    rw [intervalIntegral.integral_add (p.continuous.intervalIntegrable _ _)
      (q.continuous.intervalIntegrable _ _), hp, hq]
  | monomial r c =>
    simp [realPolynomialInterval, Polynomial.lsum_apply, Polynomial.sum_monomial_index,
      intervalIntegral.integral_const_mul, integral_pow]
    ring

noncomputable def intervalCorrection {m : ℕ} (a b : Fin m → ℝ) (t : ℝ) : Fin m → ℝ :=
  (intervalMomentMatrix a b)⁻¹.mulVec (fun r => t^r.val)

theorem intervalCorrection_continuous {m : ℕ} (a b : Fin m → ℝ) (j : Fin m) :
    Continuous (fun t => intervalCorrection a b t j) := by
  unfold intervalCorrection Matrix.mulVec dotProduct
  exact continuous_finsetSum _ (fun r _ => continuous_const.mul (continuous_id.pow r.val))

theorem intervalCorrection_moments {m : ℕ} (a b : Fin m → ℝ)
    (hab : ∀ j, a j < b j) (horder : ∀ i j, i < j → b i < a j) (t : ℝ) :
    (intervalMomentMatrix a b).mulVec (intervalCorrection a b t) = fun r => t^r.val := by
  unfold intervalCorrection
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).mp (intervalMomentMatrix_isUnit a b hab horder)),
    Matrix.one_mulVec]

theorem intervalCorrection_exact {m : ℕ} (a b : Fin m → ℝ)
    (hab : ∀ j, a j < b j) (horder : ∀ i j, i < j → b i < a j)
    (t : ℝ) (p : ℝ[X]) (hp : p.natDegree < m) :
    (∑ j, intervalCorrection a b t j * realPolynomialInterval (a j) (b j) p) = p.eval t := by
  let L : ℝ[X] →ₗ[ℝ] ℝ := ∑ j, intervalCorrection a b t j • realPolynomialInterval (a j) (b j)
  have hmono (r : ℕ) (hr : r ≤ m-1) : L (X^r) = Polynomial.leval t (X^r) := by
    have hm : 0 < m := by omega
    let rr : Fin m := ⟨r, by omega⟩
    have h := congrFun (intervalCorrection_moments a b hab horder t) rr
    simpa [L, Matrix.mulVec, dotProduct, intervalMomentMatrix, mul_comm,
      realPolynomialInterval_X_pow, Polynomial.leval_apply, rr] using h
  have h := polynomial_functionals_ext L (Polynomial.leval t) (m-1) hmono p (by omega)
  simpa [L, Polynomial.leval_apply] using h

theorem intervalCorrection_rational {m : ℕ} (a b : Fin m → ℚ)
    (hab : ∀ j, a j < b j) (horder : ∀ i j, i < j → b i < a j) (t : ℚ) :
    ∃ c : Fin m → ℚ, ∀ j,
      intervalCorrection (fun j => (a j : ℝ)) (fun j => (b j : ℝ)) t j = c j := by
  obtain ⟨c, hc⟩ := local_moment_coefficients a b hab horder t
  let ar := fun j => (a j : ℝ)
  let br := fun j => (b j : ℝ)
  have habR (j : Fin m) : ar j < br j := by
    change (a j : ℝ) < b j
    exact_mod_cast hab j
  have horderR (i j : Fin m) (hij : i < j) : br i < ar j := by
    change (b i : ℝ) < a j
    exact_mod_cast horder i j hij
  have hcast : (intervalMomentMatrix ar br).mulVec (fun j => (c j : ℝ)) = fun r => (t : ℝ)^r.val := by
    funext r
    have h := hc r
    have hR : (∑ j, (c j : ℝ) * ((intervalMomentMatrix a b r j : ℚ) : ℝ)) = (t : ℝ)^r.val := by
      exact_mod_cast h
    simpa [Matrix.mulVec, dotProduct, intervalMomentMatrix, ar, br, mul_comm] using hR
  have hinj := Matrix.mulVec_injective_iff_isUnit.mpr
    (intervalMomentMatrix_isUnit ar br habR horderR)
  have hh := hinj ((intervalCorrection_moments ar br habR horderR t).trans hcast.symm)
  exact ⟨c, fun j => congrFun hh j⟩

/-- A literal piecewise constant function, with fixed interval breakpoints. -/
noncomputable def momentStep {m : ℕ} (a b : Fin m → ℝ) (c : Fin m → ℝ) (x : ℝ) : ℝ :=
  ∑ j, c j * (Ioc (a j) (b j)).indicator (fun _ => (1 : ℝ)) x

private theorem indicator_polynomial_integrable (p : ℝ[X]) (a b : ℝ) (hab : a ≤ b) :
    Integrable ((Ioc a b).indicator p.eval) volume := by
  rw [integrable_indicator_iff measurableSet_Ioc]
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp (p.continuous.intervalIntegrable _ _)

theorem momentStep_integrable {m : ℕ} (a b : Fin m → ℝ) (c : Fin m → ℝ)
    (hab : ∀ j, a j ≤ b j) (p : ℝ[X]) :
    Integrable (fun x => momentStep a b c x * p.eval x) volume := by
  have he : (fun x => momentStep a b c x * p.eval x) =
      fun x => ∑ j, c j * (Ioc (a j) (b j)).indicator p.eval x := by
    funext x
    simp only [momentStep, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hx : x ∈ Ioc (a j) (b j) <;> simp [hx]
  rw [he]
  exact integrable_finsetSum _ (fun j _ =>
    (indicator_polynomial_integrable p (a j) (b j) (hab j)).const_mul (c j))

theorem momentStep_integral {m : ℕ} (a b : Fin m → ℝ) (c : Fin m → ℝ)
    (hab : ∀ j, a j ≤ b j) (lo hi : ℝ)
    (hlo : ∀ j, lo ≤ a j) (hhi : ∀ j, b j ≤ hi) (p : ℝ[X]) :
    (∫ x in lo..hi, momentStep a b c x * p.eval x) =
      ∑ j, c j * realPolynomialInterval (a j) (b j) p := by
  have he : (fun x => momentStep a b c x * p.eval x) =
      fun x => ∑ j, c j * (Ioc (a j) (b j)).indicator p.eval x := by
    funext x
    simp only [momentStep, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hx : x ∈ Ioc (a j) (b j) <;> simp [hx]
  rw [he, intervalIntegral.integral_finsetSum (fun j _ =>
    ((indicator_polynomial_integrable p (a j) (b j) (hab j)).const_mul (c j)).intervalIntegrable)]
  apply Finset.sum_congr rfl
  intro j _
  rw [intervalIntegral.integral_const_mul]
  congr 1
  rw [intervalIntegral.integral_eq_integral_of_support_subset
    (Set.support_indicator_subset.trans (by
      intro x hx; exact ⟨(hlo j).trans_lt hx.1, hx.2.trans (hhi j)⟩)),
    integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le (hab j), ← realPolynomialInterval_eq_integral]

/-- A correction is identically zero before all its support intervals. -/
theorem momentStep_integral_before {m : ℕ} (a b : Fin m → ℝ) (c : Fin m → ℝ)
    (lo hi : ℝ) (hlh : lo ≤ hi) (ha : ∀ j, hi ≤ a j) (p : ℝ[X]) :
    (∫ x in lo..hi, momentStep a b c x * p.eval x) = 0 := by
  calc
    _ = ∫ x in lo..hi, (0 : ℝ) := intervalIntegral.integral_congr (by
      intro x hx
      rw [uIcc_of_le hlh] at hx
      have he (j : Fin m) : x ∉ Ioc (a j) (b j) := by
        intro h; linarith [ha j, h.1, hx.2]
      simp [momentStep, he])
    _ = 0 := by simp

/-- A correction is identically zero after all its support intervals. -/
theorem momentStep_integral_after {m : ℕ} (a b : Fin m → ℝ) (c : Fin m → ℝ)
    (lo hi : ℝ) (hlh : lo ≤ hi) (hb : ∀ j, b j < lo) (p : ℝ[X]) :
    (∫ x in lo..hi, momentStep a b c x * p.eval x) = 0 := by
  calc
    _ = ∫ x in lo..hi, (0 : ℝ) := intervalIntegral.integral_congr (by
      intro x hx
      rw [uIcc_of_le hlh] at hx
      have he (j : Fin m) : x ∉ Ioc (a j) (b j) := by
        intro h; linarith [hb j, h.2, hx.1]
      simp [momentStep, he])
    _ = 0 := by simp

end FairDice
