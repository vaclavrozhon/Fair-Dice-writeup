import FairDice.MomentResponse
import Mathlib.MeasureTheory.Integral.IntervalIntegral.MeanValue

namespace FairDice

open Polynomial

/-- Moments of ordered intervals; row `r` is the integral of `x^r`. -/
def intervalMomentMatrix {R : Type*} [Field R] {m : ℕ}
    (a b : Fin m → R) : Matrix (Fin m) (Fin m) R :=
  fun r j => (b j ^ (r.val+1) - a j ^ (r.val+1)) / (r.val+1 : R)

theorem intervalMomentMatrix_eq_integral {m : ℕ} (a b : Fin m → ℝ) (r j : Fin m) :
    intervalMomentMatrix a b r j = ∫ x in a j..b j, x^r.val := by
  simp [intervalMomentMatrix, integral_pow]

/-- Invertibility of the interval moment matrix, proved by an alternative
to the determinant integral: a nonzero degree-`m-1` polynomial cannot
have zero integral on `m` strictly ordered positive-length intervals. -/
theorem intervalMomentMatrix_isUnit {m : ℕ} (a b : Fin m → ℝ)
    (hab : ∀ j, a j < b j) (horder : ∀ i j, i < j → b i < a j) :
    IsUnit (intervalMomentMatrix a b) := by
  classical
  let M := intervalMomentMatrix a b
  have hker (v : Fin m → ℝ) (hv : M.transpose.mulVec v = 0) : v = 0 := by
    by_cases hm : m = 0
    · subst m
      exact Subsingleton.elim _ _
    have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    let p : ℝ[X] := ∑ r : Fin m, monomial r.val (v r)
    have hpdeg : p.natDegree < m := by
      apply lt_of_le_of_lt (natDegree_sum_le_of_forall_le Finset.univ
        (fun r : Fin m => monomial r.val (v r))
        (fun r _ => (natDegree_monomial_le (v r)).trans (show r.val ≤ m-1 by omega)))
      omega
    have hint (j : Fin m) : (∫ x in a j..b j, p.eval x) = 0 := by
      have h := congrFun hv j
      change (∑ r, M r j * v r) = 0 at h
      simp only [p, eval_finsetSum, eval_monomial]
      rw [intervalIntegral.integral_finsetSum]
      · simp only [intervalIntegral.integral_const_mul, ← intervalMomentMatrix_eq_integral]
        simpa [M, mul_comm] using h
      · intro r _
        exact (continuous_const.mul (continuous_id.pow r.val)).intervalIntegrable _ _
    have hroot (j : Fin m) : ∃ x : ℝ, a j ≤ x ∧ x ≤ b j ∧ p.eval x = 0 := by
      obtain ⟨x, hx, he⟩ := exists_eq_const_mul_intervalIntegral_of_nonneg
        (μ := MeasureTheory.volume) (f := p.eval) (g := fun _ => (1 : ℝ)) p.continuous.continuousOn
        (intervalIntegrable_const) (fun _ _ => by norm_num)
      rw [Set.uIcc_of_le (hab j).le] at hx
      simp only [mul_one, intervalIntegral.integral_const, smul_eq_mul, mul_one, hint j] at he
      refine ⟨x, hx.1, hx.2, ?_⟩
      exact (mul_eq_zero.mp he.symm).resolve_right (ne_of_gt (sub_pos.mpr (hab j)))
    choose x hxa hxb hx using hroot
    have hmono : StrictMono x := by
      intro i j hij
      exact (hxb i).trans_lt ((horder i j hij).trans_le (hxa j))
    have hpzero : p = 0 := eq_zero_of_natDegree_lt_card_of_eval_eq_zero p hmono.injective hx
      (by simpa using hpdeg)
    funext r
    have hc := congrArg (fun q : ℝ[X] => q.coeff r.val) hpzero
    simpa [p, finsetSum_coeff, coeff_monomial, Fin.val_inj] using hc
  have hinj : Function.Injective M.transpose.mulVec := by
    intro v w h
    apply sub_eq_zero.mp
    apply hker
    rw [Matrix.mulVec_sub, h, sub_self]
  have hunit : IsUnit M.transpose := Matrix.mulVec_injective_iff_isUnit.mp hinj
  exact (Matrix.isUnit_transpose M).mp hunit

/-- The same matrix over the rationals is invertible, so local corrections
have rational values at rational nodes. -/
theorem rational_intervalMomentMatrix_isUnit {m : ℕ} (a b : Fin m → ℚ)
    (hab : ∀ j, a j < b j) (horder : ∀ i j, i < j → b i < a j) :
    IsUnit (intervalMomentMatrix a b) := by
  let M := intervalMomentMatrix a b
  let MR := intervalMomentMatrix (fun j => (a j : ℝ)) (fun j => (b j : ℝ))
  have hunit : IsUnit MR := intervalMomentMatrix_isUnit _ _
    (fun j => by exact_mod_cast hab j) (fun i j hij => by exact_mod_cast horder i j hij)
  have hMR : MR = M.map (Rat.castHom ℝ) := by
    ext r j
    simp [M, MR, intervalMomentMatrix]
  have hdet : M.det ≠ 0 := by
    intro hz
    have hR := (Matrix.isUnit_iff_isUnit_det MR).mp hunit
    apply hR.ne_zero
    rw [hMR]
    change ((Rat.castHom ℝ).mapMatrix M).det = 0
    rw [← RingHom.map_det, hz]
    simp
  exact (Matrix.isUnit_iff_isUnit_det M).mpr (isUnit_iff_ne_zero.mpr hdet)

/-- Both halves of a local correction are obtained by solving their fixed
interval moment systems with opposite evaluation vectors. -/
theorem local_moment_coefficients {m : ℕ} (a b : Fin m → ℚ)
    (hab : ∀ j, a j < b j) (horder : ∀ i j, i < j → b i < a j) (t : ℚ) :
    ∃ c : Fin m → ℚ, ∀ r : Fin m,
      ∑ j, c j * intervalMomentMatrix a b r j = t^r.val := by
  have hunit := rational_intervalMomentMatrix_isUnit a b hab horder
  obtain ⟨c, hc⟩ := (Matrix.mulVec_surjective_iff_isUnit.mpr hunit) (fun r => t^r.val)
  exact ⟨c, fun r => by simpa [Matrix.mulVec, dotProduct, mul_comm] using congrFun hc r⟩

end FairDice
