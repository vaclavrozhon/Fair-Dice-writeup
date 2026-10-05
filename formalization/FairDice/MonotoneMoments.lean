import FairDice.FaceMoments
import FairDice.PairedThresholds

namespace FairDice

open Polynomial

/-- Integral on the unit interval, retained as a real linear functional. -/
noncomputable def realPolynomialIntegral : ℝ[X] →ₗ[ℝ] ℝ :=
  Polynomial.lsum fun j => (1 / (j + 1 : ℝ)) • LinearMap.id

@[simp] theorem realPolynomialIntegral_monomial (a : ℝ) (j : ℕ) :
    realPolynomialIntegral (monomial j a) = a / (j + 1 : ℝ) := by
  simp [realPolynomialIntegral, Polynomial.lsum_apply, Polynomial.sum_monomial_index]
  ring

@[simp] theorem realPolynomialIntegral_X_pow (j : ℕ) :
    realPolynomialIntegral (X^j) = 1 / (j + 1 : ℝ) := by
  rw [← monomial_one_right_eq_X_pow, realPolynomialIntegral_monomial]

@[simp] theorem realPolynomialIntegral_one : realPolynomialIntegral 1 = 1 := by
  simpa using realPolynomialIntegral_X_pow 0

theorem realPolynomialIntegral_C_mul (a : ℝ) (p : ℝ[X]) :
    realPolynomialIntegral (C a * p) = a * realPolynomialIntegral p := by
  rw [← smul_eq_C_mul, map_smul]
  rfl

theorem realPolynomialIntegral_eq_integral (p : ℝ[X]) :
    realPolynomialIntegral p = ∫ x in (0 : ℝ)..1, p.eval x := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [map_add, eval_add]
    rw [intervalIntegral.integral_add (p.continuous.intervalIntegrable 0 1)
      (q.continuous.intervalIntegrable 0 1), hp, hq]
  | monomial j a => simp [intervalIntegral.integral_const_mul, div_eq_mul_inv]

/-- The weighted monotone comparison model used in `individual-last-row`.
The only exactness premise is the square-free monomial identity; shifted
multi-affine tests are derived from it below. -/
structure MonotoneMoments (ι : Type*) [Fintype ι] (K : ℕ) where
  row : Fin K → ι → ℝ
  weight : Fin K → ℝ
  weight_pos : ∀ q, 0 < weight q
  weight_sum : ∑ q, weight q = 1
  in_unit : ∀ q i, 0 ≤ row q i ∧ row q i ≤ 1
  monotone : ∀ i, Monotone (fun q => row q i)
  moments : ∀ S : Finset ι, ∑ q, weight q * ∏ i ∈ S, row q i = 1 / (S.card + 1 : ℝ)

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : ℕ}

noncomputable def shiftedTest (S : Finset ι) (b : ι → ℝ) : ℝ[X] :=
  ∏ i ∈ S, (X - C (b i))

/-- Equation `individual-diagonal-identity` on products of distinct shifted
coordinates, including the tests needed by both quadrature arguments. -/
theorem MonotoneMoments.shifted_identity (A : MonotoneMoments ι K)
    (S : Finset ι) (b : ι → ℝ) :
    (∑ q, A.weight q * ∏ i ∈ S, (A.row q i - b i)) =
      realPolynomialIntegral (shiftedTest S b) := by
  classical
  simp only [shiftedTest, Finset.prod_sub, map_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T _
  calc
    _ = ((-1 : ℝ)^T.card * ∏ i ∈ T, b i) *
        (∑ q, A.weight q * ∏ i ∈ S \ T, A.row q i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q _
      ring
    _ = ((-1 : ℝ)^T.card * ∏ i ∈ T, b i) / ((S \ T).card + 1 : ℝ) := by
      rw [A.moments]
      ring
    _ = _ := by
      have he : (((-1 : ℝ[X])^T.card * ∏ i ∈ S \ T, X) * ∏ i ∈ T, C (b i)) =
          C ((-1 : ℝ)^T.card * ∏ i ∈ T, b i) * X^(S \ T).card := by
        simp only [Finset.prod_const, ← map_prod]
        simp [map_mul, map_pow, mul_comm, mul_left_comm, mul_assoc]
      rw [he, realPolynomialIntegral_C_mul, realPolynomialIntegral_X_pow]
      ring

omit [Fintype ι] [DecidableEq ι] in
theorem MonotoneMoments.shifted_degree (S : Finset ι) (b : ι → ℝ) :
    (shiftedTest S b).natDegree ≤ S.card := by
  apply (natDegree_prod_le S (fun i => (X : ℝ[X]) - C (b i))).trans
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_one, Nat.cast_id] using
    Finset.sum_le_sum (s := S) (fun i _ =>
      (natDegree_sub_le (X : ℝ[X]) (C (b i))).trans
        (max_le (by simp) (by simp) : max X.natDegree (C (b i)).natDegree ≤ 1))

end FairDice
