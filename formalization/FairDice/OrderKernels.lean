import FairDice.MomentResponse
import FairDice.MonotoneMoments

namespace FairDice

open Polynomial

noncomputable def orderKernel (a b : ℕ) : ℝ[X] :=
  C (1/((a.factorial : ℝ)*(b.factorial : ℝ)))*X^a*(1-X)^b

theorem orderKernel_eval (a b : ℕ) (t : ℝ) :
    (orderKernel a b).eval t=t^a*(1-t)^b/((a.factorial : ℝ)*(b.factorial : ℝ)) := by
  simp [orderKernel]
  ring

theorem orderKernel_degree (a b : ℕ) : (orderKernel a b).natDegree ≤ a+b := by
  apply natDegree_mul_le.trans
  have hC : (C (1/((a.factorial : ℝ)*(b.factorial : ℝ)))*X^a).natDegree ≤ a :=
    (natDegree_C_mul_le _ _).trans (natDegree_X_pow_le a)
  have hlin : (1-X : ℝ[X]).natDegree ≤ 1 := (natDegree_sub_le (1 : ℝ[X]) X).trans (by simp)
  have hb : ((1-X : ℝ[X])^b).natDegree ≤ b := by rw [natDegree_pow]; nlinarith
  omega

/-- The predecessor and successor responses are exactly the derivative
of the constant-density full-order kernel, including both endpoint ranks. -/
theorem orderKernel_derivative (a b : ℕ) :
    (orderKernel a b).derivative =
      (if a=0 then 0 else orderKernel (a-1) b) -
        (if b=0 then 0 else orderKernel a (b-1)) := by
  apply Polynomial.funext
  intro x
  cases a with
  | zero =>
    cases b with
    | zero => simp [orderKernel]
    | succ b =>
      simp [orderKernel,derivative_mul,derivative_pow,Nat.factorial_succ]
      field_simp
  | succ a =>
    cases b with
    | zero =>
      simp [orderKernel,derivative_mul,derivative_pow,Nat.factorial_succ]
      field_simp
    | succ b =>
      simp [orderKernel,derivative_mul,derivative_pow,Nat.factorial_succ]
      field_simp
      ring

theorem realPolynomialIntegral_rat_map (p : ℚ[X]) :
    realPolynomialIntegral (p.map (Rat.castHom ℝ))=(polynomialIntegral 1 p : ℝ) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [Polynomial.map_add,map_add,Rat.cast_add,hp,hq]
  | monomial k c =>
    simp [Polynomial.map_monomial,realPolynomialIntegral_monomial,polynomialIntegral_monomial]

theorem orderKernel_rat_map (a b : ℕ) :
    orderKernel a b=(rankPolynomial 1 (a+b) a).map (Rat.castHom ℝ) := by
  simp [orderKernel,rankPolynomial,Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_sub]

theorem orderKernel_integral (a b : ℕ) :
    realPolynomialIntegral (orderKernel a b)=1/((a+b+1).factorial : ℝ) := by
  rw [orderKernel_rat_map,realPolynomialIntegral_rat_map,
    polynomialIntegral_rank 1 (by norm_num) (by omega),one_pow]
  push_cast
  rfl

end FairDice
