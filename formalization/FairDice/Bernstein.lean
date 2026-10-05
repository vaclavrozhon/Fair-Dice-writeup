import FairDice.Quadrature

namespace FairDice

open Polynomial

theorem polynomialIntegral_derivative (N : ℚ) (p : ℚ[X]) :
    polynomialIntegral N (derivative p) = p.eval N - p.eval 0 := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq]; ring
  | monomial j a =>
    cases j with
    | zero => simp
    | succ j =>
      simp [polynomialIntegral_monomial]
      field_simp

theorem polynomialIntegral_C_mul (N c : ℚ) (p : ℚ[X]) :
    polynomialIntegral N (C c * p) = c * polynomialIntegral N p := by
  rw [← smul_eq_C_mul, map_smul]
  rfl

theorem polynomialIntegral_bernstein_adjacent (n j : ℕ) (hj : j < n) :
    polynomialIntegral 1 (bernsteinPolynomial ℚ n j) =
      polynomialIntegral 1 (bernsteinPolynomial ℚ n (j + 1)) := by
  have hd := polynomialIntegral_derivative 1 (bernsteinPolynomial ℚ (n + 1) (j + 1))
  rw [bernsteinPolynomial.derivative_succ_aux] at hd
  have he : (bernsteinPolynomial ℚ (n + 1) (j + 1)).eval 1 -
      (bernsteinPolynomial ℚ (n + 1) (j + 1)).eval 0 = 0 := by
    simp [bernsteinPolynomial.eval_at_0, bernsteinPolynomial.eval_at_1, Nat.ne_of_lt hj]
  rw [he] at hd
  have hC : ((n : ℚ[X]) + 1) = C ((n : ℚ) + 1) := by simp
  rw [hC, polynomialIntegral_C_mul, map_sub] at hd
  have hpos : (0 : ℚ) < n + 1 := by positivity
  nlinarith

theorem polynomialIntegral_bernstein (n j : ℕ) (hj : j ≤ n) :
    polynomialIntegral 1 (bernsteinPolynomial ℚ n j) = 1 / (n + 1 : ℚ) := by
  have heq : ∀ i ≤ n, polynomialIntegral 1 (bernsteinPolynomial ℚ n i) =
      polynomialIntegral 1 (bernsteinPolynomial ℚ n 0) := by
    intro i hi
    induction i with
    | zero => rfl
    | succ i ih =>
      exact (polynomialIntegral_bernstein_adjacent n i (by omega)).symm.trans
        (ih (by omega))
  have hsum := congrArg (polynomialIntegral 1) (bernsteinPolynomial.sum ℚ n)
  rw [map_sum, polynomialIntegral_one] at hsum
  have heqsum : (∑ i ∈ Finset.range (n + 1), polynomialIntegral 1 (bernsteinPolynomial ℚ n i)) =
      (n + 1 : ℚ) * polynomialIntegral 1 (bernsteinPolynomial ℚ n 0) := by
    calc
      _ = ∑ _i ∈ Finset.range (n + 1), polynomialIntegral 1 (bernsteinPolynomial ℚ n 0) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact heq i (by have := Finset.mem_range.mp hi; omega)
      _ = _ := by simp
  rw [heqsum] at hsum
  rw [heq j hj]
  apply (eq_div_iff (by positivity : (n + 1 : ℚ) ≠ 0)).mpr
  nlinarith

theorem bernstein_degree (n j : ℕ) : (bernsteinPolynomial ℚ n j).natDegree ≤ n := by
  by_cases hj : j ≤ n
  · unfold bernsteinPolynomial
    calc
      _ ≤ ((n.choose j : ℚ[X]) * X ^ j).natDegree + ((1 - X : ℚ[X])^(n - j)).natDegree :=
        natDegree_mul_le
      _ ≤ j + (n - j) := by
        have hC : ((n.choose j : ℚ[X]) * X ^ j).natDegree ≤ j := by
          simpa using natDegree_C_mul_le (n.choose j : ℚ) (X^j)
        have hX : (1 - X : ℚ[X]).natDegree = 1 := by
          rw [show (1 - X : ℚ[X]) = -(X - 1) by ring, natDegree_neg]
          exact natDegree_X_sub_C (1 : ℚ)
        simp only [natDegree_pow, hX]
        omega
      _ = n := Nat.add_sub_of_le hj
  · rw [bernsteinPolynomial.eq_zero_of_lt ℚ (by omega)]
    simp

/-- Polynomial change of scale between `[0,N]` and `[0,1]`. -/
theorem polynomialIntegral_scale (N : ℚ) (hN : N ≠ 0) (p : ℚ[X]) :
    polynomialIntegral N (p.comp (C N⁻¹ * X)) = N * polynomialIntegral 1 p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [hp, hq, mul_add]
  | monomial j a =>
    have hpoly : (monomial j a).comp (C N⁻¹ * X) = monomial j (a * N⁻¹ ^ j) := by
      rw [monomial_comp, mul_pow, ← C_pow, ← mul_assoc, ← C_mul, C_mul_X_pow_eq_monomial]
    rw [hpoly, polynomialIntegral_monomial, polynomialIntegral_monomial]
    simp only [one_pow, mul_one, pow_succ]
    field_simp
    rw [mul_assoc, ← mul_pow]
    simp [hN]

/-- The polynomial that counts a fixed rank of the new die, before the common
factor contributed by the old face multiplicity. -/
noncomputable def rankPolynomial (N : ℚ) (r j : ℕ) : ℚ[X] :=
  C (1 / ((j.factorial : ℚ) * (r - j).factorial)) * X^j * (C N - X)^(r - j)

theorem rankPolynomial_degree (N : ℚ) {r j : ℕ} (hj : j ≤ r) :
    (rankPolynomial N r j).natDegree ≤ r := by
  unfold rankPolynomial
  calc
    _ ≤ (C (1 / ((j.factorial : ℚ) * (r - j).factorial)) * X^j).natDegree +
        ((C N - X)^(r - j)).natDegree := natDegree_mul_le
    _ ≤ j + (r - j) := by
      have hC := natDegree_C_mul_le (1 / ((j.factorial : ℚ) * (r - j).factorial)) (X^j)
      have hX : (C N - X : ℚ[X]).natDegree = 1 := by
        rw [show (C N - X : ℚ[X]) = -(X - C N) by ring, natDegree_neg]
        exact natDegree_X_sub_C N
      simp only [natDegree_pow, natDegree_X, hX, mul_one] at hC ⊢
      omega
    _ = r := Nat.add_sub_of_le hj

theorem rankPolynomial_scale (N : ℚ) (hN : N ≠ 0) {r j : ℕ} (hj : j ≤ r) :
    rankPolynomial N r j = C (N^r / (r.factorial : ℚ)) *
      (bernsteinPolynomial ℚ r j).comp (C N⁻¹ * X) := by
  apply Polynomial.funext
  intro x
  simp only [rankPolynomial, bernsteinPolynomial, eval_mul, eval_C, eval_pow, eval_X,
    eval_sub, eval_one, eval_comp, eval_natCast]
  rw [Nat.cast_choose ℚ hj]
  have hsub : 1 - N⁻¹ * x = (N - x) / N := by field_simp
  rw [hsub, div_pow, mul_pow, inv_pow]
  have hpow : N^j * N^(r - j) = N^r := by rw [← pow_add, Nat.add_sub_of_le hj]
  have hfac : (r.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (Nat.factorial_pos r)
  field_simp
  rw [mul_assoc _ (N ^ j) (N ^ (r - j)), hpow]

theorem polynomialIntegral_rank (N : ℚ) (hN : N ≠ 0) {r j : ℕ} (hj : j ≤ r) :
    polynomialIntegral N (rankPolynomial N r j) = N^(r + 1) / (r + 1).factorial := by
  rw [rankPolynomial_scale N hN hj, polynomialIntegral_C_mul,
    polynomialIntegral_scale N hN, polynomialIntegral_bernstein r j hj]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  field_simp

@[simp] theorem rankPolynomial_eval (N x : ℚ) (r j : ℕ) :
    (rankPolynomial N r j).eval x = x^j * (N - x)^(r - j) /
      ((j.factorial : ℚ) * (r - j).factorial) := by
  simp [rankPolynomial]
  ring

end FairDice
