import FairDice.HahnConstruction
import FairDice.RationalDesigns

namespace FairDice

open Polynomial

/-- Replace integer weights by repeated nodes; repetitions are permitted in
an equal-weight rational design. -/
theorem rationalDesign_of_integer_weights {ι : Type*} [Fintype ι]
    (x : ι → ℚ) (k : ι → ℕ) {K r : ℕ} (hsum : ∑ i, k i = K)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1)
    (hexact : ∀ p : ℚ[X], p.natDegree ≤ r →
      ∑ i, (k i : ℚ) * p.eval (x i) = K * polynomialIntegral 1 p) :
    Nonempty (RationalDesign K r) := by
  classical
  have hcard : Fintype.card (Σ i, Fin (k i)) = K := by
    simpa only [Fintype.card_sigma, Fintype.card_fin] using hsum
  let e := Fintype.equivFinOfCardEq hcard
  refine ⟨⟨fun j => x (e.symm j).1, fun j => hx _, ?_⟩⟩
  intro p hp
  calc
    _ = ∑ j : Σ i, Fin (k i), p.eval (x j.1) :=
      Fintype.sum_equiv e.symm _ _ (fun _ => rfl)
    _ = ∑ i, (k i : ℚ) * p.eval (x i) := by
      rw [Fintype.sum_sigma]
      simp
    _ = _ := hexact p hp

theorem RationalRule.equal_weight_design {N r : ℕ} (R : RationalRule N r) (hN : 0 < N) :
    Nonempty (RationalDesign (N * R.denominator) r) := by
  obtain ⟨k, _, hk, hsum⟩ := R.integer_gaps R.denominator_pos (dvd_refl _)
  apply rationalDesign_of_integer_weights (fun i : Fin (N + 1) => (i.val : ℚ) / N) k hsum
  · intro i
    have hi : (i.val : ℚ) ≤ N := by exact_mod_cast (show i.val ≤ N by omega)
    have hNq : (0 : ℚ) < N := by exact_mod_cast hN
    exact ⟨by positivity, (div_le_one hNq).mpr hi⟩
  · intro p hp
    have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
    let q := p.comp (C (N : ℚ)⁻¹ * X)
    have hq : q.natDegree ≤ r := by
      rw [natDegree_comp]
      have hdeg : (C (N : ℚ)⁻¹ * X).natDegree ≤ 1 := by
        simpa using natDegree_C_mul_le (N : ℚ)⁻¹ X
      exact (Nat.mul_le_mul hp hdeg).trans (by omega)
    have he := R.exactness q hq
    calc
      _ = (R.denominator : ℚ) * ∑ i, R.weight i * q.eval (i.val : ℚ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        simp only [hk, q, eval_comp, eval_mul, eval_C, eval_X,
          div_eq_mul_inv, mul_comm, mul_left_comm]
      _ = (R.denominator : ℚ) * polynomialIntegral N q := by rw [he]
      _ = _ := by
        rw [polynomialIntegral_scale N hNq]
        push_cast
        ring

/-- The degree-r rational design mentioned after Corollary 4.6, including
an explicit `2^{O(r log r)}` node bound. -/
theorem hahn_equal_weight_design (h : HahnExternal) {r : ℕ} (hr : 2 ≤ r) :
    ∃ K : ℕ, 0 < K ∧ K ≤ 2^(28 * r * Nat.log 2 r) ∧ Nonempty (RationalDesign K r) := by
  let R := hahnRule h r (by omega)
  have hN : 0 < gridSize r := by unfold gridSize; positivity
  refine ⟨gridSize r * R.denominator, Nat.mul_pos hN R.denominator_pos, ?_, R.equal_weight_design hN⟩
  apply le_trans ?_ (hahnFaces_exponential_bound hr)
  change gridSize r * commonDenominator (gridSize r) r ≤
    commonDenominator (gridSize r) r * (gridSize r)^(r - 1)
  rw [Nat.mul_comm (gridSize r)]
  apply Nat.mul_le_mul_left
  exact (pow_one (gridSize r)).symm.le.trans
    (Nat.pow_le_pow_right hN (by omega))

end FairDice
