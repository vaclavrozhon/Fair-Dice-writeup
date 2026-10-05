import FairDice.MomentColoring

namespace FairDice

open Polynomial

/-- Outer variable is the block index; coefficients are polynomials in rank
variable `z`. -/
noncomputable def placeBefore (m : ℕ) : ℚ[X][X] :=
  C (C ((m : ℚ) - 1) + X) + C (X - 1) * X

noncomputable def placeAfter (m : ℕ) : ℚ[X][X] :=
  C (C (m : ℚ)) + C (X - 1) * X

noncomputable def placePosition (n m r : ℕ) : ℚ[X][X] :=
  placeBefore m ^ r * placeAfter m ^ (n - 1 - r)

theorem placeBefore_degree (m : ℕ) : (placeBefore m).natDegree ≤ 1 := by
  unfold placeBefore
  compute_degree!

theorem placeAfter_degree (m : ℕ) : (placeAfter m).natDegree ≤ 1 := by
  unfold placeAfter
  compute_degree!

theorem placePosition_degree {n r : ℕ} (m : ℕ) (hr : r ≤ n - 1) :
    (placePosition n m r).natDegree ≤ n - 1 := by
  apply natDegree_mul_le.trans
  have h1 := (natDegree_pow_le (p := placeBefore m) (n := r)).trans
    (Nat.mul_le_mul_left r (placeBefore_degree m))
  have h2 := (natDegree_pow_le (p := placeAfter m) (n := n - 1 - r)).trans
    (Nat.mul_le_mul_left (n - 1 - r) (placeAfter_degree m))
  omega

/-- The coefficient of the highest power of the block index is independent
of the position within the block. -/
theorem placePosition_top {n r : ℕ} (m : ℕ) (hr : r ≤ n - 1) :
    (placePosition n m r).coeff (n - 1) = (X - 1 : ℚ[X])^(n - 1) := by
  have hsum : r + (n - 1 - r) = n - 1 := by omega
  have h1 : (placeBefore m ^ r).natDegree ≤ r := by
    simpa using (natDegree_pow_le (p := placeBefore m) (n := r)).trans
      (Nat.mul_le_mul_left r (placeBefore_degree m))
  have h2 : (placeAfter m ^ (n - 1 - r)).natDegree ≤ n - 1 - r := by
    simpa using (natDegree_pow_le (p := placeAfter m) (n := n - 1 - r)).trans
      (Nat.mul_le_mul_left (n - 1 - r) (placeAfter_degree m))
  unfold placePosition
  have htop := coeff_mul_add_eq_of_natDegree_le h1 h2
  rw [hsum] at htop
  rw [htop]
  have hc1 : (placeBefore m ^ r).coeff r = (X - 1 : ℚ[X])^r := by
    simpa [placeBefore, coeff_one] using coeff_pow_of_natDegree_le (m := r) (placeBefore_degree m)
  have hc2 : (placeAfter m ^ (n - 1 - r)).coeff (n - 1 - r) = (X - 1 : ℚ[X])^(n - 1 - r) := by
    simpa [placeAfter] using coeff_pow_of_natDegree_le (m := n - 1 - r) (placeAfter_degree m)
  rw [hc1, hc2, ← pow_add, hsum]

theorem placePosition_difference_degree {n : ℕ} (hn : 2 ≤ n) (m : ℕ) (r : Fin n) :
    (placePosition n m r.val - placePosition n m 0).natDegree ≤ n - 2 := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro j hj
  have hr : r.val ≤ n - 1 := by omega
  rw [coeff_sub]
  by_cases he : j = n - 1
  · rw [he, placePosition_top m hr, placePosition_top m (by omega), sub_self]
  · rw [coeff_eq_zero_of_natDegree_lt ((placePosition_degree m hr).trans_lt (by omega)),
      coeff_eq_zero_of_natDegree_lt ((placePosition_degree m (show 0 ≤ n - 1 by omega)).trans_lt (by omega)),
      sub_self]

theorem placePosition_eval (n m r t : ℕ) :
    (placePosition n m r).eval (t : ℚ[X]) =
      (C ((m : ℚ) - t - 1) + C ((t : ℚ) + 1) * X)^r *
        (C ((m : ℚ) - t) + C (t : ℚ) * X)^(n - 1 - r) := by
  have hb : (placeBefore m).eval (t : ℚ[X]) =
      C ((m : ℚ) - t - 1) + C ((t : ℚ) + 1) * X := by
    simp [placeBefore]
    ring
  have ha : (placeAfter m).eval (t : ℚ[X]) = C ((m : ℚ) - t) + C (t : ℚ) * X := by
    simp [placeAfter]
    ring
  simp [placePosition, hb, ha]

theorem placePosition_balanced {n m : ℕ} (hn : 2 ≤ n) [NeZero n]
    (c : Fin m → Fin n) (hc : MomentBalanced c (n - 2)) (a b : Fin n) :
    (∑ t : Fin m, (placePosition n m (a + c t).val).eval (t.val : ℚ[X])) =
      ∑ t : Fin m, (placePosition n m (b + c t).val).eval (t.val : ℚ[X]) := by
  exact momentBalanced_shifted_polynomials hc (fun r => placePosition n m r.val)
    (placePosition n m 0) (placePosition_difference_degree hn m) a b

end FairDice
