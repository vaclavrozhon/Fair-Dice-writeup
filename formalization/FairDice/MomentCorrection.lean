import Mathlib

namespace FairDice

/-- First two moments of the left-endpoint uniform grid. -/
theorem left_grid_first_moment (m : ℕ) (hm : 0 < m) :
    (∑ j ∈ Finset.range m, (1 / (m : ℚ)) * (j / (m : ℚ))) =
      (m - 1 : ℚ) / (2 * m) := by
  have hs (n : ℕ) : (∑ j ∈ Finset.range n, (j : ℚ)) = (n : ℚ) * (n - 1 : ℚ) / 2 := by
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
  simp_rw [div_eq_mul_inv, ← mul_assoc]
  rw [← Finset.sum_mul, ← Finset.mul_sum, hs]
  have hmq : (m : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  field_simp

theorem left_grid_second_moment (m : ℕ) (hm : 0 < m) :
    (∑ j ∈ Finset.range m, (1 / (m : ℚ)) * (j / (m : ℚ))^2) =
      (m - 1 : ℚ) * (2 * m - 1 : ℚ) / (6 * m^2) := by
  have hs (n : ℕ) : (∑ j ∈ Finset.range n, (j : ℚ)^2) =
      (n : ℚ) * (n - 1 : ℚ) * (2 * n - 1 : ℚ) / 6 := by
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring
  simp_rw [div_pow, div_eq_mul_inv, ← mul_assoc]
  rw [← Finset.sum_mul, ← Finset.mul_sum, hs]
  have hmq : (m : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  field_simp

/-- Correcting only nodes 0, 1/3, 2/3 forces the stated weight at 1/3.
The grid moments above establish the two uncorrected terms. -/
theorem three_node_correction_weight {m : ℕ} (hm : 0 < m) (β γ : ℚ)
    (hfirst : (m - 1 : ℚ) / (2 * m) + β / 3 + γ * (2 / 3) = 1 / 2)
    (hsecond : (m - 1 : ℚ) * (2 * m - 1 : ℚ) / (6 * m^2) +
      β / 9 + γ * (4 / 9) = 1 / 3) :
    1 / (m : ℚ) + β = -1 / (2 * m) + 3 / (2 * m^2) := by
  have hmq : (m : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  field_simp at hfirst hsecond ⊢
  nlinarith

theorem three_node_correction_negative {m : ℕ} (hm : 3 < m) :
    (-1 / (2 * m) + 3 / (2 * (m : ℚ)^2)) < 0 := by
  have hmR : (3 : ℚ) < m := by exact_mod_cast hm
  have hmq : (m : ℚ) ≠ 0 := by linarith
  have he : (-1 / (2 * m) + 3 / (2 * (m : ℚ)^2)) = (3 - m) / (2 * (m : ℚ)^2) := by
    field_simp
    ring
  rw [he]
  exact div_neg_of_neg_of_pos (by linarith) (by positivity)

end FairDice
