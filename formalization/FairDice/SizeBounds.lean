import FairDice.Denominators
import FairDice.HahnPositivity

namespace FairDice

theorem fallingProduct_le_pow (N n : ℕ) : fallingProduct N n ≤ N ^ n := by
  calc
    _ ≤ ∏ _a ∈ Finset.range n, N :=
      Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun _ _ => Nat.sub_le _ _)
    _ = _ := by simp

theorem risingProduct_le_pow {N n : ℕ} (hn : n + 1 ≤ N) :
    risingProduct N n ≤ (2 * N) ^ n := by
  calc
    _ ≤ ∏ _a ∈ Finset.range n, 2 * N := by
      apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
      intro a ha
      have := Finset.mem_range.mp ha
      omega
    _ = _ := by simp

/-- The explicit common-denominator estimate (3.22). -/
theorem commonDenominator_bound {N n : ℕ} (hn : n + 1 ≤ N) :
    commonDenominator N n ≤ 2^(n + 1) * (n + 1)^(n + 1) * N^(2 * n + 1) := by
  have hN : N + 1 ≤ 2 * N := by omega
  have hL : smallLCM n ≤ (n + 1)^(n + 1) :=
    (smallLCM_le_factorial n).trans (Nat.factorial_le_pow _)
  calc
    _ ≤ (2 * N) * (n + 1)^(n + 1) * N^n * (2 * N)^n :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hN hL)
        (fallingProduct_le_pow N n)) (risingProduct_le_pow hn)
    _ = _ := by simp [pow_succ, pow_add, two_mul]; ring

/-- The exact number of faces in the Hahn construction. -/
def hahnFaces (n : ℕ) : ℕ := commonDenominator (gridSize n) n * (gridSize n)^(n - 1)

theorem hahnFaces_pos {n : ℕ} (hn : 1 ≤ n) : 0 < hahnFaces n := by
  apply Nat.mul_pos (commonDenominator_pos (le_gridSize n))
  apply pow_pos
  unfold gridSize
  positivity

/-- The finite inequality underlying the main asymptotic bound. -/
theorem hahnFaces_bound {n : ℕ} (hn : 1 ≤ n) :
    hahnFaces n ≤ 2^(n + 1) * (n + 1)^(n + 1) * (gridSize n)^(3 * n) := by
  have hgrid : n + 1 ≤ gridSize n := by unfold gridSize; nlinarith
  calc
    _ ≤ (2^(n + 1) * (n + 1)^(n + 1) * (gridSize n)^(2 * n + 1)) *
        (gridSize n)^(n - 1) := Nat.mul_le_mul_right _ (commonDenominator_bound hgrid)
    _ = _ := by
      rw [Nat.mul_assoc, ← pow_add]
      congr 1
      congr 1
      omega

/-- A deliberately loose polynomial-power bound that avoids asymptotic
notation and is convenient for the final logarithmic estimate. -/
theorem hahnFaces_le_power {n : ℕ} (hn : 2 ≤ n) : hahnFaces n ≤ n^(14 * n) := by
  have hquad : n + 2 ≤ n^2 := by
    have := Nat.mul_le_mul_left n hn
    nlinarith
  have hgrid : gridSize n ≤ n^3 := by
    have := Nat.mul_le_mul_left n hquad
    unfold gridSize
    nlinarith
  calc
    _ ≤ 2^(n + 1) * (n + 1)^(n + 1) * (gridSize n)^(3 * n) := hahnFaces_bound (by omega)
    _ ≤ n^(n + 1) * (n^2)^(n + 1) * (n^3)^(3 * n) :=
      Nat.mul_le_mul
        (Nat.mul_le_mul (Nat.pow_le_pow_left hn _) (Nat.pow_le_pow_left (by omega) _))
        (Nat.pow_le_pow_left hgrid _)
    _ = n^(12 * n + 3) := by rw [← pow_mul, ← pow_mul, ← pow_add, ← pow_add]; congr 1; ring
    _ ≤ n^(14 * n) := Nat.pow_le_pow_right (by omega) (by omega)

/-- An explicit `2^{O(n log n)}` statement, using the integer base-two logarithm. -/
theorem hahnFaces_exponential_bound {n : ℕ} (hn : 2 ≤ n) :
    hahnFaces n ≤ 2^(28 * n * Nat.log 2 n) := by
  have hlog : 0 < Nat.log 2 n := Nat.log_pos (by omega) hn
  have hnlog : n ≤ 2^(2 * Nat.log 2 n) :=
    (Nat.lt_pow_succ_log_self (by omega : 1 < 2) n).le.trans
      (Nat.pow_le_pow_right (by omega) (by omega))
  calc
    _ ≤ n^(14 * n) := hahnFaces_le_power hn
    _ ≤ (2^(2 * Nat.log 2 n))^(14 * n) := Nat.pow_le_pow_left hnlog _
    _ = _ := by rw [← pow_mul]; congr 1; ring

end FairDice
