import FairDice.HahnConstruction
import FairDice.ManyLarge
import FairDice.Staircase
import FairDice.Multigrade

namespace FairDice

theorem hahn_construction_exponential (h : HahnExternal) (n : ℕ) (hn : 2 ≤ n) :
    ∃ s : List (Fin n), PermutationFair s ∧ FairUpTo n s ∧
      (∀ a, s.count a = hahnFaces n) ∧ hahnFaces n ≤ 2^(28 * n * Nat.log 2 n) := by
  obtain ⟨s, hs, hf, hc, _⟩ := hahn_construction h n (by omega)
  exact ⟨s, hs, hf, hc, hahnFaces_exponential_bound hn⟩

theorem elementary_faces_exponential {n : ℕ} (hn : 2 ≤ n) :
    n.factorial^(n - 1) ≤ 2^(2 * n^2 * Nat.log 2 n) := by
  have hlog : 0 < Nat.log 2 n := Nat.log_pos (by omega) hn
  have hnlog : n ≤ 2^(2 * Nat.log 2 n) :=
    (Nat.lt_pow_succ_log_self (by omega : 1 < 2) n).le.trans
      (Nat.pow_le_pow_right (by omega) (by omega))
  calc
    _ ≤ (n^n)^(n - 1) := Nat.pow_le_pow_left (Nat.factorial_le_pow n) _
    _ ≤ (n^n)^n := Nat.pow_le_pow_right (by positivity) (by omega)
    _ = n^(n^2) := by rw [← pow_mul, pow_two]
    _ ≤ (2^(2 * Nat.log 2 n))^(n^2) := Nat.pow_le_pow_left hnlog _
    _ = _ := by rw [← pow_mul]; congr 1; ring

/-- The informal lower-bound theorem in the introduction, for the largest
individual die rather than only the total word length. -/
theorem exists_exponentially_large_die (hext : PrimorialExternal) :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ (α : Type) [DecidableEq α] [Fintype α]
      (s : List α), n₀ ≤ Fintype.card α → PermutationFair s →
      ∃ a : α, (2 : ℝ)^(c * Fintype.card α) ≤ s.count a := by
  obtain ⟨c, hc, hall⟩ := many_large_exponential hext
  obtain ⟨n₀, hlarge⟩ := hall (1 / 2) (by norm_num) (by norm_num)
  refine ⟨c / 2, by positivity, max 1 n₀, ?_⟩
  intro α _ _ s hn hs
  classical
  have hh := hlarge α s (by omega) hs
  have hnR : (1 : ℝ) ≤ Fintype.card α := by exact_mod_cast (show 1 ≤ Fintype.card α by omega)
  have hcard : 0 < ((Finset.univ : Finset α).filter (fun a =>
      (2 : ℝ)^(c * (1 / 2) * Fintype.card α) ≤ s.count a)).card := by
    have hpos : (0 : ℝ) < (((Finset.univ : Finset α).filter (fun a =>
      (2 : ℝ)^(c * (1 / 2) * Fintype.card α) ≤ s.count a)).card : ℝ) := by nlinarith
    exact_mod_cast hpos
  obtain ⟨a, ha⟩ := Finset.card_pos.mp hcard
  refine ⟨a, ?_⟩
  simpa [div_eq_mul_inv] using (Finset.mem_filter.mp ha).2

/-- Exact optimum, stated as existence of a minimizer and a matching bound
on every competitor. -/
theorem goFirst_optimum (n : ℕ) (hn : 0 < n) :
    (∃ s : List (Fin n), GoFirstFair s ∧ s.length = n * (n + 1) / 2) ∧
      ∀ s : List (Fin n), GoFirstFair s → n * (n + 1) / 2 ≤ s.length := by
  constructor
  · obtain ⟨s, hs, hl⟩ := staircase_construction n hn
    exact ⟨s, hs, by omega⟩
  · intro s hs
    simpa using goFirst_length_lower hs

end FairDice
