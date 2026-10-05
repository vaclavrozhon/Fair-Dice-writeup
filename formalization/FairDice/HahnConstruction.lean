import FairDice.InsertionFairness
import FairDice.Bernstein
import FairDice.SizeBounds

namespace FairDice

open Polynomial

/-- A positive rational quadrature rule, together with its proved common
denominator. `HahnExternal` supplies none of these conclusions directly. -/
structure RationalRule (N n : ℕ) where
  weight : Fin (N + 1) → ℚ
  denominator : ℕ
  denominator_pos : 0 < denominator
  weight_pos : ∀ i, 0 < weight i
  clears : ∀ i, Clears denominator (weight i)
  exactness : ∀ p : ℚ[X], p.natDegree ≤ n →
    ∑ i : Fin (N + 1), weight i * p.eval (i.val : ℚ) = polynomialIntegral N p

theorem RationalRule.weight_sum {N n : ℕ} (R : RationalRule N n) :
    ∑ i, R.weight i = N := by simpa using R.exactness 1 (by simp)

noncomputable def hahnRule (h : HahnExternal) (n : ℕ) (hn : 1 ≤ n) :
    RationalRule (gridSize n) n where
  weight := hahnWeight (gridSize n) n
  denominator := commonDenominator (gridSize n) n
  denominator_pos := commonDenominator_pos (le_gridSize n)
  weight_pos := hahnWeight_pos h hn
  clears := hahnWeight_denominator h (le_gridSize n)
  exactness := hahnWeight_exact h (le_gridSize n)

theorem RationalRule.integer_gaps {N n F : ℕ} (R : RationalRule N n)
    (hF : 0 < F) (hdiv : R.denominator ∣ F) :
    ∃ k : Fin (N + 1) → ℕ, (∀ i, 0 < k i) ∧
      (∀ i, (k i : ℚ) = F * R.weight i) ∧ ∑ i, k i = N * F := by
  classical
  have hki (i : Fin (N + 1)) : ∃ k : ℕ, 0 < k ∧ (k : ℚ) = F * R.weight i :=
    positive_integer_weight hF (R.weight_pos i) ((R.clears i).of_dvd hdiv)
  choose k hk heq using hki
  refine ⟨k, hk, heq, ?_⟩
  have hsum : ∑ i, (k i : ℚ) = (N : ℚ) * F := by
    simp only [heq, ← Finset.mul_sum, R.weight_sum]
    ring
  exact_mod_cast hsum

section Insertion

variable {α : Type*} [DecidableEq α] [Fintype α]
local instance instBEqOptionHahnConstruction : BEq (Option α) := instBEqOfDecidableEq

/-- One insertion step, including positivity, integrality, fairness and the
new equal face count. The same rule can be reused at every smaller degree. -/
theorem RationalRule.insert {N n F : ℕ} (R : RationalRule N n)
    (hN : 0 < N) (hF : 0 < F) (hdiv : R.denominator ∣ F)
    (hr : Fintype.card α ≤ n) {s : List α} (hs : PermutationFair s)
    (hc : ∀ a, s.count a = F) :
    ∃ t : List (Option α), PermutationFair t ∧ ∀ a, t.count a = N * F := by
  obtain ⟨k, hk, heq, hsum⟩ := R.integer_gaps hF hdiv
  refine ⟨insertGaps s N k, ?_, ?_⟩
  · apply insertion_fair_of_moments hs F hc N hN k
      (by rw [hsum]; exact Nat.mul_pos hN hF)
      ((F : ℚ) * (N : ℚ)^(Fintype.card α + 1) / (Fintype.card α + 1).factorial)
    intro j hj
    have hquad := R.exactness (rankPolynomial N (Fintype.card α) j)
      ((rankPolynomial_degree N hj).trans hr)
    rw [polynomialIntegral_rank N (by exact_mod_cast Nat.ne_of_gt hN) hj] at hquad
    calc
      _ = (F : ℚ) * ∑ i : Fin (N + 1), R.weight i *
          (rankPolynomial N (Fintype.card α) j).eval (i.val : ℚ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [heq, rankPolynomial_eval]
        ring
      _ = _ := by rw [hquad]; ring
  · intro a
    cases a with
    | none => rw [insertGaps_new_multiplicity, hsum]
    | some a => rw [insertGaps_old_multiplicity, hc]

end Insertion

theorem singleton_alphabet_fair (M : ℕ) (hM : 0 < M) :
    PermutationFair (List.replicate M (0 : Fin 1)) := by
  constructor
  · intro a
    have ha : a = 0 := Fin.ext (by have := a.isLt; omega)
    simp [ha, Nat.ne_of_gt hM]
  · intro p q _ _ hp hq
    obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp (by simpa using hp)
    obtain ⟨b, rfl⟩ := List.length_eq_one_iff.mp (by simpa using hq)
    rw [Subsingleton.elim a b]

/-- Reuse one rule from one die up to the target alphabet size. -/
theorem RationalRule.construct {N n : ℕ} (R : RationalRule N n) (hN : 0 < N)
    (r : ℕ) (hr : r + 1 ≤ n) :
    ∃ s : List (Fin (r + 1)), PermutationFair s ∧
      ∀ a, s.count a = R.denominator * N^r := by
  induction r with
  | zero =>
    refine ⟨List.replicate R.denominator 0,
      singleton_alphabet_fair _ R.denominator_pos, ?_⟩
    intro a
    have ha : a = 0 := Fin.ext (by have := a.isLt; omega)
    simp [ha]
  | succ r ih =>
    obtain ⟨s, hs, hc⟩ := ih (by omega)
    have hF : 0 < R.denominator * N^r := Nat.mul_pos R.denominator_pos (pow_pos hN _)
    obtain ⟨t, ht, htc⟩ := R.insert hN hF (dvd_mul_right _ _) (by simpa using (show r + 1 ≤ n by omega)) hs hc
    let e := (finSuccEquiv (r + 1)).symm
    refine ⟨t.map e, permutationFair_relabel e ht, ?_⟩
    intro a
    have hm := count_relabel e [a] t
    simpa [htc, pow_succ, Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hm

/-- The main Hahn-construction theorem, with the explicit face count in the
paper. The only unproved inputs are the named classical Hahn facts. -/
theorem hahn_construction (h : HahnExternal) (n : ℕ) (hn : 1 ≤ n) :
    ∃ s : List (Fin n), PermutationFair s ∧ FairUpTo n s ∧
      (∀ a, s.count a = hahnFaces n) ∧
      hahnFaces n ≤ 2^(n + 1) * (n + 1)^(n + 1) * (gridSize n)^(3 * n) := by
  cases n with
  | zero => omega
  | succ m =>
    have hN : 0 < gridSize (m + 1) := by unfold gridSize; positivity
    obtain ⟨s, hs, hc⟩ := (hahnRule h (m + 1) hn).construct hN m (by omega)
    have hc' : ∀ a, s.count a = hahnFaces (m + 1) := by
      simpa [hahnFaces, hahnRule] using hc
    refine ⟨s, hs, ?_, hc', hahnFaces_bound hn⟩
    simpa using equal_full_to_partial hs (hahnFaces (m + 1)) hc'

end FairDice
