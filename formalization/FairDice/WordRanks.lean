import FairDice.ArithmeticRemarks

namespace FairDice

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- Outcomes with `a` in zero-based rank `k`: permute the other letters and
insert `a` at that rank. This also works for unequal face counts. -/
noncomputable def wordRankCount (s : List α) (a : α) (k : ℕ) : ℕ :=
  (((Finset.univ.erase a).toList.permutations').map
    (fun p => count (p.insertIdx k a) s)).sum

def WordPlaceFair (s : List α) : Prop :=
  (∀ a : α, a ∈ s) ∧
    ∀ k < Fintype.card α, ∀ a b : α, wordRankCount s a k = wordRankCount s b k

def HereditaryPlaceFair (s : List α) : Prop :=
  ∀ A : Finset α, A.Nonempty → WordPlaceFair (restrict A s)

theorem wordRankCount_zero (s : List α) (a : α) : wordRankCount s a 0 = winCount a s := by
  simp only [wordRankCount, List.insertIdx_zero, winCount_eq_pattern_sum]

theorem wordPlaceFair_goFirstFair {s : List α} (hs : WordPlaceFair s) : GoFirstFair s := by
  refine ⟨hs.1, ?_⟩
  intro a b
  have hn : 0 < Fintype.card α := Fintype.card_pos_iff.mpr ⟨a⟩
  simpa only [wordRankCount_zero] using hs.2 0 hn a b

omit [Fintype α] in
theorem hereditaryPlaceFair_goFirstFair {s : List α} (hs : HereditaryPlaceFair s) :
    HereditaryGoFirstFair s := fun A hA => wordPlaceFair_goFirstFair (hs A hA)

theorem hereditaryPlace_prime_product {s : List α} (hs : HereditaryPlaceFair s) :
    (∏ p ∈ (Finset.range (Fintype.card α + 1)).filter Nat.Prime,
      p^(Fintype.card α + 1 - p)) ≤ outcomeCount s :=
  hereditary_prime_product (hereditaryPlaceFair_goFirstFair hs)

theorem hereditaryPlace_equal_primorial_dvd {s : List α} (hs : HereditaryPlaceFair s)
    (m : ℕ) (hm : ∀ a, s.count a = m) : primorial (Fintype.card α) ∣ m :=
  hereditary_equal_primorial_dvd (hereditaryPlaceFair_goFirstFair hs) m hm

theorem hereditaryPlace_exponentially_large_die (hext : PrimorialExternal) :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ (α : Type) [DecidableEq α] [Fintype α]
      (s : List α), n₀ ≤ Fintype.card α → HereditaryPlaceFair s →
      ∃ a : α, (2 : ℝ)^(c * Fintype.card α) ≤ s.count a := by
  obtain ⟨c, hc, n₀, h⟩ := hereditary_exponentially_large_die hext
  exact ⟨c, hc, n₀, fun α _ _ s hn hs => h α s hn (hereditaryPlaceFair_goFirstFair hs)⟩

end FairDice
