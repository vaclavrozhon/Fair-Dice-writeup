import FairDice.GoFirst

namespace FairDice

variable {α : Type*} [DecidableEq α] [Fintype α]

theorem sum_upper_ranks (f : α → ℕ) (hf : Function.Injective f) :
    2 * (∑ a : α, ((Finset.univ : Finset α).filter (fun b => f a ≤ f b)).card) =
      Fintype.card α * (Fintype.card α + 1) := by
  classical
  simp only [Finset.card_filter]
  have hpair (a b : α) :
      (if f a ≤ f b then 1 else 0) + (if f b ≤ f a then 1 else 0) =
        (1 + if a = b then 1 else 0 : ℕ) := by
    by_cases h : a = b
    · simp [h]
    · have hn : f a ≠ f b := fun he => h (hf he)
      simp only [h, if_false]
      split <;> split <;> omega
  calc
    _ = (∑ a : α, ∑ b : α, if f a ≤ f b then 1 else 0) +
        (∑ a : α, ∑ b : α, if f b ≤ f a then 1 else 0) := by
      rw [Finset.sum_comm (f := fun a b : α => if f b ≤ f a then 1 else 0)]
      omega
    _ = ∑ a : α, ∑ b : α,
        ((if f a ≤ f b then 1 else 0) + (if f b ≤ f a then 1 else 0)) := by
      simp only [Finset.sum_add_distrib]
    _ = _ := by simp [hpair, Finset.sum_add_distrib, Nat.mul_add]

/-- The matching lower bound in Theorem 5.1, including unequal-sided dice. -/
theorem goFirst_length_lower {s : List α} (hs : GoFirstFair s) :
    Fintype.card α * (Fintype.card α + 1) / 2 ≤ s.length := by
  classical
  have hbound (a : α) :
      ((Finset.univ : Finset α).filter (fun b => s.idxOf a ≤ s.idxOf b)).card ≤ s.count a := by
    have hi : s.idxOf a < s.length := List.idxOf_lt_length_iff.mpr (hs.1 a)
    have heq : s = s.take (s.idxOf a) ++ a :: s.drop (s.idxOf a + 1) := by
      conv_lhs => rw [← List.take_append_drop (s.idxOf a) s]
      rw [List.drop_eq_getElem_cons hi, List.getElem_idxOf hi]
    have hnot : a ∉ s.take (s.idxOf a) := by
      rw [List.mem_take_iff_idxOf_lt (hs.1 a)]
      omega
    have h := goFirst_first_occurrence_bound hs heq hnot
    have hfilter : (Finset.univ.filter (fun b => b ∉ s.take (s.idxOf a))) =
        Finset.univ.filter (fun b => s.idxOf a ≤ s.idxOf b) := by
      ext b
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        List.mem_take_iff_idxOf_lt (hs.1 b), not_lt]
    rwa [hfilter] at h
  have hsum := Finset.sum_le_sum (fun a (_ : a ∈ (Finset.univ : Finset α)) => hbound a)
  rw [sum_multiplicities] at hsum
  have hrank := sum_upper_ranks (fun a => s.idxOf a)
    (fun a b hab => (List.idxOf_inj (hs.1 a)).mp hab)
  omega

end FairDice
