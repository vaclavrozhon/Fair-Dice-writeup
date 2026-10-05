import FairDice.GoFirstLower

namespace FairDice

variable {α : Type*} [DecidableEq α] [Fintype α]

theorem prefix_outcome_bound (a : α) (u v : List α) (ha : a ∉ u) :
    outcomeCount (a :: v) ≤ (u ++ a :: v).count a * winCount a (u ++ a :: v) := by
  have hf : (u ++ a :: v).count a = (a :: v).count a := by
    simp [List.count_append, List.count_eq_zero.mpr ha]
  rw [hf, winCount_prefix_of_not_mem a u _ ha]
  unfold outcomeCount
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ a)]
  apply Nat.mul_le_mul_left
  rw [winCount, if_pos rfl]
  have he : (∏ b ∈ Finset.univ.erase a, (a :: v).count b) =
      ∏ b ∈ Finset.univ.erase a, v.count b := by
    apply Finset.prod_congr rfl
    intro b hb
    simp [Ne.symm (Finset.mem_erase.mp hb).1]
  rw [he]
  omega

/-- Equation (5.12), with no exact fairness hypothesis. `δ` bounds all
first-place probabilities, and `u` is the prefix before the first face of
the prescribed die. -/
theorem approximate_first_occurrence_bound {s u v : List α} {a : α}
    (hpos : ∀ b : α, b ∈ s) (heq : s = u ++ a :: v) (ha : a ∉ u)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hwin : ∀ b : α, (winCount b s : ℝ) ≤
      (1 + δ) / Fintype.card α * outcomeCount s) :
    max 0 ((Fintype.card α : ℝ) / (1 + δ) - u.toFinset.card) ≤ s.count a := by
  classical
  letI : Nonempty α := ⟨a⟩
  let O : ℝ := outcomeCount s
  let q : ℝ := (1 + δ) / Fintype.card α
  let S := (Finset.univ : Finset α).filter (fun b => b ∈ u)
  let T := (Finset.univ : Finset α).filter (fun b => b ∉ u)
  have hO : 0 < O := by
    dsimp [O]
    exact_mod_cast (Finset.prod_pos (fun b (_ : b ∈ (Finset.univ : Finset α)) =>
      List.count_pos_iff.mpr (hpos b)) : 0 < outcomeCount s)
  have hn : (0 : ℝ) < Fintype.card α := by exact_mod_cast Fintype.card_pos (α := α)
  have hq : 0 < q := div_pos (by linarith) hn
  have hsumS : (∑ b ∈ S, (winCount b s : ℝ)) ≤ S.card * (q * O) := by
    simpa using Finset.sum_le_sum (fun b (_ : b ∈ S) => hwin b)
  have hsumT : (∑ b ∈ T, (winCount b s : ℝ)) ≤ outcomeCount (a :: v) := by
    have hN : (∑ b ∈ T, winCount b s) ≤ outcomeCount (a :: v) := by
      calc
        _ = ∑ b ∈ T, winCount b (a :: v) := by
          apply Finset.sum_congr rfl
          intro b hb
          rw [heq, winCount_prefix_of_not_mem b u _ (Finset.mem_filter.mp hb).2]
        _ ≤ ∑ b : α, winCount b (a :: v) := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
        _ = _ := sum_winCount _
    exact_mod_cast hN
  have hsum : (∑ b ∈ S, (winCount b s : ℝ)) + (∑ b ∈ T, (winCount b s : ℝ)) = O := by
    have hp := Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset α))
      (fun b => b ∈ u) (fun b => winCount b s)
    rw [sum_winCount] at hp
    dsimp [S, T, O]
    exact_mod_cast hp
  have hout : (outcomeCount (a :: v) : ℝ) ≤ (s.count a : ℝ) * winCount a s := by
    have hh := prefix_outcome_bound a u v ha
    rw [← heq] at hh
    exact_mod_cast hh
  have hw := mul_le_mul_of_nonneg_left (hwin a) (show (0 : ℝ) ≤ s.count a by positivity)
  have hmain : O ≤ ((s.count a : ℝ) + S.card) * q * O := by nlinarith
  have hcancel : 1 ≤ ((s.count a : ℝ) + S.card) * q := by
    exact (mul_le_mul_iff_left₀ hO).mp (by nlinarith [hmain])
  have hS : S.card = u.toFinset.card := by
    congr 1
    ext b
    simp [S]
  apply max_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have hb : (Fintype.card α : ℝ) ≤ ((s.count a : ℝ) + S.card) * (1 + δ) := by
    dsimp [q] at hcancel
    have hh := (le_div_iff₀ hn).mp (show 1 ≤ (((s.count a : ℝ) + S.card) * (1 + δ)) /
      Fintype.card α by simpa [mul_div_assoc] using hcancel)
    simpa using hh
  have hh := (div_le_iff₀ (by linarith : 0 < 1 + δ)).mpr hb
  rw [hS] at hh
  linarith

end FairDice
