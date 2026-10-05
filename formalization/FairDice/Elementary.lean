import FairDice.Symmetrization

namespace FairDice

/-- Start from one copy of each letter and perform `rounds` symmetrizations. -/
noncomputable def elementaryStage (n : ℕ) : ℕ → List (Fin n)
  | 0 => List.finRange n
  | r + 1 => symmetrize (elementaryStage n r)

theorem fairUpTo_finRange (n : ℕ) : FairUpTo 1 (List.finRange n) := by
  intro j hj
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hj with rfl | rfl
  · exact fairAt_zero _
  · intro p q _ _ hp hq
    obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hp
    obtain ⟨b, rfl⟩ := List.length_eq_one_iff.mp hq
    simp only [count_singleton]
    rw [List.count_eq_one_of_mem (List.nodup_finRange n) (List.mem_finRange a),
      List.count_eq_one_of_mem (List.nodup_finRange n) (List.mem_finRange b)]

theorem fairUpTo_elementaryStage (n r : ℕ) :
    FairUpTo (r + 1) (elementaryStage n r) := by
  induction r with
  | zero => exact fairUpTo_finRange n
  | succ r ih => exact fairUpTo_symmetrize ih

theorem length_elementaryStage (n r : ℕ) :
    (elementaryStage n r).length = n * n.factorial ^ r := by
  induction r with
  | zero => simp [elementaryStage]
  | succ r ih => simp [elementaryStage, length_symmetrize, ih, pow_succ, Nat.mul_assoc]

theorem count_symmetrize_of_constant {α : Type*} [DecidableEq α] [Fintype α]
    (s : List α) (c : ℕ) (hc : ∀ a, s.count a = c) (a : α) :
    (symmetrize s).count a = (Fintype.card α).factorial * c := by
  classical
  have hmap : ∀ e : Equiv.Perm α, (s.map e).count a = c := by
    intro e
    simpa only [List.map_cons, List.map_nil, count_singleton, hc] using
      count_relabel e [a] s
  simp [symmetrize, List.count_flatten, List.map_map, Function.comp_def,
    hmap, List.map_const', List.sum_replicate, Fintype.card_perm]

theorem count_elementaryStage (n r : ℕ) (a : Fin n) :
    (elementaryStage n r).count a = n.factorial ^ r := by
  induction r with
  | zero =>
    simp [elementaryStage, List.count_eq_one_of_mem (List.nodup_finRange n) (List.mem_finRange a)]
  | succ r ih =>
    have hall : ∀ b : Fin n, (elementaryStage n r).count b = n.factorial ^ r := by
      intro b
      have hfair := fairUpTo_elementaryStage n r 1 (by omega)
      have heq := hfair [b] [a] (by simp) (by simp) (by simp) (by simp)
      simpa [ih] using heq
    simpa [elementaryStage, pow_succ, Nat.mul_comm] using
      count_symmetrize_of_constant (elementaryStage n r) (n.factorial ^ r) hall a

/-- The word in Theorem 2.8. Letters are `0,...,n-1` in Lean. -/
noncomputable def elementaryWord (n : ℕ) : List (Fin n) := elementaryStage n (n - 1)

/-- Theorem 2.8, including the exact number of faces on every die. -/
theorem elementary_construction (n : ℕ) (hn : 0 < n) :
    PermutationFair (elementaryWord n) ∧
    FairUpTo n (elementaryWord n) ∧
    (elementaryWord n).length = n * n.factorial ^ (n - 1) ∧
    ∀ a : Fin n, (elementaryWord n).count a = n.factorial ^ (n - 1) := by
  have hfair : FairUpTo n (elementaryWord n) := by
    simpa [elementaryWord, Nat.sub_add_cancel hn] using fairUpTo_elementaryStage n (n - 1)
  have hc := count_elementaryStage n (n - 1)
  refine ⟨⟨?_, ?_⟩, hfair, length_elementaryStage n (n - 1), hc⟩
  · intro a
    apply List.count_pos_iff.mp
    change 0 < (elementaryStage n (n - 1)).count a
    rw [hc]
    exact pow_pos (Nat.factorial_pos n) _
  · simpa using hfair n le_rfl

end FairDice
