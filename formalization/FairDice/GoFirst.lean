import FairDice.Probability
import FairDice.Equalization

namespace FairDice

variable {α : Type*} [DecidableEq α] [Fintype α]

def outcomeCount (s : List α) : ℕ := ∏ a : α, s.count a

/-- Count outcomes by their first selected position. At a position labeled
`a`, all other dice must select a later position. -/
def winCount (a : α) : List α → ℕ
  | [] => 0
  | b :: s => winCount a s + if a = b then
      ∏ c ∈ Finset.univ.erase a, s.count c else 0

def GoFirstFair (s : List α) : Prop :=
  (∀ a : α, a ∈ s) ∧ ∀ a b : α, winCount a s = winCount b s

theorem outcomeCount_cons (a : α) (s : List α) :
    outcomeCount (a :: s) = outcomeCount s + ∏ b ∈ Finset.univ.erase a, s.count b := by
  have ho : (∏ b ∈ Finset.univ.erase a, (a :: s).count b) =
      ∏ b ∈ Finset.univ.erase a, s.count b := by
    apply Finset.prod_congr rfl
    intro b hb
    simp [Ne.symm (Finset.mem_erase.mp hb).1]
  unfold outcomeCount
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ a), ho,
    List.count_cons_self, Nat.add_mul]
  rw [Finset.mul_prod_erase Finset.univ (fun b => s.count b) (Finset.mem_univ a)]
  simp

theorem sum_winCount [Nonempty α] (s : List α) :
    ∑ a : α, winCount a s = outcomeCount s := by
  induction s with
  | nil => simp [winCount, outcomeCount]
  | cons b s ih =>
    simp only [winCount, Finset.sum_add_distrib, ih, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    exact (outcomeCount_cons b s).symm

theorem winCount_eq_pattern_sum (a : α) (s : List α) :
    winCount a s = (((Finset.univ.erase a).toList.permutations').map
      (fun p => count (a :: p) s)).sum := by
  induction s with
  | nil => simp [winCount]
  | cons b s ih =>
    simp only [winCount, count_cons_cons, ih, List.sum_map_add]
    by_cases hab : a = b
    · simp only [hab, if_true]
      rw [sum_permutation_counts _ _ (Finset.nodup_toList _)]
      rw [Finset.prod_map_toList]
    · simp [hab]

theorem permutationFair_goFirstFair {s : List α} (hs : PermutationFair s) :
    GoFirstFair s := by
  refine ⟨hs.1, ?_⟩
  intro a b
  letI : Nonempty α := ⟨a⟩
  have hcard : 0 < Fintype.card α := Fintype.card_pos
  have hterm (x : α) :
      winCount x s = ((Finset.univ.erase x).card).factorial *
        count (a :: (Finset.univ.erase a).toList) s := by
    rw [winCount_eq_pattern_sum]
    have hconst (p : List α) (hp : p ∈ (Finset.univ.erase x).toList.permutations') :
        count (x :: p) s = count (a :: (Finset.univ.erase a).toList) s := by
      have hperm := List.mem_permutations'.mp hp
      apply hs.2
      · apply List.nodup_cons.mpr
        constructor
        · intro hx
          have hx' := hperm.mem_iff.mp hx
          simp at hx'
        · exact hperm.nodup_iff.mpr (Finset.nodup_toList _)
      · simp [Finset.nodup_toList]
      · simp [hperm.length_eq]; omega
      · simp; omega
    rw [List.map_congr_left hconst]
    simp [List.map_const', List.sum_replicate, List.length_permutations,
      ← (List.permutations_perm_permutations' _).length_eq]
  rw [hterm a, hterm b]
  simp

theorem winCount_prefix_of_not_mem (a : α) (u v : List α) (ha : a ∉ u) :
    winCount a (u ++ v) = winCount a v := by
  induction u with
  | nil => rfl
  | cons b u ih =>
    simp only [List.mem_cons, not_or] at ha
    simp [winCount, ha.1, ih ha.2]

/-- The exact finite inequality behind the first-occurrence lower bound.
The die first appearing after prefix `u` has at least as many faces as there
are letters not yet seen in `u`. -/
theorem goFirst_first_occurrence_bound {s u v : List α} {a : α}
    (hs : GoFirstFair s) (heq : s = u ++ a :: v) (ha : a ∉ u) :
    ((Finset.univ : Finset α).filter (fun b => b ∉ u)).card ≤ s.count a := by
  classical
  letI : Nonempty α := ⟨a⟩
  let S := (Finset.univ : Finset α).filter (fun b => b ∉ u)
  let C := winCount a s
  have hsum : S.card * C ≤ outcomeCount (a :: v) := by
    calc
      _ = ∑ b ∈ S, winCount b (a :: v) := by
        have hconst (b : α) (hb : b ∈ S) : winCount b (a :: v) = C := by
          rw [← winCount_prefix_of_not_mem b u (a :: v) (Finset.mem_filter.mp hb).2,
            ← heq]
          exact hs.2 b a
        simp [Finset.sum_congr rfl hconst]
      _ ≤ ∑ b : α, winCount b (a :: v) := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
      _ = _ := sum_winCount _
  have hwin : (∏ b ∈ Finset.univ.erase a, v.count b) ≤ C := by
    dsimp [C]
    rw [heq, winCount_prefix_of_not_mem a u _ ha, winCount]
    simp
  have hfaces : (a :: v).count a = s.count a := by simp [heq, List.count_append, List.count_eq_zero.mpr ha]
  have hothers : (∏ b ∈ Finset.univ.erase a, (a :: v).count b) =
      ∏ b ∈ Finset.univ.erase a, v.count b := by
    apply Finset.prod_congr rfl
    intro b hb
    simp [Ne.symm (Finset.mem_erase.mp hb).1]
  have hprod : outcomeCount (a :: v) ≤ s.count a * C := by
    unfold outcomeCount
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ a), hfaces, hothers]
    exact Nat.mul_le_mul_left _ hwin
  have hC : 0 < C := by
    have hall : 0 < outcomeCount s := Finset.prod_pos (fun b _ => List.count_pos_iff.mpr (hs.1 b))
    have he : outcomeCount s = Fintype.card α * C := by
      rw [← sum_winCount]
      have hc : ∀ b : α, winCount b s = C := fun b => hs.2 b a
      simp [hc]
    rw [he] at hall
    by_contra h
    have hz : C = 0 := by omega
    simp [hz] at hall
  exact Nat.le_of_mul_le_mul_right (hsum.trans hprod) hC

end FairDice
