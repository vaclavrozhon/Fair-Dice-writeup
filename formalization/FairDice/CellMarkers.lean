import FairDice.FiniteCells

namespace FairDice

variable {α : Type*} [DecidableEq α]

local instance : BEq (Option α) := instBEqOfDecidableEq

/-- Insert a specified number of distinguished faces at each boundary of
an arbitrary list of finite cell words. -/
def insertCellGaps : List (List α) → (ℕ → ℕ) → List (Option α)
  | [],k => List.replicate (k 0) none
  | b::bs,k => List.replicate (k 0) none++b.map some++insertCellGaps bs (fun i => k (i+1))

omit [DecidableEq α] in
theorem insertCellGaps_old (bs : List (List α)) (k : ℕ → ℕ) :
    (insertCellGaps bs k).filterMap id=bs.flatten := by
  induction bs generalizing k with
  | nil => simp [insertCellGaps]
  | cons b bs ih =>
    simp [insertCellGaps,List.filterMap_map]
    exact ih _

theorem insertCellGaps_some (bs : List (List α)) (k : ℕ → ℕ) (a : α) :
    (insertCellGaps bs k).count (some a)=bs.flatten.count a := by
  have hh := count_some [a] (insertCellGaps bs k)
  simpa only [List.map_cons,List.map_nil,count_singleton,insertCellGaps_old] using hh

/-- The exact distinguished-face decomposition for unequal cell blocks. -/
theorem markedCount_insertCellGaps (bs : List (List α)) (k : ℕ → ℕ) (p q : List α) :
    markedCount p q (insertCellGaps bs k)=
      ∑ i ∈ Finset.range (bs.length+1), k i*count p (bs.take i).flatten*count q (bs.drop i).flatten := by
  induction bs generalizing p k with
  | nil =>
    have hg := markedCount_gap p q (k 0) []
    simp only [List.append_nil] at hg
    rw [insertCellGaps,hg]
    cases p <;> cases q <;> simp [markedCount_empty_word]
  | cons b bs ih =>
    rw [insertCellGaps,List.append_assoc,markedCount_gap,markedCount_prefix]
    simp_rw [ih]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    conv_rhs => rw [List.length_cons,Finset.sum_range_succ']
    have hprefix : count (q.map some) (b.map some++insertCellGaps bs (fun i => k (i+1)))=
        count q (b::bs).flatten := by
      rw [count_some]
      simp [List.filterMap_append,List.filterMap_map]
      change count q (b++(insertCellGaps bs (fun i => k (i+1))).filterMap id)=count q (b++bs.flatten)
      rw [insertCellGaps_old]
    rw [hprefix]
    have hterms (i : ℕ) :
        (∑ j ∈ Finset.range (p.length+1), count (p.take j) b*
          (k (i+1)*count (p.drop j) (bs.take i).flatten*count q (bs.drop i).flatten))=
        k (i+1)*count p ((b::bs).take (i+1)).flatten*count q ((b::bs).drop (i+1)).flatten := by
      rw [List.take_succ_cons,List.drop_succ_cons,List.flatten_cons,count_append]
      simp only [Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring
    simp_rw [hterms]
    simp only [List.take_zero,List.drop_zero,List.flatten_nil,count_empty_word]
    by_cases hp : p=[] <;> simp [hp,Nat.add_comm]

theorem insertCellGaps_none (bs : List (List α)) (k : ℕ → ℕ) :
    (insertCellGaps bs k).count none=∑ i ∈ Finset.range (bs.length+1), k i := by
  simpa [markedCount] using markedCount_insertCellGaps bs k [] []

end FairDice
