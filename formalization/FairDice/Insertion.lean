import FairDice.Powers
import FairDice.Blowup

namespace FairDice

variable {α : Type*} [DecidableEq α]

/-- Forget the distinguished new letter, represented by `none`. -/
theorem count_some (p : List α) (s : List (Option α)) :
    count (p.map some) s = count p (s.filterMap id) := by
  induction s generalizing p with
  | nil => cases p <;> simp
  | cons b s ih =>
    cases p with
    | nil => simp
    | cons a p =>
      cases b with
      | none => simpa using ih (a :: p)
      | some b =>
        have hi := ih (a :: p)
        simp only [List.map_cons] at hi ⊢
        simp [hi, ih]

def markedCount (p q : List α) (s : List (Option α)) : ℕ :=
  count (p.map some ++ none :: q.map some) s

theorem markedCount_empty_word (p q : List α) : markedCount p q [] = 0 := by
  cases p <;> simp [markedCount]

/-- When a marker-free block is prefixed, only the part preceding the marker
can take positions from that block. -/
theorem markedCount_prefix (p q s : List α) (t : List (Option α)) :
    markedCount p q (s.map some ++ t) =
      ∑ j ∈ Finset.range (p.length + 1), count (p.take j) s * markedCount (p.drop j) q t := by
  induction s generalizing p with
  | nil =>
    cases p <;> simp [Finset.sum_range_succ', List.take_succ_cons]
  | cons b s ih =>
    cases p with
    | nil => simpa [markedCount] using ih []
    | cons a p =>
      have hrec (u : List (Option α)) :
          markedCount (a :: p) q (some b :: u) =
            markedCount (a :: p) q u + if a = b then markedCount p q u else 0 := by
        simp [markedCount]
      simp only [List.map_cons, List.cons_append, hrec]
      rw [ih (a :: p), ih p]
      simp only [List.length_cons, Finset.sum_range_succ' (n := p.length + 1),
        List.take_zero, List.drop_zero, count_nil, one_mul,
        List.take_succ_cons, List.drop_succ_cons, count_cons_cons]
      by_cases h : a = b
      · simp only [h, if_true, add_mul, Finset.sum_add_distrib]
        omega
      · simp [h]

theorem markedCount_gap (p q : List α) (k : ℕ) (t : List (Option α)) :
    markedCount p q (List.replicate k none ++ t) = markedCount p q t +
      if p = [] then k * count (q.map some) t else 0 := by
  have hnone : (none : Option α) ∉ q.map some := by simp
  induction k with
  | zero => simp
  | succ k ih =>
    cases p with
    | nil =>
      simp only [markedCount, List.map_nil, List.nil_append, List.replicate_succ,
        List.cons_append, count_cons_cons, ite_true] at ih ⊢
      rw [ih, count_replicate_append_of_not_mem _ _ _ _ hnone]
      simp [Nat.add_mul, Nat.add_assoc]
    | cons a p =>
      simpa [markedCount, List.replicate_succ] using ih

def repeatWord (s : List α) (n : ℕ) : List α := (List.replicate n s).flatten

omit [DecidableEq α] in
@[simp] theorem repeatWord_zero (s : List α) : repeatWord s 0 = [] := rfl

omit [DecidableEq α] in
@[simp] theorem repeatWord_succ (s : List α) (n : ℕ) :
    repeatWord s (n + 1) = s ++ repeatWord s n := by simp [repeatWord, List.replicate_succ]

/-- Put `k i` new letters in gap `i` around `N` copies of the old word. -/
def insertGaps (s : List α) : (N : ℕ) → (Fin (N + 1) → ℕ) → List (Option α)
  | 0, k => List.replicate (k 0) none
  | N + 1, k => List.replicate (k 0) none ++ s.map some ++
      insertGaps s N (fun i => k i.succ)

omit [DecidableEq α] in
theorem insertGaps_old_letters (s : List α) (N : ℕ) (k : Fin (N + 1) → ℕ) :
    (insertGaps s N k).filterMap id = repeatWord s N := by
  induction N with
  | zero => simp [insertGaps]
  | succ N ih =>
    simp [insertGaps, List.filterMap_append, List.filterMap_map]
    exact ih _

/-- The exact count underlying both the weighted insertion criterion and the
rational equal-weight design insertion. No fairness assumption is needed. -/
theorem markedCount_insertGaps (s p q : List α) (N : ℕ) (k : Fin (N + 1) → ℕ) :
    markedCount p q (insertGaps s N k) =
      ∑ i : Fin (N + 1), k i * count p (repeatWord s i.val) *
        count q (repeatWord s (N - i.val)) := by
  induction N generalizing p with
  | zero =>
    have hg := markedCount_gap p q (k 0) []
    simp only [List.append_nil] at hg
    rw [insertGaps, hg]
    cases p <;> cases q <;> simp [markedCount_empty_word]
  | succ N ih =>
    rw [insertGaps, List.append_assoc, markedCount_gap, markedCount_prefix]
    simp_rw [ih]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm, Fin.sum_univ_succ (n := N + 1)]
    have hprefix : count (q.map some)
        (s.map some ++ insertGaps s N (fun i => k i.succ)) =
        count q (repeatWord s (N + 1)) := by
      rw [count_some]
      simp [List.filterMap_append, List.filterMap_map]
      exact congrArg (fun t => count q (s ++ t)) (insertGaps_old_letters s N _)
    rw [hprefix]
    have hterms (i : Fin (N + 1)) :
        (∑ j ∈ Finset.range (p.length + 1), count (p.take j) s *
          (k i.succ * count (p.drop j) (repeatWord s i.val) *
            count q (repeatWord s (N - i.val)))) =
        k i.succ * count p (repeatWord s (i.val + 1)) *
          count q (repeatWord s (N - i.val)) := by
      rw [repeatWord_succ, count_append]
      simp only [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring
    simp_rw [hterms]
    simp only [Fin.val_zero, Nat.sub_zero, repeatWord_zero, count_empty_word,
      Fin.val_succ, Nat.succ_sub_succ_eq_sub]
    by_cases hp : p = [] <;> simp [hp, Nat.add_comm]

end FairDice
