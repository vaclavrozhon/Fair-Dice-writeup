import FairDice.GoFirstLower
import FairDice.Elementary

namespace FairDice

variable {α β : Type*} [DecidableEq α] [Fintype α]

theorem prod_erase_eq_ite (f : α → ℕ) (a : α) :
    (∏ b ∈ Finset.univ.erase a, f b) = ∏ b : α, if b = a then 1 else f b := by
  classical
  rw [Finset.prod_ite]
  simp only [Finset.prod_const_one, one_mul]
  congr 1
  ext b
  simp

theorem winCount_relabel [DecidableEq β] [Fintype β] (e : α ≃ β) (a : α) (s : List α) :
    winCount (e a) (s.map e) = winCount a s := by
  induction s with
  | nil => rfl
  | cons b s ih =>
    simp only [List.map_cons, winCount, ih, e.injective.eq_iff]
    congr 1
    congr 1
    rw [prod_erase_eq_ite, prod_erase_eq_ite]
    apply Fintype.prod_equiv e.symm
    intro x
    by_cases hx : x = e a
    · simp [hx]
    · have hx' : e.symm x ≠ a := by
        intro he
        apply hx
        rw [← he, e.apply_symm_apply]
      simp only [hx, hx', if_false]
      have hc := count_relabel e [x] s
      simpa using hc

theorem goFirstFair_relabel [DecidableEq β] [Fintype β] (e : α ≃ β)
    {s : List α} (hs : GoFirstFair s) : GoFirstFair (s.map e) := by
  refine ⟨fun b => List.mem_map.mpr ⟨e.symm b, hs.1 _, e.apply_symm_apply b⟩, ?_⟩
  intro a b
  simpa only [e.apply_symm_apply] using
    (winCount_relabel e (e.symm a) s).trans ((hs.2 _ _).trans (winCount_relabel e (e.symm b) s).symm)

local instance instBEqOptionStaircase : BEq (Option α) := instBEqOfDecidableEq

def staircaseTail (s : List α) (k : ℕ) : List (Option α) :=
  s.map some ++ List.replicate k none

omit [Fintype α] in
theorem staircaseTail_counts (s : List α) (k : ℕ) :
    (staircaseTail s k).count none = k ∧
      ∀ a : α, (staircaseTail s k).count (some a) = s.count a := by
  constructor
  · have hz : (s.map some).count (none : Option α) = 0 := List.count_eq_zero.mpr (by simp)
    simp [staircaseTail, List.count_append, hz]
  · intro a
    have hz : (List.replicate k (none : Option α)).count (some a) = 0 :=
      List.count_eq_zero.mpr (by simp)
    simp [staircaseTail, hz, List.count_map_of_injective s some (Option.some_injective α) a]

theorem staircaseTail_old_wins (s : List α) (k : ℕ) (a : α) :
    winCount (some a) (staircaseTail s k) = k * winCount a s := by
  induction s with
  | nil =>
    induction k with
    | zero => simp [staircaseTail, winCount]
    | succ k ih => simpa [staircaseTail, List.replicate_succ, winCount] using ih
  | cons b s ih =>
    change winCount (some a) (some b :: staircaseTail s k) = _
    rw [winCount, ih, winCount, mul_add]
    by_cases hab : a = b
    · simp only [hab, if_true]
      congr 1
      rw [prod_erase_eq_ite, Fintype.prod_option, prod_erase_eq_ite]
      simp only [Option.some.injEq, reduceCtorEq, if_false, (staircaseTail_counts s k).1]
      congr 1
      apply Finset.prod_congr rfl
      intro c _
      split <;> simp_all [(staircaseTail_counts s k).2]
    · simp [hab]

theorem staircaseTail_new_wins [Nonempty α] (s : List α) (k : ℕ) :
    winCount none (staircaseTail s k) = 0 := by
  induction s with
  | nil =>
    induction k with
    | zero => rfl
    | succ k ih =>
      change winCount none (none :: staircaseTail [] k) = 0
      rw [winCount, ih, if_pos rfl, zero_add, prod_erase_eq_ite, Fintype.prod_option]
      have hz (a : α) : (List.replicate k (none : Option α)).count (some a) = 0 :=
        List.count_eq_zero.mpr (by simp)
      simp [staircaseTail, hz]
  | cons a s ih => simpa [staircaseTail, winCount] using ih

/-- Add the new first letter, followed by the old staircase, followed by
one copy of the new letter for each old die. -/
def staircaseStep (s : List α) : List (Option α) := none :: staircaseTail s (Fintype.card α)

theorem staircaseStep_fair [Nonempty α] {s : List α} (hs : GoFirstFair s) :
    GoFirstFair (staircaseStep s) := by
  have hn (a : α) : Fintype.card α * winCount a s = outcomeCount s := by
    rw [← sum_winCount]
    have hc : ∀ b : α, winCount b s = winCount a s := fun b => hs.2 b a
    simp [hc]
  have hnone : winCount none (staircaseStep s) = outcomeCount s := by
    rw [staircaseStep, winCount, staircaseTail_new_wins, if_pos rfl, zero_add,
      prod_erase_eq_ite, Fintype.prod_option]
    simp [(staircaseTail_counts s (Fintype.card α)).2, outcomeCount]
  have hsome (a : α) : winCount (some a) (staircaseStep s) = outcomeCount s := by
    simp only [staircaseStep, winCount, reduceCtorEq, if_false, add_zero,
      staircaseTail_old_wins, hn]
  refine ⟨?_, ?_⟩
  · intro a
    cases a with
    | none => simp [staircaseStep]
    | some a => simp [staircaseStep, staircaseTail, hs.1 a]
  · intro a b
    cases a <;> cases b <;> simp [hnone, hsome]

/-- The upper bound in Theorem 5.1, constructed by the staircase recurrence. -/
theorem staircase_construction (n : ℕ) (hn : 0 < n) :
    ∃ s : List (Fin n), GoFirstFair s ∧ 2 * s.length = n * (n + 1) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hn0 : n = 0
    · subst n
      refine ⟨[0], ?_, by decide⟩
      refine ⟨?_, ?_⟩
      · intro a
        have : a = 0 := Fin.ext (by omega)
        simp [this]
      · intro a b
        have : a = b := Fin.ext (by omega)
        rw [this]
    · obtain ⟨s, hs, hlen⟩ := ih (by omega)
      letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
      refine ⟨(staircaseStep s).map (finSuccEquiv n).symm,
        goFirstFair_relabel _ (staircaseStep_fair hs), ?_⟩
      simp only [List.length_map, staircaseStep, List.length_cons, staircaseTail,
        List.length_append, List.length_replicate, Fintype.card_fin]
      nlinarith

end FairDice
