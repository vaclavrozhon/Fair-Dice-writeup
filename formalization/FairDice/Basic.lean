import Mathlib

namespace FairDice

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

/-- The number of occurrences of `p` as a subsequence of `s`. Positions, rather
than distinct resulting sublists, are counted. The empty pattern occurs once. -/
def count : List α → List α → ℕ
  | [], _ => 1
  | _ :: _, [] => 0
  | a :: p, b :: s => count (a :: p) s + if a = b then count p s else 0

@[simp] theorem count_nil (s : List α) : count [] s = 1 := by cases s <;> rfl

@[simp] theorem count_cons_nil (a : α) (p : List α) : count (a :: p) [] = 0 := rfl

@[simp] theorem count_cons_cons (a b : α) (p s : List α) :
    count (a :: p) (b :: s) = count (a :: p) s + if a = b then count p s else 0 := rfl

theorem count_empty_word (p : List α) : count p [] = if p = [] then 1 else 0 := by
  cases p <;> simp

/-- The recursive counter agrees with the list of all position sublists. -/
theorem count_eq_sublists (p s : List α) : count p s = s.sublists'.count p := by
  induction s generalizing p with
  | nil => cases p <;> simp [List.sublists']
  | cons b s ih =>
    cases p with
    | nil =>
      have hz : (s.sublists'.map (List.cons b)).count [] = 0 := by
        simp [List.count_eq_zero, List.mem_map]
      simpa [List.sublists'_cons, hz] using ih []
    | cons a p =>
      rw [count_cons_cons, List.sublists'_cons, List.count_append, ← ih]
      by_cases h : a = b
      · subst a
        rw [if_pos rfl, List.count_map_of_injective _ _ List.cons_injective, ← ih]
      · simp [h, Ne.symm h, List.count_eq_zero, List.mem_map]

@[simp] theorem count_singleton (a : α) (s : List α) : count [a] s = s.count a := by
  induction s with
  | nil => rfl
  | cons b s ih =>
    by_cases h : a = b
    · subst b; simp [ih]
    · simp [ih, h, Ne.symm h]

theorem count_pos_iff (p s : List α) : 0 < count p s ↔ p.Sublist s := by
  rw [count_eq_sublists, List.count_pos_iff, List.mem_sublists']

theorem count_eq_zero_of_length (p s : List α) (h : s.length < p.length) :
    count p s = 0 := by
  by_contra hn
  have := (count_pos_iff p s).mp (Nat.pos_of_ne_zero hn)
  have := this.length_le
  omega

/-- Applying an injective relabelling to the word and pattern preserves counts. -/
theorem count_map (f : α → β) (hf : Function.Injective f) (p s : List α) :
    count (p.map f) (s.map f) = count p s := by
  induction s generalizing p with
  | nil => cases p <;> simp
  | cons b s ih =>
    cases p with
    | nil => simp
    | cons a p =>
      have hi := ih (a :: p)
      simp only [List.map_cons] at hi ⊢
      simp only [count_cons_cons, hi, ih, hf.eq_iff]

theorem count_relabel (e : α ≃ β) (p : List β) (s : List α) :
    count p (s.map e) = count (p.map e.symm) s := by
  simpa using count_map e e.injective (p.map e.symm) s

/-- Deleting symbols outside a pattern leaves its count unchanged. -/
theorem count_filter (keep : α → Bool) (p s : List α)
    (hp : ∀ a ∈ p, keep a = true) : count p (s.filter keep) = count p s := by
  induction s generalizing p with
  | nil => simp
  | cons b s ih =>
    cases p with
    | nil => simp
    | cons a p =>
      have ha := hp a (by simp)
      have ht : ∀ c ∈ p, keep c = true := fun c hc => hp c (by simp [hc])
      by_cases hb : keep b = true
      · simp [hb, ih _ hp, ih _ ht]
      · have hab : a ≠ b := by intro h; subst b; exact hb ha
        simp [hb, hab, ih _ hp]

/-- Fairness at a fixed pattern length, as in Section 2. -/
def FairAt (k : ℕ) (s : List α) : Prop :=
  ∀ p q : List α, p.Nodup → q.Nodup → p.length = k → q.length = k →
    count p s = count q s

def FairUpTo (k : ℕ) (s : List α) : Prop := ∀ j ≤ k, FairAt j s

/-- Full fairness includes the requirement that every symbol occurs. -/
def PermutationFair [Fintype α] (s : List α) : Prop :=
  (∀ a : α, a ∈ s) ∧ FairAt (Fintype.card α) s

theorem fairAt_zero (s : List α) : FairAt 0 s := by
  intro p q _ _ hp hq
  simp only [List.length_eq_zero_iff] at hp hq
  simp [hp, hq]

theorem fairUpTo_mono {s : List α} {j k : ℕ} (h : FairUpTo k s) (hjk : j ≤ k) :
    FairUpTo j s := fun i hi => h i (hi.trans hjk)

theorem fairAt_relabel (e : α ≃ β) {s : List α} {k : ℕ} (h : FairAt k s) :
    FairAt k (s.map e) := by
  intro p q hp hq hpl hql
  rw [count_relabel, count_relabel]
  apply h
  · exact hp.map e.symm.injective
  · exact hq.map e.symm.injective
  · simpa using hpl
  · simpa using hql

theorem fairUpTo_relabel (e : α ≃ β) {s : List α} {k : ℕ} (h : FairUpTo k s) :
    FairUpTo k (s.map e) := fun j hj => fairAt_relabel e (h j hj)

theorem permutationFair_relabel [Fintype α] [Fintype β] (e : α ≃ β)
    {s : List α} (h : PermutationFair s) : PermutationFair (s.map e) := by
  refine ⟨?_, ?_⟩
  · intro b
    exact List.mem_map.mpr ⟨e.symm b, h.1 _, e.apply_symm_apply b⟩
  · have hcard := Fintype.card_congr e
    rw [← hcard]
    exact fairAt_relabel e h.2

end FairDice
