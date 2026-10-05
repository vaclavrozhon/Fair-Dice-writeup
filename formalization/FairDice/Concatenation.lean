import FairDice.Basic

namespace FairDice

variable {α : Type*} [DecidableEq α]

/-- Split an occurrence at the boundary of two concatenated words. -/
theorem count_append (p s t : List α) :
    count p (s ++ t) = ∑ j ∈ Finset.range (p.length + 1),
      count (p.take j) s * count (p.drop j) t := by
  induction s generalizing p with
  | nil =>
    cases p with
    | nil => simp
    | cons a p =>
      simp [Finset.sum_range_succ', List.take_succ_cons]
  | cons b s ih =>
    cases p with
    | nil => simp
    | cons a p =>
      simp only [List.cons_append, count_cons_cons]
      rw [ih (a :: p), ih p]
      simp only [List.length_cons]
      simp only [Finset.sum_range_succ' (n := p.length + 1)]
      simp only [List.take_zero, List.drop_zero, count_nil, one_mul,
        List.take_succ_cons, List.drop_succ_cons, count_cons_cons]
      by_cases h : a = b
      · simp only [h, if_true, add_mul, Finset.sum_add_distrib]
        omega
      · simp [h]

/-- The concatenation closure claimed after Corollary 2.5. -/
theorem fairUpTo_append {k : ℕ} {s t : List α}
    (hs : FairUpTo k s) (ht : FairUpTo k t) : FairUpTo k (s ++ t) := by
  intro j hj p q hp hq hpl hql
  rw [count_append, count_append, hpl, hql]
  apply Finset.sum_congr rfl
  intro i hi
  have hij : i ≤ j := by simpa using Finset.mem_range.mp hi
  congr 1
  · apply hs i (hij.trans hj) _ _ hp.take hq.take
    · simp [List.length_take, hpl, Nat.min_eq_left hij]
    · simp [List.length_take, hql, Nat.min_eq_left hij]
  · apply ht (j - i) (Nat.sub_le j i |>.trans hj) _ _ hp.drop hq.drop
    · simp [hpl]
    · simp [hql]

/-- Any finite concatenation of words fair through length `k` is fair through
length `k`. -/
theorem fairUpTo_flatten {k : ℕ} {ss : List (List α)}
    (h : ∀ s ∈ ss, FairUpTo k s) : FairUpTo k ss.flatten := by
  induction ss with
  | nil =>
    intro j _ p q _ _ hp hq
    cases p <;> cases q <;> simp_all <;> omega
  | cons s ss ih =>
    exact fairUpTo_append (h s (by simp)) (ih (fun t ht => h t (by simp [ht])))

/-- A positive power of a word with fairness at every shorter length preserves
that property. This also covers equal-composition fair words once the
full-to-partial implication has been established. -/
theorem fairUpTo_repeat {k m : ℕ} {s : List α} (h : FairUpTo k s) :
    FairUpTo k (List.replicate m s).flatten := by
  apply fairUpTo_flatten
  intro t ht
  obtain ⟨_, rfl⟩ := List.mem_replicate.mp ht
  exact h

end FairDice
