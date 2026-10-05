import FairDice.Blowup

namespace FairDice

variable {α : Type*} [DecidableEq α]

private theorem letter_count_cons (a b : α) (s : List α) :
    (b :: s).count a = s.count a + if a = b then 1 else 0 := by
  simpa only [count_singleton, count_nil] using count_cons_cons a b [] s

def insertionSum (a : α) (p s : List α) : ℕ :=
  ∑ i ∈ Finset.range (p.length + 1), count (p.insertIdx i a) s

theorem insertionSum_cons_word (a b c : α) (p s : List α) :
    insertionSum a (c :: p) (b :: s) = insertionSum a (c :: p) s +
      (if a = b then count (c :: p) s else 0) +
      (if c = b then insertionSum a p s else 0) := by
  simp only [insertionSum, List.length_cons,
    Finset.sum_range_succ' (n := p.length + 1), List.insertIdx_zero,
    List.insertIdx_succ_cons, count_cons_cons, Finset.sum_add_distrib]
  by_cases hab : a = b <;> by_cases hcb : c = b <;>
    simp [hab, hcb, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Count a partial occurrence together with one chosen occurrence of an
omitted letter, either independently or by its position in the merged order. -/
theorem count_mul_letter (a : α) (p s : List α) (ha : a ∉ p) :
    count p s * s.count a = insertionSum a p s := by
  induction s generalizing p with
  | nil =>
    cases p with
    | nil => simp [insertionSum]
    | cons c p =>
      simp [insertionSum, Finset.sum_range_succ', List.insertIdx_succ_cons]
  | cons b s ih =>
    cases p with
    | nil => simp [insertionSum, letter_count_cons]
    | cons c p =>
      have hac : a ≠ c := by intro h; subst c; exact ha (by simp)
      have hat : a ∉ p := fun h => ha (by simp [h])
      rw [insertionSum_cons_word, ← ih (c :: p) ha, ← ih p hat]
      simp only [count_cons_cons]
      by_cases hab : a = b
      · subst b
        have hca : c ≠ a := Ne.symm hac
        simp [hca, Nat.mul_add]
      · by_cases hcb : c = b
        · subst b; simp [letter_count_cons, hab, Nat.add_mul]
        · simp [hab, hcb, Ne.symm hab]

/-- Fairness of all orders of a specified subset of the alphabet. -/
def OrderFair (s letters : List α) : Prop :=
  ∀ p q : List α, p.Perm letters → q.Perm letters → count p s = count q s

theorem orderFair_perm {s p q : List α} (h : OrderFair s p) (hpq : p.Perm q) :
    OrderFair s q := fun a b ha hb => h a b (ha.trans hpq.symm) (hb.trans hpq.symm)

theorem insertionSum_of_orderFair {s : List α} (a : α) (p : List α)
    (h : OrderFair s (a :: p)) :
    insertionSum a p s = (p.length + 1) * count (a :: p) s := by
  unfold insertionSum
  calc
    _ = ∑ _i ∈ Finset.range (p.length + 1), count (a :: p) s := by
      apply Finset.sum_congr rfl
      intro i hi
      exact h _ _ (List.perm_insertIdx a p (by simpa using Finset.mem_range.mp hi))
        (List.Perm.refl _)
    _ = _ := by simp

/-- Removing a die preserves the uniformity of the orders of the remaining
dice. Positivity is explicit because cancellation by an absent letter would
otherwise be invalid. -/
theorem orderFair_tail {s : List α} {a : α} {p : List α}
    (hs : 0 < s.count a) (hp : (a :: p).Nodup) (h : OrderFair s (a :: p)) :
    OrderFair s p := by
  intro q r hq hr
  have haq : a ∉ q := by
    intro ha; exact (List.nodup_cons.mp hp).1 (hq.mem_iff.mp ha)
  have har : a ∉ r := by
    intro ha; exact (List.nodup_cons.mp hp).1 (hr.mem_iff.mp ha)
  apply Nat.eq_of_mul_eq_mul_right hs
  rw [count_mul_letter a q s haq, count_mul_letter a r s har]
  rw [insertionSum_of_orderFair a q (orderFair_perm h (hq.cons a).symm),
    insertionSum_of_orderFair a r (orderFair_perm h (hr.cons a).symm),
    hq.length_eq, hr.length_eq, h _ _ (hq.cons a) (hr.cons a)]

/-- Once all orders are equally frequent, their common count times the
factorial equals the number of independent face selections. -/
theorem orderFair_total {s p : List α} (hp : p.Nodup)
    (hpos : ∀ a ∈ p, 0 < s.count a) (h : OrderFair s p) :
    p.length.factorial * count p s = (p.map (fun a => s.count a)).prod := by
  induction p with
  | nil => simp
  | cons a p ih =>
    have hp' := List.nodup_cons.mp hp
    have ht := orderFair_tail (hpos a (by simp)) hp h
    have hi := ih hp'.2 (fun b hb => hpos b (by simp [hb])) ht
    have hm := count_mul_letter a p s hp'.1
    rw [insertionSum_of_orderFair a p h] at hm
    simp only [List.length_cons, Nat.factorial_succ, List.map_cons, List.prod_cons]
    rw [← hi]
    nlinarith

theorem orderFair_suffix {s p q : List α} (hp : (p ++ q).Nodup)
    (hpos : ∀ a ∈ p, 0 < s.count a) (h : OrderFair s (p ++ q)) : OrderFair s q := by
  induction p with
  | nil => exact h
  | cons a p ih =>
    exact ih (List.nodup_cons.mp hp).2 (fun b hb => hpos b (by simp [hb]))
      (orderFair_tail (hpos a (by simp)) hp h)

theorem orderFair_subperm {s p q : List α} (hp : p.Nodup)
    (hpos : ∀ a ∈ p, 0 < s.count a) (h : OrderFair s p) (hqp : q.Subperm p) :
    OrderFair s q := by
  obtain ⟨l, hl, hql⟩ := List.subperm_iff.mp hqp
  obtain ⟨t, ht⟩ := hql.exists_perm_append
  have htp : (t ++ q).Perm p := List.perm_append_comm.trans (ht.symm.trans hl)
  apply orderFair_suffix (htp.nodup_iff.mpr hp) _ (orderFair_perm h htp.symm)
  intro a ha
  exact hpos a (htp.mem_iff.mp (List.mem_append.mpr (Or.inl ha)))

variable [Fintype α]

theorem permutationFair_orderFair {s : List α} (hs : PermutationFair s)
    (p : List α) (hp : p.Nodup) (hlen : p.length = Fintype.card α) : OrderFair s p := by
  intro q r hq hr
  apply hs.2 q r (hq.nodup_iff.mpr hp) (hr.nodup_iff.mpr hp)
    (hq.length_eq.trans hlen) (hr.length_eq.trans hlen)

/-- Restricting a fully fair word to any specified collection of letters
preserves uniformity of their relative orders. -/
theorem permutationFair_partialOrder {s : List α} (hs : PermutationFair s)
    (p : List α) (hp : p.Nodup) : OrderFair s p := by
  classical
  let all := (Finset.univ : Finset α).toList
  have hn : all.Nodup := Finset.nodup_toList _
  have hm : ∀ a : α, a ∈ all := by simp [all]
  apply orderFair_subperm hn
    (fun a _ => List.count_pos_iff.mpr (hs.1 a))
    (permutationFair_orderFair hs all hn (by simp [all]))
    (hp.subperm (fun a _ => hm a))

/-- Lemma 2.4 in its division-free normalized form. Unlike full fairness,
the product on the right is allowed to depend on the letters in `p`. -/
theorem partial_count_product {s : List α} (hs : PermutationFair s)
    (p : List α) (hp : p.Nodup) :
    p.length.factorial * count p s = (p.map (fun a => s.count a)).prod :=
  orderFair_total hp (fun a _ => List.count_pos_iff.mpr (hs.1 a))
    (permutationFair_partialOrder hs p hp)

/-- Lemma 2.6: equal multiplicities turn full fairness into fairness at every
shorter pattern length. -/
theorem equal_full_to_partial {s : List α} (hs : PermutationFair s)
    (c : ℕ) (hc : ∀ a, s.count a = c) : FairUpTo (Fintype.card α) s := by
  intro k _ p q hp hq hpl hql
  have hp' := partial_count_product hs p hp
  have hq' := partial_count_product hs q hq
  simp only [hc, List.map_const', List.prod_replicate, hpl, hql] at hp' hq'
  exact Nat.eq_of_mul_eq_mul_left (Nat.factorial_pos k) (hp'.trans hq'.symm)

end FairDice
