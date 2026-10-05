import FairDice.Basic

namespace FairDice

variable {α : Type*} [DecidableEq α]

theorem count_cons_of_not_mem (p : List α) (s : List α) (b : α) (hb : b ∉ p) :
    count p (b :: s) = count p s := by
  cases p with
  | nil => simp
  | cons a p =>
    have hab : a ≠ b := by intro h; subst a; exact hb (by simp)
    simp [hab]

theorem count_replicate_append_of_not_mem (p s : List α) (b : α) (r : ℕ)
    (hb : b ∉ p) : count p (List.replicate r b ++ s) = count p s := by
  induction r with
  | zero => simp
  | succ r ih => simpa [List.replicate_succ, count_cons_of_not_mem _ _ _ hb] using ih

theorem count_replicate_append (a b : α) (p s : List α) (r : ℕ)
    (hp : (a :: p).Nodup) :
    count (a :: p) (List.replicate r b ++ s) =
      count (a :: p) s + if a = b then r * count p s else 0 := by
  induction r with
  | zero => simp
  | succ r ih =>
    simp only [List.replicate_succ, List.cons_append, count_cons_cons, ih]
    by_cases h : a = b
    · subst b
      simp [count_replicate_append_of_not_mem p s a r (List.nodup_cons.mp hp).1,
        Nat.add_mul, Nat.add_assoc]
    · simp [h]

/-- Replace each occurrence of `a` by `w a` consecutive copies. -/
def blowup (w : α → ℕ) (s : List α) : List α :=
  s.flatMap fun a => List.replicate (w a) a

/-- Each occurrence of an injective pattern has exactly the product of the
specified multiplicities many lifts. This is Claim 2.2(ii), in a stronger
form allowing all letters to be blown up at once. -/
theorem count_blowup (w : α → ℕ) (p s : List α) (hp : p.Nodup) :
    count p (blowup w s) = (p.map w).prod * count p s := by
  induction s generalizing p with
  | nil => cases p <;> simp [blowup]
  | cons b s ih =>
    cases p with
    | nil => simp
    | cons a p =>
      change count (a :: p) (List.replicate (w b) b ++ blowup w s) = _
      rw [count_replicate_append _ _ _ _ _ hp, ih _ hp,
        ih _ (List.nodup_cons.mp hp).2]
      simp only [List.map_cons, List.prod_cons, count_cons_cons]
      by_cases h : a = b
      · subst b; simp; ring
      · simp [h]

theorem multiplicity_blowup (w : α → ℕ) (s : List α) (a : α) :
    (blowup w s).count a = w a * s.count a := by
  simpa using count_blowup w [a] s (by simp)

variable [Fintype α]

/-- An injective full-length pattern contains every letter. -/
theorem mem_full_pattern (p : List α) (hp : p.Nodup)
    (hlen : p.length = Fintype.card α) (a : α) : a ∈ p := by
  have hu : p.toFinset = Finset.univ :=
    Finset.eq_univ_of_card _ (by simpa [List.toFinset_card_of_nodup hp] using hlen)
  have : a ∈ p.toFinset := by rw [hu]; exact Finset.mem_univ _
  exact List.mem_toFinset.mp this

theorem full_patterns_perm (p q : List α) (hp : p.Nodup) (hq : q.Nodup)
    (hpl : p.length = Fintype.card α) (hql : q.length = Fintype.card α) :
    p.Perm q := by
  apply List.perm_iff_count.mpr
  intro a
  rw [List.count_eq_one_of_mem hp (mem_full_pattern p hp hpl a),
    List.count_eq_one_of_mem hq (mem_full_pattern q hq hql a)]

theorem permutationFair_blowup {s : List α} (hs : PermutationFair s)
    (w : α → ℕ) (hw : ∀ a, 0 < w a) : PermutationFair (blowup w s) := by
  constructor
  · intro a
    apply List.count_pos_iff.mp
    rw [multiplicity_blowup]
    exact Nat.mul_pos (hw a) (List.count_pos_iff.mpr (hs.1 a))
  · intro p q hp hq hpl hql
    rw [count_blowup _ _ _ hp, count_blowup _ _ _ hq,
      hs.2 p q hp hq hpl hql,
      ((full_patterns_perm p q hp hq hpl hql).map w).prod_eq]

end FairDice
