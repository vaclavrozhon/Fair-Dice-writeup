import FairDice.Blowup
import FairDice.Concatenation
import FairDice.Probability

namespace FairDice

variable {α : Type*} [DecidableEq α]

theorem count_reverse (p s : List α) : count p s.reverse = count p.reverse s := by
  rw [count_eq_sublists, count_eq_sublists, List.sublists'_reverse]
  have h := List.count_map_of_injective s.sublists List.reverse List.reverse_injective p.reverse
  have h' : (s.sublists.map List.reverse).count p = s.sublists.count p.reverse := by simpa using h
  rw [h']
  exact (List.sublists_perm_sublists' s).count_eq p.reverse

theorem count_append_singleton_of_not_mem (p s : List α) (a : α) (ha : a ∉ p) :
    count p (s ++ [a]) = count p s := by
  have hr : a ∉ p.reverse := by simpa using ha
  have hh := count_cons_of_not_mem p.reverse s.reverse a hr
  have h₁ := count_reverse p (a :: s.reverse)
  have h₂ := count_reverse p s.reverse
  simpa only [List.reverse_cons, List.reverse_reverse] using h₁.trans (hh.trans h₂.symm)

theorem count_cons_zero_of_not_mem (a : α) (p s : List α) (ha : a ∉ s) :
    count (a :: p) s = 0 := by
  by_contra h
  have hs := (count_pos_iff _ _).mp (Nat.pos_of_ne_zero h)
  exact ha (hs.subset (by simp))

/-- A nodup prescribed order has at most two position occurrences in a
palindrome formed from a permutation. This is the combinatorial ingredient
of `eq:palindrome-delta-bound`. -/
theorem count_palindrome_le_two (s p : List α) (hs : s.Nodup) (hp : p.Nodup) :
    count p (s ++ s.reverse) ≤ 2 := by
  induction s generalizing p with
  | nil => cases p <;> simp
  | cons a s ih =>
    have has : a ∉ s := (List.nodup_cons.mp hs).1
    have hs' := (List.nodup_cons.mp hs).2
    let t := s ++ s.reverse
    have hat : a ∉ t := by simp [t, has]
    have ht : t.reverse = t := by simp [t]
    have hhead (q : List α) (hq : (a :: q).Nodup) :
        count (a :: q) (a :: (t ++ [a])) ≤ 2 := by
      have haq : a ∉ q := (List.nodup_cons.mp hq).1
      rw [count_cons_cons, if_pos rfl, count_append_singleton_of_not_mem q t a haq]
      cases q with
      | nil => simp [count_singleton, List.count_append, List.count_eq_zero.mpr hat]
      | cons b q =>
        have hab : b ≠ a := by intro h; subst b; exact haq (by simp)
        have hrev : (b :: q).reverse ≠ [] := by simp
        obtain ⟨c, r, hcr⟩ := List.exists_cons_of_ne_nil hrev
        have hca : c ≠ a := by
          intro h
          subst c
          exact haq (List.mem_reverse.mp (by rw [hcr]; simp))
        have hz : count (a :: b :: q) (t ++ [a]) = 0 := by
          rw [← List.reverse_reverse (t ++ [a]), count_reverse]
          simp only [List.reverse_append, List.reverse_cons,
            ht, hcr, List.cons_append, List.reverse_nil, List.nil_append]
          rw [count_cons_cons, if_neg hca]
          have hh := count_cons_zero_of_not_mem a (b :: q) t hat
          have hh' := count_reverse (a :: b :: q) t
          rw [ht] at hh'
          simpa [List.reverse_cons, hcr] using hh'.symm.trans hh
        rw [hz, zero_add]
        exact ih (b :: q) hs' (List.nodup_cons.mp hq).2
    cases p with
    | nil => simp
    | cons b p =>
      have he : (a :: s) ++ (a :: s).reverse = a :: (t ++ [a]) := by simp [t, List.append_assoc]
      rw [he]
      by_cases hba : b = a
      · subst b; exact hhead p hp
      · rw [count_cons_cons, if_neg hba, add_zero]
        have hr : (b :: p).reverse ≠ [] := by simp
        obtain ⟨c, q, hcq⟩ := List.exists_cons_of_ne_nil hr
        by_cases hca : c = a
        · have hh := count_reverse (b :: p) (a :: (t ++ [a]))
          have hsym : (a :: (t ++ [a])).reverse = a :: (t ++ [a]) := by simp [ht]
          rw [hsym, hcq, hca] at hh
          rw [count_cons_cons, if_neg hba, add_zero] at hh
          rw [hh]
          exact hhead q (by simpa [hcq, hca] using List.nodup_reverse.mpr hp)
        · have hback : (c :: q).reverse = b :: p := by rw [← hcq, List.reverse_reverse]
          have hh := count_reverse (c :: q) (t ++ [a])
          simp only [List.reverse_append, List.reverse_singleton, ht,
            List.singleton_append, hback] at hh
          rw [count_cons_cons, if_neg hca, add_zero] at hh
          have hrt := count_reverse (b :: p) t
          rw [ht, hcq] at hrt
          rw [← hh, ← hrt]
          exact ih _ hs' hp

/-- Each symbol of the permutation has exactly two faces in its palindrome. -/
theorem palindrome_multiplicity (s : List α) (hs : s.Nodup) (a : α) (ha : a ∈ s) :
    (s ++ s.reverse).count a = 2 := by
  simp [List.count_append, List.count_eq_one_of_mem hs ha]

/-- Reversal of a palindrome interchanges the two prescribed pair orders. -/
theorem palindrome_pair_count (s : List α) (hs : s.Nodup) (a b : α)
    (ha : a ∈ s) (hb : b ∈ s) (hab : a ≠ b) :
    count [a, b] (s ++ s.reverse) = 2 := by
  have heq : count [a, b] (s ++ s.reverse) = count [b, a] (s ++ s.reverse) := by
    have hh := count_reverse [a, b] (s ++ s.reverse)
    simpa using hh
  have hsum := sum_permutation_counts [a, b] (s ++ s.reverse) (by simp [hab])
  simp only [List.permutations', List.permutations'Aux, List.flatMap_cons,
    List.flatMap_nil, List.append_nil, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, List.prod_cons, List.prod_nil, mul_one, add_zero] at hsum
  rw [palindrome_multiplicity s hs a ha, palindrome_multiplicity s hs b hb] at hsum
  omega

noncomputable def palindromeDelta (s p : List α) : ℝ :=
  (p.length.factorial : ℝ) * (count p (s ++ s.reverse) : ℝ) / 2^p.length - 1

/-- Errors vanish identically for occupancies zero, one and two. -/
theorem palindromeDelta_short (s p : List α) (hs : s.Nodup) (hp : p.Nodup)
    (hps : ∀ a ∈ p, a ∈ s) (hlen : p.length ≤ 2) : palindromeDelta s p = 0 := by
  cases p with
  | nil => simp [palindromeDelta]
  | cons a p =>
    cases p with
    | nil =>
      simp [palindromeDelta, palindrome_multiplicity s hs a (hps a (by simp))]
    | cons b p =>
      have hp0 : p = [] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at hlen; omega)
      subst p
      simp only [List.nodup_cons, List.mem_cons] at hp
      rw [palindromeDelta, palindrome_pair_count s hs a b (hps a (by simp))
        (hps b (by simp)) (by simpa using hp.1)]
      norm_num

/-- The factorial dominates the factor used to bound centered errors. -/
theorem factorial_two_le (k : ℕ) (hk : 3 ≤ k) : 2^k ≤ 2 * k.factorial := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hk
  induction j with
  | zero => norm_num
  | succ j ih =>
    have ih' := ih (by omega)
    rw [show 3 + (j + 1) = (3 + j) + 1 by omega, pow_succ, Nat.factorial_succ]
    nlinarith

/-- Equation `eq:palindrome-delta-bound`, with natural powers avoiding
negative-exponent conventions: the right side is `k! * 2 / 2^k`. -/
theorem palindromeDelta_bound (s p : List α) (hs : s.Nodup) (hp : p.Nodup)
    (hk : 3 ≤ p.length) :
    |palindromeDelta s p| ≤ (p.length.factorial : ℝ) * 2 / 2^p.length := by
  have hc : (count p (s ++ s.reverse) : ℝ) ≤ 2 := by
    exact_mod_cast count_palindrome_le_two s p hs hp
  have hfact : (2 : ℝ)^p.length ≤ 2 * p.length.factorial := by
    exact_mod_cast factorial_two_le p.length hk
  have hpow : (0 : ℝ) < 2^p.length := by positivity
  rw [abs_le, palindromeDelta]
  constructor
  · have hb : (1 : ℝ) ≤ (p.length.factorial : ℝ) * 2 / 2^p.length := by
      apply (le_div_iff₀ hpow).mpr
      nlinarith
    have he : (0 : ℝ) ≤ (p.length.factorial : ℝ) * count p (s ++ s.reverse) / 2^p.length := by
      positivity
    linarith
  · have hh : (p.length.factorial : ℝ) * count p (s ++ s.reverse) / 2^p.length ≤
        (p.length.factorial : ℝ) * 2 / 2^p.length := by
      apply div_le_div_of_nonneg_right _ (le_of_lt hpow)
      exact mul_le_mul_of_nonneg_left hc (by positivity)
    linarith

/-- The concrete word used in the new random construction. -/
def palindromeWord {n m : ℕ} (ρ : Fin m → Equiv.Perm (Fin n)) : List (Fin n) :=
  ((List.finRange m).map (fun i =>
    let s := (List.finRange n).map (ρ i)
    s ++ s.reverse)).flatten

theorem palindromeWord_multiplicity {n m : ℕ} (ρ : Fin m → Equiv.Perm (Fin n))
    (a : Fin n) : (palindromeWord ρ).count a = 2 * m := by
  have hh (i : Fin m) :
      (((List.finRange n).map (ρ i)) ++ ((List.finRange n).map (ρ i)).reverse).count a = 2 := by
    apply palindrome_multiplicity
    · exact (List.nodup_finRange n).map (ρ i).injective
    · exact List.mem_map.mpr ⟨(ρ i).symm a, List.mem_finRange _, (ρ i).apply_symm_apply a⟩
  simp [palindromeWord, List.count_flatten, List.map_map, Function.comp_def,
    hh, List.map_const', Nat.mul_comm]

end FairDice
