import FairDice.PartialPatterns
import FairDice.Concatenation

namespace FairDice

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- Concatenating two fully fair words preserves fairness whenever their
letter multiplicities are proportional. Unequal-sided dice are allowed. -/
theorem permutationFair_append_proportional {s t : List α}
    (hs : PermutationFair s) (ht : PermutationFair t) (m : ℕ)
    (hm : ∀ a, s.count a = m * t.count a) : PermutationFair (s ++ t) := by
  refine ⟨fun a => List.mem_append.mpr (Or.inl (hs.1 a)), ?_⟩
  intro p q hp hq hpl hql
  rw [count_append, count_append, hpl, hql]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j ≤ Fintype.card α := by simpa using Finset.mem_range.mp hj
  have count_term (r : List α) (hr : r.Nodup) (hrl : r.length = Fintype.card α) :
      (j.factorial * (Fintype.card α - j).factorial) *
        (count (r.take j) s * count (r.drop j) t) =
      m ^ j * (r.map (fun a => t.count a)).prod := by
    have htake := partial_count_product hs (r.take j) hr.take
    have hdrop := partial_count_product ht (r.drop j) hr.drop
    simp only [List.length_take, List.length_drop, hrl, Nat.min_eq_left hjn] at htake hdrop
    simp only [hm, List.prod_map_mul, List.map_const', List.prod_replicate,
      List.length_take, hrl, Nat.min_eq_left hjn] at htake
    have hsplit : ((r.take j).map (fun a => t.count a)).prod *
        ((r.drop j).map (fun a => t.count a)).prod =
        (r.map (fun a => t.count a)).prod := by
      rw [← List.prod_append, ← List.map_append, List.take_append_drop]
    calc
      _ = (j.factorial * count (r.take j) s) *
        ((Fintype.card α - j).factorial * count (r.drop j) t) := by ring
      _ = _ := by rw [htake, hdrop, Nat.mul_assoc, hsplit]
  apply Nat.eq_of_mul_eq_mul_left
    (Nat.mul_pos (Nat.factorial_pos j) (Nat.factorial_pos _))
  rw [count_term p hp hpl, count_term q hq hql,
    ((full_patterns_perm p q hp hq hpl hql).map (fun a => t.count a)).prod_eq]

/-- Corollary 2.5 for every positive exponent, including non-powers of two
and words with unequal letter multiplicities. -/
theorem permutationFair_repeat {s : List α} (hs : PermutationFair s) (m : ℕ) :
    PermutationFair (List.replicate (m + 1) s).flatten := by
  induction m with
  | zero => simpa using hs
  | succ m ih =>
    have hcount : ∀ a, ((List.replicate (m + 1) s).flatten).count a =
        (m + 1) * s.count a := by
      intro a
      simp [List.count_flatten, List.map_replicate, List.sum_replicate]
    have h := permutationFair_append_proportional ih hs (m + 1) hcount
    have hword : (List.replicate (m + 1 + 1) s).flatten =
        (List.replicate (m + 1) s).flatten ++ s := by
      rw [List.replicate_add, List.flatten_append]
      simp
    rw [hword]
    exact h

end FairDice
