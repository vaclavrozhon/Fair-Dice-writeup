import FairDice.PalindromeBlocks
import FairDice.Symmetrization

namespace FairDice

variable {α : Type*} [DecidableEq α] [Fintype α]

private theorem sum_list_sum (qs : List (List α)) (f : List α → Equiv.Perm α → ℕ) :
    (qs.map (fun q => ∑ e, f q e)).sum = ∑ e, (qs.map (fun q => f q e)).sum := by
  induction qs with
  | nil => simp
  | cons q qs ih => simp [ih, Finset.sum_add_distrib]

/-- Relabelling a two-occurrence word gives the exact factorial mean of
every injective pattern. No assumption of fairness is needed. -/
theorem relabel_two_count_mean (s p : List α) (hp : p.Nodup)
    (hs : ∀ a : α, s.count a = 2) :
    p.length.factorial * (∑ e : Equiv.Perm α, count p (s.map e)) =
      (Fintype.card α).factorial * 2^p.length := by
  classical
  have hconstant (q : List α) (hq : q ∈ p.permutations') :
      (∑ e : Equiv.Perm α, count q (s.map e)) = ∑ e : Equiv.Perm α, count p (s.map e) := by
    have hperm := List.mem_permutations'.mp hq
    exact sum_relabel_counts s q p (hperm.nodup_iff.mpr hp) hp hperm.length_eq
  have hleft : (p.permutations'.map (fun q => ∑ e : Equiv.Perm α, count q (s.map e))).sum =
      p.length.factorial * (∑ e : Equiv.Perm α, count p (s.map e)) := by
    rw [List.map_congr_left hconstant]
    have hlen : p.permutations'.length = p.length.factorial :=
      (List.permutations_perm_permutations' p).length_eq.symm.trans (List.length_permutations p)
    simp [List.map_const', hlen]
  have hterm (e : Equiv.Perm α) :
      (p.permutations'.map (fun q => count q (s.map e))).sum = 2^p.length := by
    rw [sum_permutation_counts p _ hp]
    have hh (a : α) : (s.map e).count a = 2 := by
      rw [← e.apply_symm_apply a, List.count_map_of_injective _ _ e.injective]
      exact hs _
    simp [hh, List.map_const']
  rw [← hleft, sum_list_sum]
  simp [hterm, Fintype.card_perm]

/-- Uniform relabelling centers each palindrome error exactly. -/
theorem palindromeDelta_centered (s p : List α) (hs : s.Nodup)
    (hfull : ∀ a : α, a ∈ s) (hp : p.Nodup) :
    (∑ e : Equiv.Perm α, palindromeDelta (s.map e) p) = 0 := by
  classical
  have hmean := relabel_two_count_mean (s ++ s.reverse) p hp
    (fun a => palindrome_multiplicity s hs a (hfull a))
  have hmeanR : (p.length.factorial : ℝ) *
      (∑ e : Equiv.Perm α, (count p ((s ++ s.reverse).map e) : ℝ)) =
        ((Fintype.card α).factorial : ℝ) * 2^p.length := by exact_mod_cast hmean
  have hword (e : Equiv.Perm α) :
      s.map e ++ (s.map e).reverse = (s ++ s.reverse).map e := by simp
  simp only [palindromeDelta, hword, Finset.sum_sub_distrib, ← Finset.sum_div,
    ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hmeanR]
  have hpow : (2 : ℝ)^p.length ≠ 0 := by positivity
  field_simp
  simp [Fintype.card_perm]

end FairDice
