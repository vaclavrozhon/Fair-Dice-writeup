import FairDice.PartialPatterns

namespace FairDice

variable {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
theorem permutationsAux_eq_insertions (a : α) (p : List α) :
    List.permutations'Aux a p = (List.range (p.length + 1)).map (fun i => p.insertIdx i a) := by
  induction p with
  | nil => simp [List.permutations'Aux]
  | cons b p ih =>
    rw [List.permutations'Aux, ih, List.length_cons,
      List.range_succ_eq_map (n := p.length + 1)]
    simp [List.map_map, Function.comp_def]

theorem insertionSum_eq_list_sum (a : α) (p s : List α) :
    insertionSum a p s = ((List.permutations'Aux a p).map (fun q => count q s)).sum := by
  rw [permutationsAux_eq_insertions, List.map_map]
  simpa only [List.toFinset_range, insertionSum, Function.comp_def] using
    List.sum_toFinset (fun i => count (p.insertIdx i a) s) List.nodup_range

/-- All orders of one face chosen from each listed die partition the sample
space, whose size is the product of the numbers of faces. Fairness is not
assumed. This supplies the normalizing constant for the order probabilities. -/
theorem sum_permutation_counts (p s : List α) (hp : p.Nodup) :
    (p.permutations'.map (fun q => count q s)).sum =
      (p.map (fun a => s.count a)).prod := by
  induction p with
  | nil => simp
  | cons a p ih =>
    have hp' := List.nodup_cons.mp hp
    have hterm (q : List α) (hq : q ∈ p.permutations') :
        ((List.permutations'Aux a q).map (fun r => count r s)).sum = count q s * s.count a := by
      rw [← insertionSum_eq_list_sum, ← count_mul_letter]
      intro ha
      exact hp'.1 ((List.mem_permutations'.mp hq).mem_iff.mp ha)
    simp only [List.permutations', List.flatMap_def, List.map_flatten,
      List.sum_flatten, List.map_map, Function.comp_def]
    rw [List.map_congr_left hterm]
    simp only [List.sum_map_mul_right, ih hp'.2, List.map_cons, List.prod_cons]
    ring

/-- Probability of a prescribed relative order, with independent uniform face
choices and the positions in the word serving as the distinct face labels. -/
def patternProbability (s p : List α) : ℚ :=
  count p s / ((p.map (fun a => s.count a)).prod : ℚ)

theorem patternProbability_nonneg (s p : List α) : 0 ≤ patternProbability s p := by
  unfold patternProbability
  positivity

theorem permutation_probability_sum (s p : List α) (hp : p.Nodup)
    (hpos : ∀ a ∈ p, 0 < s.count a) :
    (p.permutations'.map (patternProbability s)).sum = 1 := by
  have hprod : 0 < (p.map (fun a => s.count a)).prod := by
    apply List.prod_pos
    intro c hc
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hc
    exact hpos a ha
  have hterm (q : List α) (hq : q ∈ p.permutations') :
      patternProbability s q = (count q s : ℚ) / (p.map (fun a => s.count a)).prod := by
    unfold patternProbability
    rw [((List.mem_permutations'.mp hq).map (fun a => s.count a)).prod_eq]
  rw [List.map_congr_left hterm]
  simp only [div_eq_mul_inv, List.sum_map_mul_right]
  have hcounts := sum_permutation_counts p s hp
  have hcast : (p.permutations'.map (fun q => (count q s : ℚ))).sum =
      ((p.map (fun a => s.count a)).prod : ℚ) := by
    simpa only [Nat.cast_list_sum, List.map_map, Function.comp_def] using
      congrArg (fun n : ℕ => (n : ℚ)) hcounts
  rw [hcast, mul_inv_cancel₀ (by exact_mod_cast Nat.ne_of_gt hprod)]

variable [Fintype α]

/-- Every partial order of a fully fair word has probability `1/k!`, even
when the individual dice have different numbers of faces. -/
theorem patternProbability_uniform {s : List α} (hs : PermutationFair s)
    (p : List α) (hp : p.Nodup) :
    patternProbability s p = 1 / (p.length.factorial : ℚ) := by
  have hprod : 0 < (p.map (fun a => s.count a)).prod := by
    apply List.prod_pos
    intro c hc
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hc
    exact List.count_pos_iff.mpr (hs.1 a)
  have hcount := partial_count_product hs p hp
  have hcast : (p.length.factorial : ℚ) * count p s =
      ((p.map (fun a => s.count a)).prod : ℚ) := by exact_mod_cast hcount
  unfold patternProbability
  apply (div_eq_div_iff (by exact_mod_cast Nat.ne_of_gt hprod)
    (by exact_mod_cast Nat.ne_of_gt (Nat.factorial_pos p.length))).mpr
  nlinarith

/-- The counting/probability equivalence of Lemma 2.1. -/
theorem permutationFair_iff_uniform (s : List α) (hpos : ∀ a : α, a ∈ s) :
    PermutationFair s ↔ ∀ p : List α, p.Nodup → p.length = Fintype.card α →
      patternProbability s p = 1 / ((Fintype.card α).factorial : ℚ) := by
  constructor
  · intro hs p hp hlen
    simpa [hlen] using patternProbability_uniform hs p hp
  · intro h
    refine ⟨hpos, ?_⟩
    intro p q hp hq hpl hql
    have heq := (h p hp hpl).trans (h q hq hql).symm
    unfold patternProbability at heq
    rw [((full_patterns_perm p q hp hq hpl hql).map (fun a => s.count a)).prod_eq] at heq
    have hprod : (0 : ℚ) < ((q.map (fun a => s.count a)).prod : ℚ) := by
      apply Nat.cast_pos.mpr
      apply List.prod_pos
      intro c hc
      obtain ⟨a, _, rfl⟩ := List.mem_map.mp hc
      exact List.count_pos_iff.mpr (hpos a)
    exact_mod_cast (div_left_inj' hprod.ne').mp heq

end FairDice
