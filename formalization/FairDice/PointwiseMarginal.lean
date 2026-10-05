import FairDice.FirstRanks
import FairDice.InsertionFairness

namespace FairDice

variable {α : Type*} [DecidableEq α] [Fintype α]

theorem pointwise_implies_first_marginal {s : List α} (hpos : ∀ a : α, a ∈ s)
    {δ : ℝ} (hpoint : ∀ p : List α, p.Nodup → p.length = Fintype.card α →
      (patternProbability s p : ℝ) ≤ (1 + δ) / ((Fintype.card α).factorial : ℝ)) :
    ∀ a : α, (winCount a s : ℝ) ≤ (1 + δ) / Fintype.card α * outcomeCount s := by
  intro a
  classical
  letI : Nonempty α := ⟨a⟩
  let n := Fintype.card α
  let L := (Finset.univ.erase a).toList.permutations'
  let B : ℝ := (1 + δ) / (n.factorial : ℝ) * outcomeCount s
  have hn : 0 < n := Fintype.card_pos
  have hO : (0 : ℝ) < outcomeCount s := by
    exact_mod_cast (Finset.prod_pos (fun b (_ : b ∈ (Finset.univ : Finset α)) =>
      List.count_pos_iff.mpr (hpos b)) : 0 < outcomeCount s)
  have hterm (p : List α) (hp : p ∈ L) : (count (a :: p) s : ℝ) ≤ B := by
    have hperm := List.mem_permutations'.mp hp
    have hpnd : (a :: p).Nodup := by
      apply List.nodup_cons.mpr
      refine ⟨?_, hperm.nodup_iff.mpr (Finset.nodup_toList _)⟩
      intro hh
      have hh' := hperm.mem_iff.mp hh
      simp at hh'
    have hplen : (a :: p).length = n := by simp [hperm.length_eq, n]; omega
    have hh := hpoint (a :: p) hpnd hplen
    have he : (patternProbability s (a :: p) : ℝ) = (count (a :: p) s : ℝ) / outcomeCount s := by
      unfold patternProbability
      rw [full_pattern_face_product hpnd hplen]
      push_cast
      simp only [outcomeCount, Nat.cast_prod]
    rw [he] at hh
    exact (div_le_iff₀ hO).mp hh
  have hh := List.sum_le_sum hterm
  have hlen : L.length = (n - 1).factorial := by
    dsimp [L]
    rw [← (List.permutations_perm_permutations' _).length_eq, List.length_permutations]
    simp [n]
  have hsum : (L.map (fun p => (count (a :: p) s : ℝ))).sum = (winCount a s : ℝ) := by
    rw [winCount_eq_pattern_sum]
    simp only [Nat.cast_list_sum, List.map_map, Function.comp_def, L]
  rw [hsum] at hh
  simp only [List.map_const', List.sum_replicate, hlen, nsmul_eq_mul] at hh
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
  have hfacR : ((n - 1).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n - 1)
  have he : ((n - 1).factorial : ℝ) * B = (1 + δ) / n * outcomeCount s := by
    dsimp [B]
    rw [show n.factorial = n * (n - 1).factorial by
      simpa only [Nat.sub_add_cancel hn] using Nat.factorial_succ (n - 1)]
    push_cast
    field_simp
  exact he ▸ hh

theorem pointwise_approximation_length_lower {s : List α} (hpos : ∀ a : α, a ∈ s)
    {δ : ℝ} (hδ : 0 ≤ δ) (hlarge : 4 * (1 + δ) ≤ Fintype.card α)
    (hpoint : ∀ p : List α, p.Nodup → p.length = Fintype.card α →
      |(patternProbability s p : ℝ) - 1 / ((Fintype.card α).factorial : ℝ)| ≤
        δ / ((Fintype.card α).factorial : ℝ)) :
    (Fintype.card α : ℝ)^2 / (8 * (1 + δ)^2) ≤ s.length := by
  apply approximate_goFirst_quadratic hpos hδ hlarge
  apply pointwise_implies_first_marginal hpos
  intro p hp hlen
  have hh := (abs_le.mp (hpoint p hp hlen)).2
  rw [add_div]
  linarith

end FairDice
