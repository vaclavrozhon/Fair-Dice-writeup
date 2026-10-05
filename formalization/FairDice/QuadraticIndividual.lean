import FairDice.LastRow
import FairDice.ComparisonModel

namespace FairDice

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- The lower half of the new Theorem `thm:individual-size`, for actual
permutation-fair words, including unequal face counts. The classical
quadrature input contains no dice-specific inequality. -/
theorem each_die_quadratic (hext : ClassicalQuadratureExternal)
    {s : List α} (hs : PermutationFair s) (hn : 2 ≤ Fintype.card α) (a : α) :
    ((Fintype.card α : ℝ) - 1)^2 / 200 ≤ s.count a := by
  classical
  let A := comparisonModel hs a
  let K := (faceSuffixes a s).reverse.length
  have hK : K = s.count a := by simp [K, length_faceSuffixes]
  have hKpos : 0 < K := by rw [hK]; exact List.count_pos_iff.mpr (hs.1 a)
  let last : Fin K := ⟨K - 1, by omega⟩
  have hlast (q : Fin K) : q ≤ last := by show q.val ≤ K - 1; omega
  have hcard : Fintype.card {b : α // b ≠ a} = Fintype.card α - 1 := by
    simp [Fintype.card_subtype_compl]
  have hm : 0 < Fintype.card {b : α // b ≠ a} := by rw [hcard]; omega
  have hh := last_row_weight_bound hext A last hlast hm
  change 1 / (s.count a : ℝ) ≤ 200 / (Fintype.card {b : α // b ≠ a} : ℝ)^2 at hh
  rw [hcard] at hh
  have hsub : ((Fintype.card α - 1 : ℕ) : ℝ) = (Fintype.card α : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  rw [hsub] at hh
  have hc : (0 : ℝ) < s.count a := by exact_mod_cast List.count_pos_iff.mpr (hs.1 a)
  have hnR : (2 : ℝ) ≤ Fintype.card α := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (Fintype.card α : ℝ) - 1 := by linarith
  have hden : (0 : ℝ) < ((Fintype.card α : ℝ) - 1)^2 := sq_pos_of_pos hn1
  have h := (div_le_div_iff₀ hc hden).mp hh
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 200)).mpr
  nlinarith

end FairDice
