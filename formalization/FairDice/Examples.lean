import FairDice.Blowup

namespace FairDice

theorem permutationFair_of_permutation_counts {n C : ℕ} {s : List (Fin n)}
    (hmem : ∀ a : Fin n, a ∈ s)
    (h : ∀ p ∈ (List.finRange n).permutations', count p s = C) : PermutationFair s := by
  refine ⟨hmem, ?_⟩
  intro p q hp hq hpl hql
  have hm (r : List (Fin n)) (hr : r.Nodup) (hrl : r.length = Fintype.card (Fin n)) :
      r ∈ (List.finRange n).permutations' :=
    List.mem_permutations'.mpr (full_patterns_perm r (List.finRange n) hr
      (List.nodup_finRange n) hrl (by simp))
  rw [h p (hm p hp hpl), h q (hm q hq hql)]

/-- The sharp three-die example `213122221312`, with symbols shifted down by one. -/
def unequalThree : List (Fin 3) := [1, 0, 2, 0, 1, 1, 1, 1, 0, 2, 0, 1]

theorem unequalThree_counts :
    ∀ p ∈ (List.finRange 3).permutations', count p unequalThree = 8 := by decide

theorem unequalThree_fair : PermutationFair unequalThree :=
  permutationFair_of_permutation_counts (by decide) unequalThree_counts

theorem unequalThree_multiplicities :
    unequalThree.count 0 = 4 ∧ unequalThree.count 1 = 6 ∧ unequalThree.count 2 = 2 := by decide

def simpsonTwo : List (Fin 3) := [1, 0, 0, 0, 1, 1, 1, 1, 0, 0, 0, 1]

/-- The two insertion steps in the Simpson-rule example of Section 3. -/
def simpsonThree : List (Fin 3) :=
  List.replicate 2 2 ++ simpsonTwo ++ List.replicate 8 2 ++ simpsonTwo ++ List.replicate 2 2

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem simpsonThree_counts :
    ∀ p ∈ (List.finRange 3).permutations', count p simpsonThree = 288 := by decide

theorem simpsonThree_fair : PermutationFair simpsonThree :=
  permutationFair_of_permutation_counts (by decide) simpsonThree_counts

theorem simpsonThree_multiplicities : ∀ a : Fin 3, simpsonThree.count a = 12 := by decide

end FairDice
