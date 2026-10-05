import FairDice.PartialPatterns

namespace FairDice

variable {α : Type*} [DecidableEq α]

/-- Delete all letters outside `A` and use `A` itself as the new alphabet. -/
def restrict (A : Finset α) (s : List α) : List A :=
  s.filterMap fun a => if h : a ∈ A then some ⟨a, h⟩ else none

theorem map_restrict (A : Finset α) (s : List α) :
    (restrict A s).map Subtype.val = s.filter (fun a => decide (a ∈ A)) := by
  induction s with
  | nil => rfl
  | cons a s ih =>
    by_cases h : a ∈ A <;> simp [restrict, h, ← ih]

theorem count_restrict (A : Finset α) (p : List A) (s : List α) :
    count p (restrict A s) = count (p.map Subtype.val) s := by
  rw [← count_map Subtype.val Subtype.val_injective p (restrict A s), map_restrict]
  apply count_filter
  intro a ha
  obtain ⟨b, _, rfl⟩ := List.mem_map.mp ha
  exact decide_eq_true b.property

/-- Claim 2.2(i), with the restricted alphabet represented by a subtype. -/
theorem permutationFair_restrict [Fintype α] {s : List α} (hs : PermutationFair s)
    (A : Finset α) : PermutationFair (restrict A s) := by
  constructor
  · intro a
    apply List.mem_filterMap.mpr
    exact ⟨a.val, hs.1 a.val, by simp [a.property]⟩
  · intro p q hp hq hpl hql
    rw [count_restrict, count_restrict]
    apply permutationFair_partialOrder hs (p.map Subtype.val)
      (hp.map Subtype.val_injective)
    · exact List.Perm.refl _
    · exact (full_patterns_perm q p hq hp hql hpl).map Subtype.val

/-- Every partial subset has the factorial divisibility used in Section 4. -/
theorem factorial_dvd_pattern_product [Fintype α] {s : List α}
    (hs : PermutationFair s) (p : List α) (hp : p.Nodup) :
    p.length.factorial ∣ (p.map (fun a => s.count a)).prod :=
  ⟨count p s, (partial_count_product hs p hp).symm⟩

theorem factorial_dvd_face_product [Fintype α] {s : List α}
    (hs : PermutationFair s) : (Fintype.card α).factorial ∣ ∏ a : α, s.count a := by
  classical
  have h := factorial_dvd_pattern_product hs
    (Finset.univ : Finset α).toList (Finset.nodup_toList _)
  simpa only [Finset.length_toList, Finset.card_univ, Finset.prod_map_toList] using h

end FairDice
