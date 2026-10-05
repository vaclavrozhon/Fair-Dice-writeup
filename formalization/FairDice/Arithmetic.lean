import FairDice.Restriction

namespace FairDice

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- The divisibility constraint applies to every subset, not just to all dice. -/
theorem subset_factorial_dvd {s : List α} (hs : PermutationFair s) (A : Finset α) :
    A.card.factorial ∣ ∏ a ∈ A, s.count a := by
  have h := factorial_dvd_pattern_product hs A.toList A.nodup_toList
  simpa only [Finset.length_toList, Finset.prod_map_toList] using h

/-- The key arithmetic step of Lemma 4.2: fewer than `p` dice can have a
number of faces not divisible by the prime `p`. -/
theorem few_multiplicities_not_dvd {s : List α} (hs : PermutationFair s)
    (p : ℕ) (hp : p.Prime) :
    ((Finset.univ : Finset α).filter fun a => ¬p ∣ s.count a).card < p := by
  classical
  by_contra h
  obtain ⟨A, hA, hcard⟩ := Finset.exists_subset_card_eq (Nat.le_of_not_gt h)
  have hd : p ∣ ∏ a ∈ A, s.count a :=
    (Nat.dvd_factorial hp.pos (by omega)).trans (subset_factorial_dvd hs A)
  obtain ⟨a, ha, hpa⟩ := (hp.prime.dvd_finsetProd_iff _).mp hd
  exact (Finset.mem_filter.mp (hA ha)).2 hpa

/-- A quantitative version of the same step, useful before applying any
external estimate on primorial growth. -/
theorem many_multiplicities_dvd {s : List α} (hs : PermutationFair s)
    (p : ℕ) (hp : p.Prime) :
    Fintype.card α + 1 - p ≤
      ((Finset.univ : Finset α).filter fun a => p ∣ s.count a).card := by
  classical
  have hsmall := few_multiplicities_not_dvd hs p hp
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset α)) (fun a => p ∣ s.count a)
  simp only [Finset.card_univ] at hpartition
  omega

/-- Simultaneously use distinct prime divisors of each face count. The result
is stronger than applying the individual divisibility inequalities separately. -/
theorem prime_product_power_bound {s : List α} (hs : PermutationFair s)
    (P : Finset ℕ) (m : ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hm : ∀ p ∈ P, m + p ≤ Fintype.card α + 1) :
    (∏ p ∈ P, p)^m ≤ ∏ a : α, s.count a := by
  classical
  have hcard (p : ℕ) (hp : p ∈ P) :
      m ≤ ((Finset.univ : Finset α).filter fun a => p ∣ s.count a).card := by
    have := many_multiplicities_dvd hs p (hP p hp)
    have := hm p hp
    omega
  calc
    _ = ∏ p ∈ P, p^m := (Finset.prod_pow P m id).symm
    _ ≤ ∏ p ∈ P, p^((Finset.univ : Finset α).filter fun a => p ∣ s.count a).card := by
      apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
      intro p hp
      exact Nat.pow_le_pow_right (hP p hp).pos (hcard p hp)
    _ = ∏ p ∈ P, ∏ a : α, if p ∣ s.count a then p else 1 := by
      apply Finset.prod_congr rfl
      intro p _
      simp [Finset.prod_ite]
    _ = ∏ a : α, ∏ p ∈ P, if p ∣ s.count a then p else 1 := Finset.prod_comm
    _ ≤ ∏ a : α, s.count a := by
      apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
      intro a _
      have hd : (∏ p ∈ P.filter (fun p => p ∣ s.count a), p) ∣ s.count a := by
        apply Finset.prod_primes_dvd
        · intro p hp
          exact (hP p (Finset.mem_filter.mp hp).1).prime
        · intro p hp
          exact (Finset.mem_filter.mp hp).2
      simpa only [Finset.prod_filter] using Nat.le_of_dvd (List.count_pos_iff.mpr (hs.1 a)) hd

/-- The finite primorial inequality at the heart of Lemma 4.2. -/
theorem primorial_face_product_bound {s : List α} (hs : PermutationFair s) :
    (primorial (Fintype.card α / 2))^(Fintype.card α / 2) ≤ ∏ a : α, s.count a := by
  apply prime_product_power_bound hs
  · intro p hp
    exact (Finset.mem_filter.mp hp).2
  · intro p hp
    have := Finset.mem_range.mp (Finset.mem_filter.mp hp).1
    omega

theorem primorial_length_bound {s : List α} (hs : PermutationFair s) :
    (primorial (Fintype.card α / 2))^(Fintype.card α / 2) ≤ s.length^(Fintype.card α) := by
  apply (primorial_face_product_bound hs).trans
  simpa using Finset.prod_le_pow_card (Finset.univ : Finset α) (fun a => s.count a)
    s.length (fun a _ => List.count_le_length)

end FairDice
