import FairDice.GapEnergy

namespace FairDice

/-- A finite sum of nonnegative terms cannot decrease when an injective
index set is enlarged. -/
theorem finite_sum_embedding_le {U V : Type*} [Fintype U] [Fintype V]
    (e : U ↪ V) (f : V → ℝ) (hf : ∀ v, 0 ≤ f v) :
    (∑ u, f (e u)) ≤ ∑ v, f v := by
  classical
  calc
    _ = ∑ v ∈ Finset.univ.image e, f v := (Finset.sum_image e.injective.injOn).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun v _ _ => hf v)

/-- Sum the collision energies over the literal selected block sets. The
proved gap embedding introduces no additional multiplicity. -/
theorem actual_block_collision_lattice (H : PoissonEstimates) (ell m d : ℕ)
    (hell : 1 ≤ ell) (hM : d+1 ≤ m-ell) :
    (∑ I : BlockSelection ell m,
      multinomialCollision d (fun r => (blockSelectionGaps I r : ℝ)/(m-ell : ℕ))) ≤
        (108*(m-ell : ℕ)/Real.sqrt (d+1 : ℝ))^ell := by
  have hn (g : {g : Fin (ell+1) → ℕ // g ∈ Finset.piAntidiag Finset.univ (m-ell)}) :
      0 ≤ multinomialCollision d (fun r => (g.val r : ℝ)/(m-ell : ℕ)) := by
    unfold multinomialCollision
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have he := finite_sum_embedding_le (blockSelectionGapEmbedding (ell := ell) (m := m))
    (fun g => multinomialCollision d (fun r => (g.val r : ℝ)/(m-ell : ℕ))) hn
  have hright : (∑ g : {g : Fin (ell+1) → ℕ // g ∈ Finset.piAntidiag Finset.univ (m-ell)},
      multinomialCollision d (fun r => (g.val r : ℝ)/(m-ell : ℕ))) =
        ∑ g ∈ Finset.piAntidiag (Finset.univ : Finset (Fin (ell+1))) (m-ell),
          multinomialCollision d (fun r => (g r : ℝ)/(m-ell : ℕ)) :=
    Finset.sum_coe_sort (Finset.piAntidiag (Finset.univ : Finset (Fin (ell+1))) (m-ell))
      (fun g : Fin (ell+1) → ℕ => multinomialCollision d (fun r => (g r : ℝ)/(m-ell : ℕ)))
  rw [hright] at he
  exact he.trans (palindrome_lattice_bound H ell d (m-ell) hell hM)

/-- The manuscript's lattice energy estimate now applies to the actual
segment coefficients summed over all selected block sets and all gap
letter-count vectors, for a fixed selected length vector. -/
theorem actual_selected_lattice_energy (H : PoissonEstimates) (ell m s d : ℕ)
    (σ : Equiv.Perm (Fin (s+d))) (k : Fin ell → ℕ)
    (hs : ∑ j, k j=s) (hk : ∀ j, 3 ≤ k j) (hell : 1 ≤ ell)
    (hm : 0 < m) (hM : d+1 ≤ m-ell) :
    (∑ I : BlockSelection ell m,
      ∑ a : {a : Fin (ell+1) → ℕ // a ∈ Finset.piAntidiag Finset.univ d},
        let P := blockGapPartition (I.val.orderEmbOfFin I.property)
        let K := Finset.univ.image (gapSegments s d P k a.val hs
          (Finset.mem_piAntidiag.mp a.property).1 hk)
        (palindromeSegmentCoefficient σ ell K)^2 *
          (∏ v ∈ K, (segmentErrorBound v)^2/segmentRetentionWeight v.2)) ≤
      (((s+d).descFactorial s : ℝ)/(m : ℝ)^s)^2 *
        (((m-ell : ℕ) : ℝ)/m)^(2*d) * (∏ j, (k j : ℝ)/(2 : ℝ)^k j) *
          (108*(m-ell : ℕ)/Real.sqrt (d+1 : ℝ))^ell := by
  simp_rw [actual_gap_colored_squared_sum s d σ _ k hs hk hm (by omega : 0 < m-ell)]
  change (∑ I : BlockSelection ell m,
    (((s+d).descFactorial s : ℝ)/(m : ℝ)^s)^2 *
      (((m-ell : ℕ) : ℝ)/m)^(2*d) * (∏ j, (k j : ℝ)/(2 : ℝ)^k j) *
        multinomialCollision d (fun r => (blockSelectionGaps I r : ℝ)/(m-ell : ℕ))) ≤ _
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (actual_block_collision_lattice H ell m d hell hM)
    (by positivity)

/-- The concrete colored square-energy for one selected length vector. -/
noncomputable def actualLengthEnergy {ell m : ℕ} (s d : ℕ)
    (σ : Equiv.Perm (Fin (s+d))) (k : Fin ell → ℕ)
    (hs : ∑ j, k j=s) (hk : ∀ j, 3 ≤ k j) : ℝ :=
  ∑ I : BlockSelection ell m,
    ∑ a : {a : Fin (ell+1) → ℕ // a ∈ Finset.piAntidiag Finset.univ d},
      let P := blockGapPartition (I.val.orderEmbOfFin I.property)
      let K := Finset.univ.image (gapSegments s d P k a.val hs
        (Finset.mem_piAntidiag.mp a.property).1 hk)
      (palindromeSegmentCoefficient σ ell K)^2 *
        (∏ v ∈ K, (segmentErrorBound v)^2/segmentRetentionWeight v.2)

/-- The actual colored length energy is bounded by the full gap lattice
sum. Each literal selected block set has its unique gap vector. -/
theorem actualLengthEnergy_le_gap_sum {ell m : ℕ} (s d : ℕ)
    (σ : Equiv.Perm (Fin (s+d))) (k : Fin ell → ℕ)
    (hs : ∑ j, k j=s) (hk : ∀ j, 3 ≤ k j) :
    actualLengthEnergy (m := m) s d σ k hs hk ≤
      ∑ g ∈ Finset.piAntidiag (Finset.univ : Finset (Fin (ell+1))) (m-ell),
        ∑ a ∈ Finset.piAntidiag (Finset.univ : Finset (Fin (ell+1))) d,
          (selectedGapMass m s d k g a)^2 *
            ∏ j, (((k j).factorial : ℝ)*2/(2 : ℝ)^k j)^2 /
              ((1/(2 : ℝ)^(k j-2))/(k j : ℝ)) := by
  let f := fun g : Fin (ell+1) → ℕ =>
    ∑ a ∈ Finset.piAntidiag (Finset.univ : Finset (Fin (ell+1))) d,
      (selectedGapMass m s d k g a)^2 *
        ∏ j, (((k j).factorial : ℝ)*2/(2 : ℝ)^k j)^2 /
          ((1/(2 : ℝ)^(k j-2))/(k j : ℝ))
  have hf (g) : 0 ≤ f g := by
    apply Finset.sum_nonneg
    intro a _
    exact mul_nonneg (sq_nonneg _) (Finset.prod_nonneg (fun j _ => by positivity))
  have he := finite_sum_embedding_le (blockSelectionGapEmbedding (ell := ell) (m := m))
    (fun g => f g.val) (fun g => hf g.val)
  have hactual : actualLengthEnergy (m := m) s d σ k hs hk=∑ I : BlockSelection ell m, f (blockSelectionGaps I) := by
    unfold actualLengthEnergy
    simp_rw [gap_coefficient_energy]
    apply Finset.sum_congr rfl
    intro I _
    exact Finset.sum_coe_sort (Finset.piAntidiag (Finset.univ : Finset (Fin (ell+1))) d)
      (fun a : Fin (ell+1) → ℕ => (selectedGapMass m s d k (blockSelectionGaps I) a)^2 *
        ∏ j, (((k j).factorial : ℝ)*2/(2 : ℝ)^k j)^2 /
          ((1/(2 : ℝ)^(k j-2))/(k j : ℝ)))
  rw [hactual]
  exact he.trans_eq (Finset.sum_coe_sort
    (Finset.piAntidiag (Finset.univ : Finset (Fin (ell+1))) (m-ell)) f)

/-- The short-support coefficient-energy bound, now for actual monomials
summed over every selected block set and every segment start. -/
theorem actual_short_length_energy (H : PoissonEstimates) (ell m s d : ℕ)
    (σ : Equiv.Perm (Fin (s+d))) (k : Fin ell → ℕ) (hell : 1 ≤ ell)
    (hk : ∀ j, 3 ≤ k j) (hs : ∑ j, k j=s)
    (hshort : 2*s ≤ s+d) (hnm : s+d ≤ m) :
    actualLengthEnergy (m := m) s d σ k hs hk ≤
      (160*m/Real.sqrt ((s+d : ℕ) : ℝ))^ell *
        ∏ j, (k j : ℝ)*(((s+d : ℕ) : ℝ)^2/(2*(m : ℝ)^2))^k j :=
  (actualLengthEnergy_le_gap_sum (m := m) s d σ k hs hk).trans
    (short_selected_colored_energy H ell m (s+d) s d k hell hk hs rfl hshort hnm)

end FairDice
