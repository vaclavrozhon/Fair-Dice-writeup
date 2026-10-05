import FairDice.CutOccupancy

open scoped Classical

namespace FairDice

/-- The selected block set can be recovered from the segment monomial. -/
theorem cutGraph_image_blocks {n m : ℕ} (ps : List (List (Fin n)))
    (hlen : ps.length=m) (hflat : ps.flatten.length=n)
    (I : Finset (Fin m)) (hI : ∀ i ∈ I, 3 ≤ (ps[i.val]?.getD []).length) :
    (cutGraph ps hlen hflat I hI).image (fun v => v.1)=I := by
  classical
  ext b
  constructor
  · intro hb
    obtain ⟨v,hv,he⟩ := Finset.mem_image.mp hb
    unfold cutGraph at hv
    obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hv
    exact he ▸ i.property
  · intro hb
    unfold cutGraph
    apply Finset.mem_image.mpr
    refine ⟨_,Finset.mem_map.mpr ⟨⟨b,hb⟩,Finset.mem_univ _,rfl⟩,rfl⟩

theorem palindromeCutCoefficient_block_set {n m : ℕ} (σ : Equiv.Perm (Fin n))
    (I : Finset (Fin m)) (j : CutIndex σ m) (K : Finset (BlockSegment (Fin m) n))
    (hI : I≠K.image (fun v => v.1)) : palindromeCutCoefficient σ I j K=0 := by
  classical
  unfold palindromeCutCoefficient
  split_ifs with h he
  · apply False.elim
    apply hI
    rw [← he]
    exact (cutGraph_image_blocks _ _ _ _ _).symm
  all_goals rfl

/-- Once the segment monomial is fixed, its selected block set is fixed as
well, so grouping over block selections contributes no extra multiplicity. -/
theorem palindromeSegmentCoefficient_fixed_blocks {n m : ℕ} (σ : Equiv.Perm (Fin n))
    (ell : ℕ) (K : Finset (BlockSegment (Fin m) n)) :
    palindromeSegmentCoefficient σ ell K =
      if (K.image (fun v => v.1)).card=ell then
        ∑ j : CutIndex σ m, palindromeCutCoefficient σ (K.image (fun v => v.1)) j K
      else 0 := by
  classical
  unfold palindromeSegmentCoefficient
  let J := K.image (fun v => v.1)
  by_cases hJ : J.card=ell
  · rw [if_pos hJ]
    apply Finset.sum_eq_single J
    · intro I _ hIJ
      apply Finset.sum_eq_zero
      intro j _
      exact palindromeCutCoefficient_block_set σ I j K hIJ
    · intro hnot
      exact False.elim (hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ J,hJ⟩))
  · rw [if_neg hJ]
    apply Finset.sum_eq_zero
    intro I hI
    apply Finset.sum_eq_zero
    intro j _
    apply palindromeCutCoefficient_block_set
    intro he
    apply hJ
    change (K.image (fun v => v.1)).card=ell
    rw [← he]
    exact (Finset.mem_filter.mp hI).2

/-- Selected-segment constraints read directly on the actual multinomial
occupancy space, via the cut bijection. This is a literal finite event. -/
noncomputable def occupancySegmentEvent {n m : ℕ} (σ : Equiv.Perm (Fin n))
    (I : Finset (Fin m)) (K : Finset (BlockSegment (Fin m) n))
    (k : {k : Fin m → ℕ // k ∈ Finset.piAntidiag Finset.univ n}) : Prop :=
  ∃ h : ∀ i ∈ I, 3 ≤ ((cutAt σ ((cutOccupancyEquiv σ).symm k))[i.val]?.getD []).length,
    cutGraphAt σ I ((cutOccupancyEquiv σ).symm k) h=K

theorem palindromeCutCoefficient_occupancy_event {n m : ℕ} (σ : Equiv.Perm (Fin n))
    (I : Finset (Fin m)) (K : Finset (BlockSegment (Fin m) n))
    (k : {k : Fin m → ℕ // k ∈ Finset.piAntidiag Finset.univ n}) :
    palindromeCutCoefficient σ I ((cutOccupancyEquiv σ).symm k) K =
      if occupancySegmentEvent σ I K k then
        multinomialMass n (fun _ : Fin m => (1 : ℝ)/m) k.val else 0 := by
  classical
  have hk : cutOccupancy σ ((cutOccupancyEquiv σ).symm k)=k.val :=
    congrArg Subtype.val ((cutOccupancyEquiv σ).apply_symm_apply k)
  unfold palindromeCutCoefficient
  by_cases h : ∀ i ∈ I, 3 ≤ ((cutAt σ ((cutOccupancyEquiv σ).symm k))[i.val]?.getD []).length
  · rw [dif_pos h]
    by_cases he : cutGraphAt σ I ((cutOccupancyEquiv σ).symm k) h=K
    · have hh : occupancySegmentEvent σ I K k := ⟨h,he⟩
      rw [if_pos he,if_pos hh,palindromeCutWeight_occupancy,hk]
    · have hh : ¬ occupancySegmentEvent σ I K k := by
        rintro ⟨h',he'⟩
        exact he he'
      rw [if_neg he,if_neg hh]
  · have hh : ¬ occupancySegmentEvent σ I K k := by
      rintro ⟨h',_⟩
      exact h h'
    rw [dif_neg h,if_neg hh]

/-- The actual selected-segment coefficient is an actual multinomial
marginal, with its event and block set derived rather than assumed. -/
theorem palindromeSegmentCoefficient_multinomial {n m : ℕ} (σ : Equiv.Perm (Fin n))
    (ell : ℕ) (K : Finset (BlockSegment (Fin m) n)) :
    palindromeSegmentCoefficient σ ell K =
      if (K.image (fun v => v.1)).card=ell then
        ∑ k : {k : Fin m → ℕ // k ∈ Finset.piAntidiag Finset.univ n},
          if occupancySegmentEvent σ (K.image (fun v => v.1)) K k then
            multinomialMass n (fun _ : Fin m => (1 : ℝ)/m) k.val else 0
      else 0 := by
  classical
  rw [palindromeSegmentCoefficient_fixed_blocks]
  split_ifs with h
  · rw [Fintype.sum_equiv (cutOccupancyEquiv (m := m) σ)
      (fun j => palindromeCutCoefficient σ (K.image (fun v => v.1)) j K)
      (fun k => palindromeCutCoefficient σ (K.image (fun v => v.1)) ((cutOccupancyEquiv σ).symm k) K)
      (fun j => by rw [Equiv.symm_apply_apply])]
    simp_rw [palindromeCutCoefficient_occupancy_event]
  · rfl

end FairDice
