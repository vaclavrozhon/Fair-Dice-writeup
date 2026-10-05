import FairDice.ActualLattice

open scoped Classical

namespace FairDice

/-- Gap segments without changing the ambient alphabet when lengths vary. -/
def gapSegmentsAt {ell m : ℕ} (n : ℕ) (P : BlockGapPartition ell m)
    (k : Fin ell → ℕ) (a : Fin (ell+1) → ℕ)
    (ht : (∑ j, k j)+(∑ r, a r)=n) (hk : ∀ j, 3 ≤ k j) :
    Fin ell → BlockSegment (Fin m) n := fun j =>
  ⟨P.selected j,segmentOfStart n (selectedGapStart k a j) (k j)
    (by rw [← ht]; exact selectedGapStart_fits k a j) (hk j)⟩

noncomputable def fixedLengthEnergy {ell m n : ℕ} (σ : Equiv.Perm (Fin n))
    (k : Fin ell → ℕ) (ht : (∑ j, k j) ≤ n) (hk : ∀ j, 3 ≤ k j) : ℝ :=
  ∑ I : BlockSelection ell m,
    ∑ a : {a : Fin (ell+1) → ℕ // a ∈ Finset.piAntidiag Finset.univ (n-∑ j, k j)},
      let P := blockGapPartition (I.val.orderEmbOfFin I.property)
      let K := Finset.univ.image (gapSegmentsAt n P k a.val
        (by rw [(Finset.mem_piAntidiag.mp a.property).1]; exact Nat.add_sub_of_le ht) hk)
      (palindromeSegmentCoefficient σ ell K)^2 *
        ∏ v ∈ K, (segmentErrorBound v)^2/segmentRetentionWeight v.2

theorem fixedLengthEnergy_nonneg {ell m n : ℕ} (σ : Equiv.Perm (Fin n))
    (k : Fin ell → ℕ) (ht : (∑ j, k j) ≤ n) (hk : ∀ j, 3 ≤ k j) :
    0 ≤ fixedLengthEnergy (m := m) σ k ht hk := by
  apply Finset.sum_nonneg
  intro I _
  apply Finset.sum_nonneg
  intro a _
  apply mul_nonneg (sq_nonneg _)
  exact Finset.prod_nonneg (fun v _ => div_nonneg (sq_nonneg _) (segmentRetentionWeight_pos v.2).le)

theorem gapSegmentsAt_add {ell m : ℕ} (s d : ℕ) (P : BlockGapPartition ell m)
    (k : Fin ell → ℕ) (a : Fin (ell+1) → ℕ)
    (hs : (∑ j, k j)=s) (ha : (∑ r, a r)=d)
    (ht : (∑ j, k j)+(∑ r, a r)=s+d) (hk : ∀ j, 3 ≤ k j) :
    gapSegmentsAt (s+d) P k a ht hk=gapSegments s d P k a hs ha hk := rfl

theorem fixedLengthEnergy_add {ell m : ℕ} (s d : ℕ)
    (σ : Equiv.Perm (Fin (s+d))) (k : Fin ell → ℕ)
    (hs : (∑ j, k j)=s) (ht : (∑ j, k j) ≤ s+d) (hk : ∀ j, 3 ≤ k j) :
    fixedLengthEnergy (m := m) σ k ht hk=actualLengthEnergy (m := m) s d σ k hs hk := by
  classical
  unfold fixedLengthEnergy actualLengthEnergy
  apply Finset.sum_congr rfl
  intro I _
  let E : {a : Fin (ell+1) → ℕ // a ∈ Finset.piAntidiag Finset.univ (s+d-∑ j, k j)} ≃
      {a : Fin (ell+1) → ℕ // a ∈ Finset.piAntidiag Finset.univ d} :=
    Equiv.subtypeEquivRight (fun a => by rw [hs,Nat.add_sub_cancel_left])
  apply Fintype.sum_equiv E
  intro a
  dsimp only
  have ha : (∑ r, a.val r)=d := by
    have ha := (Finset.mem_piAntidiag.mp a.property).1
    simpa only [hs,Nat.add_sub_cancel_left] using ha
  rw [gapSegmentsAt_add s d _ k a.val hs ha]
  rfl

/-- The lattice estimate on the original fixed alphabet. -/
theorem fixedLengthEnergy_short {ell m n : ℕ} (H : PoissonEstimates)
    (σ : Equiv.Perm (Fin n)) (k : Fin ell → ℕ) (ht : (∑ j, k j) ≤ n)
    (hk : ∀ j, 3 ≤ k j) (hell : 1 ≤ ell)
    (hshort : 2*(∑ j, k j) ≤ n) (hnm : n ≤ m) :
    fixedLengthEnergy (m := m) σ k ht hk ≤
      (160*m/Real.sqrt (n : ℝ))^ell *
        ∏ j, (k j : ℝ)*((n : ℝ)^2/(2*(m : ℝ)^2))^k j := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le ht
  rw [fixedLengthEnergy_add (∑ j, k j) d σ k rfl ht hk]
  exact actual_short_length_energy H ell m (∑ j, k j) d σ k hell hk rfl hshort hnm

/-- Literal selected block sets have the binomial cardinality. -/
theorem blockSelection_card (ell m : ℕ) : Fintype.card (BlockSelection ell m)=m.choose ell := by
  classical
  let E : BlockSelection ell m ≃
      {I // I ∈ (Finset.univ : Finset (Fin m)).powersetCard ell} :=
    Equiv.subtypeEquivRight (fun I => by simp)
  rw [Fintype.card_congr E,Fintype.card_coe,Finset.card_powersetCard]
  simp

/-- Bounding collision probabilities by one gives the estimate used for
long supports and for the finitely many small alphabet sizes. -/
theorem fixedLengthEnergy_global {ell m n : ℕ} (σ : Equiv.Perm (Fin n))
    (k : Fin ell → ℕ) (ht : (∑ j, k j) ≤ n) (hk : ∀ j, 3 ≤ k j)
    (hm : 0 < m) (hnm : n ≤ m) :
    fixedLengthEnergy (m := m) σ k ht hk ≤
      ((m : ℝ)^ell/(ell.factorial : ℝ)) *
        ∏ j, (k j : ℝ)*((n : ℝ)^2/(2*(m : ℝ)^2))^k j := by
  have hell : 3*ell ≤ ∑ j, k j := by
    have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin ell))) (fun j _ => hk j)
    simpa [Nat.mul_comm] using hh
  have hM : 0 < m-ell := by omega
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le ht
  rw [fixedLengthEnergy_add (∑ j, k j) d σ k rfl ht hk]
  unfold actualLengthEnergy
  simp_rw [actual_gap_colored_squared_sum _ _ σ _ k rfl hk hm hM]
  let C : ℝ := (((((∑ j, k j)+d).descFactorial (∑ j, k j) : ℕ) : ℝ)/(m : ℝ)^(∑ j, k j))^2 *
    (((m-ell : ℕ) : ℝ)/m)^(2*d) * (∏ j, (k j : ℝ)/(2 : ℝ)^k j)
  have hcollision (I : BlockSelection ell m) :
      multinomialCollision d (fun r => (blockSelectionGaps I r : ℝ)/(m-ell : ℕ)) ≤ 1 := by
    apply multinomialCollision_le_one
    · intro r; positivity
    · rw [← Finset.sum_div]
      have hg : (∑ r, (blockSelectionGaps I r : ℝ))=(m-ell : ℕ) :=
        by exact_mod_cast blockSelectionGaps_sum I
      rw [hg,div_self (by exact_mod_cast (by omega : m-ell≠0))]
  have hc : C ≤ ∏ j, (k j : ℝ)*((((∑ j, k j)+d : ℕ) : ℝ)^2/(2*(m : ℝ)^2))^k j := by
    have hfall : (((((∑ j, k j)+d).descFactorial (∑ j, k j) : ℕ) : ℝ)/(m : ℝ)^(∑ j, k j))^2 ≤
        (((((∑ j, k j)+d : ℕ) : ℝ)/m)^(∑ j, k j))^2 := by
      apply pow_le_pow_left₀ (by positivity)
      rw [div_pow]
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact_mod_cast Nat.descFactorial_le_pow ((∑ j, k j)+d) (∑ j, k j)
    have hr : (((m-ell : ℕ) : ℝ)/m)^(2*d) ≤ 1 := by
      apply pow_le_one₀ (by positivity)
      apply (div_le_one (by exact_mod_cast hm)).mpr
      exact_mod_cast Nat.sub_le m ell
    dsimp [C]
    calc
      _ ≤ ((((((∑ j, k j)+d : ℕ) : ℝ)/m)^(∑ j, k j))^2) *
        (∏ j, (k j : ℝ)/(2 : ℝ)^k j) := by
        have hh := mul_le_mul hfall hr (by positivity) (by positivity)
        simpa using mul_le_mul_of_nonneg_right hh
          (show 0 ≤ ∏ j, (k j : ℝ)/(2 : ℝ)^k j by positivity)
      _ = _ := colored_length_product _ _ _ k rfl
  change (∑ I : BlockSelection ell m, C *
    multinomialCollision d (fun r => (blockSelectionGaps I r : ℝ)/(m-ell : ℕ))) ≤ _
  calc
    _ ≤ ∑ _I : BlockSelection ell m, C := Finset.sum_le_sum (fun I _ =>
      by simpa using mul_le_mul_of_nonneg_left (hcollision I) (by dsimp [C]; positivity))
    _ = (m.choose ell : ℝ)*C := by simp [blockSelection_card]
    _ ≤ ((m : ℝ)^ell/(ell.factorial : ℝ))*
        (∏ j, (k j : ℝ)*((((∑ j, k j)+d : ℕ) : ℝ)^2/(2*(m : ℝ)^2))^k j) :=
      mul_le_mul (Nat.choose_le_pow_div ell m) hc (by dsimp [C]; positivity) (by positivity)

end FairDice
