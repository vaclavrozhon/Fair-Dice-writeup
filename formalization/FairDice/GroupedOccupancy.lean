import FairDice.SelectedOccupancy

open scoped Classical

namespace FairDice

/-- The literal occupancies in every unselected block gap. -/
abbrev GapOccupancies {ell : ℕ} (g a : Fin (ell+1) → ℕ) :=
  ∀ j, {b : Fin (g j) → ℕ // b ∈ Finset.piAntidiag Finset.univ (a j)}

/-- Assign selected lengths and individual gap occupancies to the actual
block labels through a partition of those labels. -/
def groupedOccupancy {ell m : ℕ} (g : Fin (ell+1) → ℕ)
    (E : Fin m ≃ (Fin ell ⊕ Sigma (fun j => Fin (g j))))
    (k : Fin ell → ℕ) (a : Fin (ell+1) → ℕ) (b : GapOccupancies g a) : Fin m → ℕ :=
  fun i => match E i with
    | .inl j => k j
    | .inr v => (b v.1).val v.2

theorem groupedOccupancy_sum {ell m : ℕ} (g a : Fin (ell+1) → ℕ)
    (E : Fin m ≃ (Fin ell ⊕ Sigma (fun j => Fin (g j))))
    (k : Fin ell → ℕ) (b : GapOccupancies g a) :
    (∑ i, groupedOccupancy g E k a b i)=(∑ j, k j)+∑ j, a j := by
  classical
  have he := Fintype.sum_equiv E (fun i => groupedOccupancy g E k a b i)
    (fun v => match v with | .inl j => k j | .inr v => (b v.1).val v.2) (fun _ => rfl)
  rw [he,Fintype.sum_sum_type,Fintype.sum_sigma]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  exact (Finset.mem_piAntidiag.mp (b j).property).1

theorem groupedOccupancy_factorials {ell m : ℕ} (g a : Fin (ell+1) → ℕ)
    (E : Fin m ≃ (Fin ell ⊕ Sigma (fun j => Fin (g j))))
    (k : Fin ell → ℕ) (b : GapOccupancies g a) :
    (∏ i, ((groupedOccupancy g E k a b i).factorial : ℝ))=
      (∏ j, ((k j).factorial : ℝ)) * ∏ j, ∏ i, (((b j).val i).factorial : ℝ) := by
  have he := Fintype.prod_equiv E (fun i => ((groupedOccupancy g E k a b i).factorial : ℝ))
    (fun v => match v with
      | .inl j => ((k j).factorial : ℝ)
      | .inr v => (((b v.1).val v.2).factorial : ℝ))
    (by intro i; cases he : E i <;> simp [groupedOccupancy,he])
  rw [he,Fintype.prod_sum_type,Fintype.prod_sigma]

/-- Summing over the actual unselected block coordinates of a fixed
selected/gap partition gives exactly `selectedGapMass`. -/
theorem grouped_uniform_occupancy_mass {ell m : ℕ} (s d : ℕ)
    (g a : Fin (ell+1) → ℕ)
    (E : Fin m ≃ (Fin ell ⊕ Sigma (fun j => Fin (g j))))
    (k : Fin ell → ℕ) (hs : ∑ j, k j=s) (ha : ∑ j, a j=d) :
    (∑ b : GapOccupancies g a,
      multinomialMass (s+d) (fun _ : Fin m => (1 : ℝ)/m) (groupedOccupancy g E k a b)) =
        selectedGapMass m s d k g a := by
  classical
  have hm (b : GapOccupancies g a) :
      multinomialMass (s+d) (fun _ : Fin m => (1 : ℝ)/m) (groupedOccupancy g E k a b) =
        ((s+d).factorial : ℝ)/((m : ℝ)^(s+d)*(∏ j, ((k j).factorial : ℝ))) *
          ∏ j, 1/(∏ i, (((b j).val i).factorial : ℝ)) := by
    have hsum : ∑ i, groupedOccupancy g E k a b i=s+d := by
      rw [groupedOccupancy_sum,hs,ha]
    rw [multinomialMass_factorial _ _ _ hsum,groupedOccupancy_factorials]
    simp only [one_div]
    rw [Finset.prod_pow_eq_pow_sum,hsum,Finset.prod_inv_distrib]
    ring
  simp_rw [hm]
  rw [← Finset.mul_sum]
  have hp := Fintype.prod_sum (ι := Fin (ell+1))
    (κ := fun j => {b : Fin (g j) → ℕ // b ∈ Finset.piAntidiag Finset.univ (a j)})
    (fun j b => (1 : ℝ)/(∏ i, ((b.val i).factorial : ℝ)))
  rw [← hp]
  unfold selectedGapMass
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  exact Finset.sum_coe_sort _ (fun b : Fin (g j) → ℕ => 1/(∏ i, ((b i).factorial : ℝ)))

/-- Conditions on the actual block occupancy vector: selected lengths are
fixed and the unselected letters have prescribed total in each gap. -/
def groupedOccupancyEvent {ell m : ℕ} (g : Fin (ell+1) → ℕ)
    (E : Fin m ≃ (Fin ell ⊕ Sigma (fun j => Fin (g j))))
    (k : Fin ell → ℕ) (a : Fin (ell+1) → ℕ) (v : Fin m → ℕ) : Prop :=
  (∀ j, v (E.symm (.inl j))=k j) ∧
  ∀ j, ∑ i : Fin (g j), v (E.symm (.inr ⟨j,i⟩))=a j

/-- The assignments in `grouped_uniform_occupancy_mass` enumerate every
occupancy satisfying the selected-length and gap-total constraints exactly
once. The total-letter constraint is derived from these constraints. -/
noncomputable def groupedOccupancyEquiv {ell m : ℕ} (s d : ℕ)
    (g a : Fin (ell+1) → ℕ)
    (E : Fin m ≃ (Fin ell ⊕ Sigma (fun j => Fin (g j))))
    (k : Fin ell → ℕ) (hs : ∑ j, k j=s) (ha : ∑ j, a j=d) :
    GapOccupancies g a ≃
      {v : {v : Fin m → ℕ // v ∈ Finset.piAntidiag Finset.univ (s+d)} //
        groupedOccupancyEvent g E k a v.val} where
  toFun b := ⟨⟨groupedOccupancy g E k a b,by
    apply Finset.mem_piAntidiag.mpr
    exact ⟨by rw [groupedOccupancy_sum,hs,ha],by simp⟩⟩,by
      constructor
      · intro j
        simp [groupedOccupancy]
      · intro j
        simpa [groupedOccupancy] using (Finset.mem_piAntidiag.mp (b j).property).1⟩
  invFun v := fun j => ⟨fun i => v.val.val (E.symm (.inr ⟨j,i⟩)),
    Finset.mem_piAntidiag.mpr ⟨v.property.2 j,by simp⟩⟩
  left_inv b := by
    funext j
    apply Subtype.ext
    funext i
    simp [groupedOccupancy]
  right_inv v := by
    apply Subtype.ext
    apply Subtype.ext
    funext i
    dsimp only
    cases he : E i with
    | inl j =>
      have hi : i=E.symm (.inl j) := (E.eq_symm_apply).mpr he
      simp only [groupedOccupancy,he]
      simpa only [hi] using (v.property.1 j).symm
    | inr w =>
      simp only [groupedOccupancy,he]
      rw [← he,E.symm_apply_apply]

/-- The selected-gap formula is therefore the literal multinomial marginal
of the grouped event, rather than only a separately defined coefficient. -/
theorem grouped_multinomial_marginal {ell m : ℕ} (s d : ℕ)
    (g a : Fin (ell+1) → ℕ)
    (E : Fin m ≃ (Fin ell ⊕ Sigma (fun j => Fin (g j))))
    (k : Fin ell → ℕ) (hs : ∑ j, k j=s) (ha : ∑ j, a j=d) :
    (∑ v : {v : Fin m → ℕ // v ∈ Finset.piAntidiag Finset.univ (s+d)},
      if groupedOccupancyEvent g E k a v.val then
        multinomialMass (s+d) (fun _ : Fin m => (1 : ℝ)/m) v.val else 0) =
      selectedGapMass m s d k g a := by
  classical
  letI : Fintype
      {v : {v : Fin m → ℕ // v ∈ Finset.piAntidiag Finset.univ (s+d)} //
        groupedOccupancyEvent g E k a v.val} :=
    Fintype.subtype (Finset.univ.filter (fun v => groupedOccupancyEvent g E k a v.val))
      (by intro v; simp)
  have hfilter := Finset.sum_subtype (F := inferInstance)
    (p := fun v : {v : Fin m → ℕ // v ∈ Finset.piAntidiag Finset.univ (s+d)} =>
      groupedOccupancyEvent g E k a v.val)
    (Finset.univ.filter (fun v => groupedOccupancyEvent g E k a v.val))
    (by intro v; simp) (fun v => multinomialMass (s+d) (fun _ : Fin m => (1 : ℝ)/m) v.val)
  rw [Finset.sum_filter] at hfilter
  rw [hfilter]
  rw [← Fintype.sum_equiv (groupedOccupancyEquiv s d g a E k hs ha)
    (fun b => multinomialMass (s+d) (fun _ : Fin m => (1 : ℝ)/m) (groupedOccupancy g E k a b))
    (fun v => multinomialMass (s+d) (fun _ : Fin m => (1 : ℝ)/m) v.val.val) (fun _ => rfl)]
  exact grouped_uniform_occupancy_mass s d g a E k hs ha

end FairDice
