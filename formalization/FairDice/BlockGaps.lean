import FairDice.CoefficientOccupancy
import FairDice.GroupedOccupancy
import Mathlib.Data.Finset.Sort

open scoped Classical

namespace FairDice

abbrev BlockSelection (ell m : ℕ) := {I : Finset (Fin m) // I.card=ell}

noncomputable instance blockSelectionFintype (ell m : ℕ) : Fintype (BlockSelection ell m) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

/-- The gap containing an unselected block is the number of selected blocks
strictly before it. -/
noncomputable def blockGapIndex {ell m : ℕ} (t : Fin ell ↪o Fin m)
    (u : {u : Fin m // u ∉ Set.range t}) : Fin (ell+1) :=
  ⟨((Finset.univ : Finset (Fin ell)).filter (fun j => t j<u.val)).card,
    by have h := Finset.card_le_univ ((Finset.univ : Finset (Fin ell)).filter (fun j => t j<u.val))
       simp only [Fintype.card_fin] at h
       omega⟩

/-- The actual consecutive-gap classification respects the order of blocks. -/
theorem blockGapIndex_before {ell m : ℕ} (t : Fin ell ↪o Fin m)
    (u : {u : Fin m // u ∉ Set.range t}) (j : Fin ell) :
    u.val<t j ↔ (blockGapIndex t u).val≤j.val := by
  have hne : u.val≠t j := by intro h; exact u.property ⟨j,h.symm⟩
  change u.val<t j ↔ ((Finset.univ : Finset (Fin ell)).filter (fun i => t i<u.val)).card≤j.val
  constructor
  · intro hu
    have hsub : ((Finset.univ : Finset (Fin ell)).filter (fun i => t i<u.val)) ⊆ Finset.Iio j := by
      intro i hi
      apply Finset.mem_Iio.mpr
      exact t.lt_iff_lt.mp ((Finset.mem_filter.mp hi).2.trans hu)
    simpa only [Fin.card_Iio] using Finset.card_le_card hsub
  · intro hc
    by_contra hu
    have hju : t j<u.val := lt_of_le_of_ne (le_of_not_gt hu) hne.symm
    have hsub : Finset.Iic j ⊆ ((Finset.univ : Finset (Fin ell)).filter (fun i => t i<u.val)) := by
      intro i hi
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i,(t.monotone (Finset.mem_Iic.mp hi)).trans_lt hju⟩
    have hh := Finset.card_le_card hsub
    simp only [Fin.card_Iic] at hh
    omega

/-- A literal partition of block labels into selected blocks and their
ordered gaps. Only the order of gap membership matters; labels within one
gap may be enumerated in any order. -/
structure BlockGapPartition (ell m : ℕ) where
  selected : Fin ell ↪o Fin m
  gapSize : Fin (ell+1) → ℕ
  labels : Fin m ≃ (Fin ell ⊕ Sigma (fun j => Fin (gapSize j)))
  selected_label : ∀ j, labels.symm (.inl j)=selected j
  gap_before : ∀ j r i, labels.symm (.inr ⟨r,i⟩)<selected j ↔ r.val≤j.val

/-- Every actual ordered selected block set has the gap partition used by
the manuscript's coefficient calculation. -/
noncomputable def blockGapPartition {ell m : ℕ} (t : Fin ell ↪o Fin m) : BlockGapPartition ell m := by
  let U := {u : Fin m // u ∉ Set.range t}
  letI : Fintype U := Fintype.ofInjective Subtype.val Subtype.val_injective
  let gap := blockGapIndex t
  let fiber := fun r : Fin (ell+1) => {u : U // gap u=r}
  letI (r : Fin (ell+1)) : Fintype (fiber r) := Fintype.ofInjective Subtype.val Subtype.val_injective
  let g := fun r => Fintype.card (fiber r)
  let S := Equiv.ofInjective t t.injective
  let V : U ≃ Sigma (fun r => Fin (g r)) :=
    (Equiv.sigmaFiberEquiv gap).symm.trans (Equiv.sigmaCongrRight (fun r => Fintype.equivFin (fiber r)))
  let E : Fin m ≃ (Fin ell ⊕ Sigma (fun r => Fin (g r))) :=
    (Equiv.sumCompl (fun i : Fin m => i ∈ Set.range t)).symm.trans (Equiv.sumCongr S.symm V)
  refine ⟨t,g,E,?_,?_⟩
  · intro j
    rfl
  · intro j r i
    let u : U := ((Fintype.equivFin (fiber r)).symm i).val
    have hu : gap u=r := ((Fintype.equivFin (fiber r)).symm i).property
    have he : E.symm (.inr ⟨r,i⟩)=u.val := by rfl
    rw [he,blockGapIndex_before]
    change (gap u).val≤j.val ↔ r.val≤j.val
    rw [hu]

/-- The number of unselected blocks is exactly the sum of the gap sizes. -/
theorem BlockGapPartition.gap_sum {ell m : ℕ} (P : BlockGapPartition ell m) :
    ∑ r, P.gapSize r=m-ell := by
  have he := Fintype.card_congr P.labels
  simp only [Fintype.card_fin,Fintype.card_sum,Fintype.card_sigma] at he
  omega

/-- Every prefix before a selected block is exactly the preceding selected
coordinates plus all coordinates in its preceding gaps. -/
theorem BlockGapPartition.prefix_sum {ell m : ℕ} (P : BlockGapPartition ell m)
    (v : Fin m → ℕ) (j : Fin ell) :
    (∑ i ∈ (Finset.univ : Finset (Fin m)).filter (fun i => i<P.selected j), v i) =
      (∑ r ∈ Finset.Iio j, v (P.selected r)) +
        ∑ r ∈ (Finset.univ : Finset (Fin (ell+1))).filter (fun r => r.val≤j.val),
          ∑ i, v (P.labels.symm (.inr ⟨r,i⟩)) := by
  rw [Finset.sum_filter]
  have he := Fintype.sum_equiv P.labels (fun i => if i<P.selected j then v i else 0)
    (fun w => if P.labels.symm w<P.selected j then v (P.labels.symm w) else 0)
    (fun i => by simp)
  rw [he,Fintype.sum_sum_type,Fintype.sum_sigma]
  simp_rw [P.selected_label,P.selected.lt_iff_lt,P.gap_before]
  congr 1
  · simpa only [← Finset.mem_Iio] using Finset.sum_ite_mem_eq (Finset.Iio j) (fun r => v (P.selected r))
  · have hh (r : Fin (ell+1)) :
        (∑ i : Fin (P.gapSize r), if r.val≤j.val then v (P.labels.symm (.inr ⟨r,i⟩)) else 0) =
          if r.val≤j.val then ∑ i, v (P.labels.symm (.inr ⟨r,i⟩)) else 0 := by
        by_cases hr : r.val≤j.val <;> simp [hr]
    simp_rw [hh]
    exact (Finset.sum_filter _ _).symm

/-- The segment starts appearing in the coefficient event are cumulative
selected lengths and cumulative gap totals. -/
theorem BlockGapPartition.prefix_of_event {ell m : ℕ} (P : BlockGapPartition ell m)
    (k : Fin ell → ℕ) (a : Fin (ell+1) → ℕ) (v : Fin m → ℕ)
    (h : groupedOccupancyEvent P.gapSize P.labels k a v) (j : Fin ell) :
    (∑ i ∈ (Finset.univ : Finset (Fin m)).filter (fun i => i<P.selected j), v i) =
      (∑ r ∈ Finset.Iio j, k r) +
        ∑ r ∈ (Finset.univ : Finset (Fin (ell+1))).filter (fun r => r.val≤j.val), a r := by
  rw [P.prefix_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro r _
    rw [← P.selected_label]
    exact h.1 r
  · apply Finset.sum_congr rfl
    intro r _
    exact h.2 r

/-- Cumulative sums uniquely determine a finite vector, including zero
entries. This is the inversion of the segment-start coordinates. -/
theorem fin_prefix_sums_injective {N : ℕ} (a b : Fin N → ℕ)
    (h : ∀ j, (∑ r ∈ Finset.Iic j, a r)=∑ r ∈ Finset.Iic j, b r) : a=b := by
  funext j
  induction hj : j.val using Nat.strong_induction_on generalizing j with
  | h n ih =>
    have he : (∑ r ∈ Finset.Iio j, a r)=∑ r ∈ Finset.Iio j, b r := by
      apply Finset.sum_congr rfl
      intro r hr
      exact ih r.val (by have := Finset.mem_Iio.mp hr; omega) r rfl
    have ha := h j
    have hjnot : j ∉ Finset.Iio j := by simp
    rw [← Finset.Iio_insert j] at ha
    rw [Finset.sum_insert hjnot,Finset.sum_insert hjnot,he] at ha
    omega

/-- Splitting all block coordinates into selected labels and literal gaps. -/
theorem BlockGapPartition.total_sum {ell m : ℕ} (P : BlockGapPartition ell m)
    (v : Fin m → ℕ) :
    (∑ i, v i)=(∑ j, v (P.selected j))+∑ r, ∑ i, v (P.labels.symm (.inr ⟨r,i⟩)) := by
  have he := Fintype.sum_equiv P.labels v (fun w => v (P.labels.symm w)) (fun i => by simp)
  rw [he,Fintype.sum_sum_type,Fintype.sum_sigma]
  simp_rw [P.selected_label]

/-- Prescribing the selected lengths and their segment starts is exactly
prescribing the selected lengths and all gap totals. This includes empty
gaps and zero unselected-letter totals. -/
theorem BlockGapPartition.event_iff_starts {ell m : ℕ} (P : BlockGapPartition ell m)
    (k : Fin ell → ℕ) (a : Fin (ell+1) → ℕ) (v : Fin m → ℕ)
    (htotal : ∑ i, v i=(∑ j, k j)+∑ r, a r) :
    groupedOccupancyEvent P.gapSize P.labels k a v ↔
      (∀ j, v (P.selected j)=k j) ∧
      ∀ j, (∑ i ∈ (Finset.univ : Finset (Fin m)).filter (fun i => i<P.selected j), v i) =
        (∑ r ∈ Finset.Iio j, k r)+
          ∑ r ∈ (Finset.univ : Finset (Fin (ell+1))).filter (fun r => r.val≤j.val), a r := by
  constructor
  · intro h
    exact ⟨fun j => by rw [← P.selected_label]; exact h.1 j,P.prefix_of_event k a v h⟩
  · rintro ⟨hsel,hstart⟩
    let b := fun r => ∑ i, v (P.labels.symm (.inr ⟨r,i⟩))
    have hselected (S : Finset (Fin ell)) : (∑ j ∈ S, v (P.selected j))=∑ j ∈ S, k j :=
      Finset.sum_congr rfl (fun j _ => hsel j)
    have hsum : ∑ r, b r=∑ r, a r := by
      have he := P.total_sum v
      rw [hselected] at he
      change (∑ i, v i)=(∑ j, k j)+∑ r, b r at he
      omega
    have hpref (j : Fin ell) :
        (∑ r ∈ (Finset.univ : Finset (Fin (ell+1))).filter (fun r => r.val≤j.val), b r) =
          ∑ r ∈ (Finset.univ : Finset (Fin (ell+1))).filter (fun r => r.val≤j.val), a r := by
      have he := P.prefix_sum v j
      rw [hselected] at he
      have hh := hstart j
      change (∑ i ∈ (Finset.univ : Finset (Fin m)).filter (fun i => i<P.selected j), v i) =
        (∑ r ∈ Finset.Iio j, k r)+
          ∑ r ∈ (Finset.univ : Finset (Fin (ell+1))).filter (fun r => r.val≤j.val), b r at he
      exact Nat.add_left_cancel (he.symm.trans hh)
    have hba : b=a := by
      apply fin_prefix_sums_injective
      intro r
      by_cases hr : r.val<ell
      · let j : Fin ell := ⟨r.val,hr⟩
        have hfilter : (Finset.univ : Finset (Fin (ell+1))).filter (fun u => u.val≤j.val)=Finset.Iic r := by
          ext u
          simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_Iic,Fin.le_iff_val_le_val]
          rfl
        simpa only [hfilter] using hpref j
      · have hIic : Finset.Iic r=(Finset.univ : Finset (Fin (ell+1))) := by
          ext u
          simp only [Finset.mem_Iic,Finset.mem_univ,iff_true,Fin.le_iff_val_le_val]
          omega
        simpa only [hIic] using hsum
    refine ⟨fun j => by rw [P.selected_label]; exact hsel j,?_⟩
    intro r
    exact congrFun hba r

/-- Gap sizes recover the literal selected block positions by prefix counts. -/
theorem BlockGapPartition.selected_position {ell m : ℕ} (P : BlockGapPartition ell m)
    (j : Fin ell) :
    (P.selected j).val=j.val+
      ∑ r ∈ (Finset.univ : Finset (Fin (ell+1))).filter (fun r => r.val≤j.val), P.gapSize r := by
  have he := P.prefix_sum (fun _ => 1) j
  have hleft : (Finset.univ : Finset (Fin m)).filter (fun i => i<P.selected j)=Finset.Iio (P.selected j) := by
    ext i
    simp
  simp only [hleft,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    nsmul_eq_mul,mul_one,Fin.card_Iio] at he
  exact he

/-- Two actual selected block sets with the same gap sizes coincide. -/
theorem BlockGapPartition.selected_eq_of_gaps {ell m : ℕ} (P Q : BlockGapPartition ell m)
    (h : P.gapSize=Q.gapSize) : P.selected=Q.selected := by
  ext j
  rw [P.selected_position,Q.selected_position,h]

/-- Ordered gap counts attached to the literal selected block set. -/
noncomputable def blockSelectionGaps {ell m : ℕ} (I : {I : Finset (Fin m) // I.card=ell}) :
    Fin (ell+1) → ℕ := (blockGapPartition (I.val.orderEmbOfFin I.property)).gapSize

theorem blockSelectionGaps_sum {ell m : ℕ} (I : {I : Finset (Fin m) // I.card=ell}) :
    ∑ r, blockSelectionGaps I r=m-ell := (blockGapPartition _).gap_sum

theorem blockSelectionGaps_injective {ell m : ℕ} :
    Function.Injective (blockSelectionGaps (ell := ell) (m := m)) := by
  intro I J h
  have hselected := BlockGapPartition.selected_eq_of_gaps
    (blockGapPartition (I.val.orderEmbOfFin I.property))
    (blockGapPartition (J.val.orderEmbOfFin J.property)) h
  change I.val.orderEmbOfFin I.property=J.val.orderEmbOfFin J.property at hselected
  apply Subtype.ext
  have he := congrArg (fun t : Fin ell ↪o Fin m => Finset.univ.image t) hselected
  simpa only [Finset.image_orderEmbOfFin_univ] using he

/-- Literal selected block sets embed in the gap-composition lattice used
by the collision bound. Injectivity suffices for its nonnegative sum. -/
noncomputable def blockSelectionGapEmbedding {ell m : ℕ} :
    {I : Finset (Fin m) // I.card=ell} ↪
      {g : Fin (ell+1) → ℕ // g ∈ Finset.piAntidiag Finset.univ (m-ell)} := {
  toFun := fun I => ⟨blockSelectionGaps I,
    Finset.mem_piAntidiag.mpr ⟨blockSelectionGaps_sum I,by simp⟩⟩
  inj' := fun I J h => blockSelectionGaps_injective (congrArg Subtype.val h) }

end FairDice
