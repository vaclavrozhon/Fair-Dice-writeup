import FairDice.BlockGaps
import FairDice.SegmentOccupancy

open scoped Classical

namespace FairDice

/-- The canonical cumulative starting position for a selected segment. -/
def selectedGapStart {ell : ℕ} (k : Fin ell → ℕ) (a : Fin (ell+1) → ℕ) (j : Fin ell) : ℕ :=
  (∑ r ∈ Finset.Iio j, k r) +
    ∑ r ∈ (Finset.univ : Finset (Fin (ell+1))).filter (fun r => r.val≤j.val), a r

/-- Equality of the actual selected-segment event with the event obtained by
fixing the lengths of selected blocks and letter totals of unselected gaps. -/
theorem occupancySegmentEvent_iff_gaps {n ell m : ℕ} (σ : Equiv.Perm (Fin n))
    (P : BlockGapPartition ell m) (k : Fin ell → ℕ) (a : Fin (ell+1) → ℕ)
    (e : Fin ell → BlockSegment (Fin m) n)
    (hblock : ∀ j, (e j).1=P.selected j)
    (hstart : ∀ j, segmentStart (e j).2=selectedGapStart k a j)
    (hlen : ∀ j, segmentLength (e j).2=k j) (hk : ∀ j, 3 ≤ k j)
    (hn : n=(∑ j, k j)+∑ r, a r)
    (v : {v : Fin m → ℕ // v ∈ Finset.piAntidiag Finset.univ n}) :
    occupancySegmentEvent σ (Finset.univ.image P.selected) (Finset.univ.image e) v ↔
      groupedOccupancyEvent P.gapSize P.labels k a v.val := by
  classical
  let jcut := (cutOccupancyEquiv σ).symm v
  have hv : cutOccupancy σ jcut=v.val := congrArg Subtype.val ((cutOccupancyEquiv σ).apply_symm_apply v)
  have htotal : ∑ i, v.val i=(∑ j, k j)+∑ r, a r :=
    (Finset.mem_piAntidiag.mp v.property).1.trans hn
  rw [P.event_iff_starts k a v.val htotal]
  constructor
  · rintro ⟨h,hgraph⟩
    have hmem (j : Fin ell) : e j ∈ cutGraphAt σ (Finset.univ.image P.selected) jcut h := by
      rw [hgraph]
      exact Finset.mem_image.mpr ⟨j,Finset.mem_univ j,rfl⟩
    have hdata (j : Fin ell) := (cutGraph_mem_iff (cutAt σ jcut) (cutAt_length σ jcut)
      (by rw [cutAt_flatten]; simp) (Finset.univ.image P.selected) h (e j)).mp (hmem j)
    refine ⟨?_,?_⟩
    · intro j
      have he := (hdata j).2.2
      rw [hblock,hlen] at he
      change k j=cutOccupancy σ jcut (P.selected j) at he
      rw [hv] at he
      exact he.symm
    · intro j
      have he := (hdata j).2.1
      rw [hblock,hstart,cutStart_occupancy,hv] at he
      exact he.symm
  · rintro ⟨hselected,hstarts⟩
    have hlong : ∀ i ∈ Finset.univ.image P.selected,
        3 ≤ ((cutAt σ jcut)[i.val]?.getD []).length := by
      intro i hi
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hi
      change 3 ≤ cutOccupancy σ jcut (P.selected j)
      rw [hv,hselected]
      exact hk j
    refine ⟨hlong,?_⟩
    ext w
    rw [cutGraphAt,cutGraph_mem_iff]
    constructor
    · rintro ⟨hw,ha,hl⟩
      obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hw
      have hwe : w=e j := by
        cases w with
        | mk b t =>
          have hb : b=(e j).1 := hj.symm.trans (hblock j).symm
          have ht : t=(e j).2 := by
            apply segment_eq_of_start_length
            · rw [ha,← hj,cutStart_occupancy,hv,hstarts,hstart]
              rfl
            · rw [hl,← hj]
              change cutOccupancy σ jcut (P.selected j)=segmentLength (e j).2
              rw [hv,hselected,hlen]
          exact Sigma.ext hb (heq_of_eq ht)
      exact Finset.mem_image.mpr ⟨j,Finset.mem_univ j,hwe.symm⟩
    · intro hw
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hw
      refine ⟨Finset.mem_image.mpr ⟨j,Finset.mem_univ j,(hblock j).symm⟩,?_,?_⟩
      · rw [hblock,cutStart_occupancy,hv,hstarts,hstart]
        rfl
      · rw [hblock,hlen]
        change k j=cutOccupancy σ jcut (P.selected j)
        rw [hv,hselected]

/-- The article's selected-block coefficient formula for the concrete cut
coefficients, including zero gap sizes and zero remaining-letter counts.
The selected monomial is specified by its block labels, lengths and starts;
all its weights are derived from the actual word model. -/
theorem palindrome_selected_gap_coefficient {ell m : ℕ} (s d : ℕ)
    (σ : Equiv.Perm (Fin (s+d))) (P : BlockGapPartition ell m)
    (k : Fin ell → ℕ) (a : Fin (ell+1) → ℕ)
    (e : Fin ell → BlockSegment (Fin m) (s+d))
    (hblock : ∀ j, (e j).1=P.selected j)
    (hstart : ∀ j, segmentStart (e j).2=selectedGapStart k a j)
    (hlen : ∀ j, segmentLength (e j).2=k j) (hk : ∀ j, 3 ≤ k j)
    (hs : ∑ j, k j=s) (ha : ∑ r, a r=d) :
    palindromeSegmentCoefficient σ ell (Finset.univ.image e)=
      selectedGapMass m s d k P.gapSize a := by
  classical
  have hblocks : (Finset.univ.image e).image (fun v => v.1)=Finset.univ.image P.selected := by
    rw [Finset.image_image]
    apply Finset.image_congr
    intro j _
    exact hblock j
  have hcard : (Finset.univ.image P.selected).card=ell := by
    rw [Finset.card_image_of_injective _ P.selected.injective]
    simp
  rw [palindromeSegmentCoefficient_multinomial,hblocks,hcard,if_pos rfl]
  have hn : s+d=(∑ j, k j)+∑ r, a r := by rw [hs,ha]
  simp_rw [occupancySegmentEvent_iff_gaps σ P k a e hblock hstart hlen hk hn]
  exact grouped_multinomial_marginal s d P.gapSize a P.labels k hs ha

/-- `eq:palindrome-coefficient`: the coefficient of the actual selected
segment monomial, in its closed falling-factorial and multinomial form. -/
theorem palindrome_selected_gap_formula {ell m : ℕ} (s d : ℕ)
    (σ : Equiv.Perm (Fin (s+d))) (P : BlockGapPartition ell m)
    (k : Fin ell → ℕ) (a : Fin (ell+1) → ℕ)
    (e : Fin ell → BlockSegment (Fin m) (s+d))
    (hblock : ∀ j, (e j).1=P.selected j)
    (hstart : ∀ j, segmentStart (e j).2=selectedGapStart k a j)
    (hlen : ∀ j, segmentLength (e j).2=k j) (hk : ∀ j, 3 ≤ k j)
    (hs : ∑ j, k j=s) (ha : ∑ r, a r=d) (hm : 0 < m) (hM : 0 < m-ell) :
    palindromeSegmentCoefficient σ ell (Finset.univ.image e)=
      ((s+d).descFactorial s : ℝ)/((m : ℝ)^s*(∏ j, ((k j).factorial : ℝ))) *
        (((m-ell : ℕ) : ℝ)/m)^d * multinomialMass d (fun j => (P.gapSize j : ℝ)/(m-ell : ℕ)) a := by
  rw [palindrome_selected_gap_coefficient s d σ P k a e hblock hstart hlen hk hs ha]
  exact selected_gap_mass_formula m s d (m-ell) k P.gapSize a hm hM ha

/-- The gap-count starting position lies inside the target pattern. -/
theorem selectedGapStart_fits {ell : ℕ} (k : Fin ell → ℕ) (a : Fin (ell+1) → ℕ)
    (j : Fin ell) : selectedGapStart k a j+k j ≤ (∑ r, k r)+∑ r, a r := by
  have hselected : (∑ r ∈ Finset.Iic j, k r) ≤ ∑ r, k r :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)
  have hgap : (∑ r ∈ (Finset.univ : Finset (Fin (ell+1))).filter (fun r => r.val≤j.val), a r) ≤
      ∑ r, a r :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun _ _ _ => Nat.zero_le _)
  rw [← Finset.Iio_insert j,Finset.sum_insert (by simp)] at hselected
  unfold selectedGapStart
  omega

/-- Construct the actual segment from its start and length. -/
def segmentOfStart (n start len : ℕ) (hfit : start+len ≤ n) (hk : 3 ≤ len) : ConsecutiveSegment n := by
  refine ⟨(⟨start,by omega⟩,⟨len-3,by omega⟩),?_⟩
  dsimp
  omega

@[simp] theorem segmentOfStart_start (n start len : ℕ) (hfit : start+len ≤ n) (hk : 3 ≤ len) :
    segmentStart (segmentOfStart n start len hfit hk)=start := rfl

@[simp] theorem segmentOfStart_length (n start len : ℕ) (hfit : start+len ≤ n) (hk : 3 ≤ len) :
    segmentLength (segmentOfStart n start len hfit hk)=len := by
  change len-3+3=len
  omega

/-- Literal selected segments for every admissible length vector and gap
letter-count vector. The needed endpoint inequalities are derived. -/
def gapSegments {ell m : ℕ} (s d : ℕ) (P : BlockGapPartition ell m)
    (k : Fin ell → ℕ) (a : Fin (ell+1) → ℕ)
    (hs : ∑ j, k j=s) (ha : ∑ r, a r=d) (hk : ∀ j, 3 ≤ k j) :
    Fin ell → BlockSegment (Fin m) (s+d) := fun j =>
  ⟨P.selected j,segmentOfStart (s+d) (selectedGapStart k a j) (k j)
    (by have h := selectedGapStart_fits k a j; rwa [hs,ha] at h) (hk j)⟩

/-- Every admissible selected-gap index produces its actual concrete
segment coefficient; no segment-existence premise remains. -/
theorem palindrome_gap_data_coefficient {ell m : ℕ} (s d : ℕ)
    (σ : Equiv.Perm (Fin (s+d))) (P : BlockGapPartition ell m)
    (k : Fin ell → ℕ) (a : Fin (ell+1) → ℕ)
    (hs : ∑ j, k j=s) (ha : ∑ r, a r=d) (hk : ∀ j, 3 ≤ k j) :
    palindromeSegmentCoefficient σ ell (Finset.univ.image (gapSegments s d P k a hs ha hk))=
      selectedGapMass m s d k P.gapSize a := by
  apply palindrome_selected_gap_coefficient s d σ P k a _
  · intro j; rfl
  · intro j; simp [gapSegments]
  · intro j; simp [gapSegments]
  · exact hk
  · exact hs
  · exact ha

end FairDice
