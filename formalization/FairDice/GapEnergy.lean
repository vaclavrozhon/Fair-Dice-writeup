import FairDice.GapCoefficients
import FairDice.SelectedColorEnergy

open scoped Classical

namespace FairDice

/-- The literal retention weight written using the segment length. -/
theorem segmentRetentionWeight_length {n : ℕ} (v : ConsecutiveSegment n) :
    segmentRetentionWeight v=(1/(2 : ℝ)^(segmentLength v-2))/segmentLength v := by
  have he : segmentLength v-2=(segmentSizeIndex v).val+1 := by
    unfold segmentLength segmentSizeIndex
    omega
  rw [he]
  rfl

theorem gapSegments_injective {ell m : ℕ} (s d : ℕ) (P : BlockGapPartition ell m)
    (k : Fin ell → ℕ) (a : Fin (ell+1) → ℕ)
    (hs : ∑ j, k j=s) (ha : ∑ r, a r=d) (hk : ∀ j, 3 ≤ k j) :
    Function.Injective (gapSegments s d P k a hs ha hk) := by
  intro i j h
  exact P.selected.injective (congrArg Sigma.fst h)

/-- The energy of one actual segment monomial is the literal selected-gap
mass squared times the manuscript's inverse-retention error factors. -/
theorem gap_coefficient_energy {ell m : ℕ} (s d : ℕ)
    (σ : Equiv.Perm (Fin (s+d))) (P : BlockGapPartition ell m)
    (k : Fin ell → ℕ) (a : Fin (ell+1) → ℕ)
    (hs : ∑ j, k j=s) (ha : ∑ r, a r=d) (hk : ∀ j, 3 ≤ k j) :
    let K := Finset.univ.image (gapSegments s d P k a hs ha hk)
    (palindromeSegmentCoefficient σ ell K)^2 *
      (∏ v ∈ K, (segmentErrorBound v)^2/segmentRetentionWeight v.2) =
        (selectedGapMass m s d k P.gapSize a)^2 *
          ∏ j, (((k j).factorial : ℝ)*2/(2 : ℝ)^k j)^2 /
            ((1/(2 : ℝ)^(k j-2))/(k j : ℝ)) := by
  dsimp only
  rw [palindrome_gap_data_coefficient,Finset.prod_image
    (gapSegments_injective s d P k a hs ha hk).injOn]
  congr 1
  apply Finset.prod_congr rfl
  intro j _
  rw [segmentRetentionWeight_length]
  have hlen : segmentLength (gapSegments s d P k a hs ha hk j).2=k j := by
    simp [gapSegments]
  simp only [segmentErrorBound,hlen]

/-- The exact squared sum of actual cut coefficients for a fixed selected
block set and length vector. This is the collision-probability reduction
used by the short- and long-support estimates. -/
theorem actual_gap_colored_squared_sum {ell m : ℕ} (s d : ℕ)
    (σ : Equiv.Perm (Fin (s+d))) (P : BlockGapPartition ell m)
    (k : Fin ell → ℕ) (hs : ∑ j, k j=s) (hk : ∀ j, 3 ≤ k j)
    (hm : 0 < m) (hM : 0 < m-ell) :
    (∑ a : {a : Fin (ell+1) → ℕ // a ∈ Finset.piAntidiag Finset.univ d},
      let K := Finset.univ.image (gapSegments s d P k a.val hs
        (Finset.mem_piAntidiag.mp a.property).1 hk)
      (palindromeSegmentCoefficient σ ell K)^2 *
        (∏ v ∈ K, (segmentErrorBound v)^2/segmentRetentionWeight v.2)) =
      (((s+d).descFactorial s : ℝ)/(m : ℝ)^s)^2 *
        (((m-ell : ℕ) : ℝ)/m)^(2*d) * (∏ j, (k j : ℝ)/(2 : ℝ)^k j) *
          multinomialCollision d (fun j => (P.gapSize j : ℝ)/(m-ell : ℕ)) := by
  simp_rw [gap_coefficient_energy]
  rw [Finset.sum_coe_sort (Finset.piAntidiag (Finset.univ : Finset (Fin (ell+1))) d)
    (fun a : Fin (ell+1) → ℕ => (selectedGapMass m s d k P.gapSize a)^2 *
      ∏ j, (((k j).factorial : ℝ)*2/(2 : ℝ)^k j)^2 /
        ((1/(2 : ℝ)^(k j-2))/(k j : ℝ)))]
  exact selected_gap_colored_squared_sum m s d (m-ell) k P.gapSize hm hM
    (fun j => (hk j).trans' (by norm_num))

end FairDice
