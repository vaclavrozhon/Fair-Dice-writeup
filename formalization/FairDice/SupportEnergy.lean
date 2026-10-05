import FairDice.SegmentParameters
import FairDice.LengthEnergy

open scoped Classical

namespace FairDice

def segmentSupportSize {n m : ℕ} (K : Finset (BlockSegment (Fin m) n)) : ℕ :=
  ∑ v ∈ K, segmentLength v.2

theorem parameterSegments_support {ell m n : ℕ} (u : SegmentParameters ell m n) :
    segmentSupportSize (parameterSegments u)=selectedLengthSum u.1 := by
  classical
  unfold segmentSupportSize parameterSegments
  dsimp only
  rw [Finset.sum_image]
  · simp only [segmentOfStart_length]
    rfl
  · intro i _ j _ hij
    exact (u.2.1.val.orderEmbOfFin u.2.1.property).injective (congrArg Sigma.fst hij)

theorem parameter_length_energy {ell m n : ℕ} (σ : Equiv.Perm (Fin n))
    (k : AdmissibleLengths ell n) :
    (∑ Ia : BlockSelection ell m ×
        {a : Fin (ell+1) → ℕ // a ∈ Finset.piAntidiag Finset.univ (n-selectedLengthSum k)},
      segmentCoefficientEnergy σ ell (parameterSegments ⟨k,Ia⟩)) =
      fixedLengthEnergy (m := m) σ (selectedLengths k) k.property
        (fun j => by dsimp [selectedLengths]; omega) := by
  rw [Fintype.sum_prod_type]
  rfl

/-- The energy for any restriction on total selected support is bounded
by the corresponding admissible length sum. -/
theorem palindrome_restricted_energy {n m : ℕ} (σ : Equiv.Perm (Fin n))
    (ell : ℕ) (D : ℕ → Prop) :
    (∑ K : Finset (BlockSegment (Fin m) n),
      if D (segmentSupportSize K) then segmentCoefficientEnergy σ ell K else 0) ≤
      ∑ k : AdmissibleLengths ell n,
        if D (selectedLengthSum k) then
          fixedLengthEnergy (m := m) σ (selectedLengths k) k.property
            (fun j => by dsimp [selectedLengths]; omega) else 0 := by
  have he := finite_sum_le_of_support_covered (parameterSegments (ell := ell) (m := m) (n := n))
    (fun K => if D (segmentSupportSize K) then segmentCoefficientEnergy σ ell K else 0)
    (fun K => by split_ifs; exact segmentCoefficientEnergy_nonneg σ ell K; exact le_rfl)
    (by
      intro K hK
      apply palindrome_coefficient_parameter σ K
      intro hc
      apply hK
      simp [segmentCoefficientEnergy,hc])
  simp_rw [parameterSegments_support] at he
  rw [Fintype.sum_sigma] at he
  convert he using 1
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : D (selectedLengthSum k)
  · simp only [hk,ite_true]
    exact (parameter_length_energy σ k).symm
  · simp [hk]

/-- Extending the admissible lengths to all independent finite choices. -/
theorem admissible_length_sum_le {ell n : ℕ} (f : (Fin ell → Fin (n-2)) → ℝ)
    (hf : ∀ k, 0 ≤ f k) :
    (∑ k : AdmissibleLengths ell n, f k.val) ≤ ∑ k : Fin ell → Fin (n-2), f k :=
  finite_sum_embedding_le ⟨Subtype.val,Subtype.val_injective⟩ f hf

/-- Complete short-support square-energy estimate for the actual word. -/
theorem palindrome_short_energy {n m : ℕ} (H : PoissonEstimates)
    (σ : Equiv.Perm (Fin n)) (ell : ℕ) (hell : 1 ≤ ell)
    (hm : 0 < m) (hnm : n ≤ m) :
    (∑ K : Finset (BlockSegment (Fin m) n),
      if 2*segmentSupportSize K ≤ n then segmentCoefficientEnergy σ ell K else 0) ≤
      ((160*m/Real.sqrt (n : ℝ))*((n : ℝ)^6/(m : ℝ)^6))^ell := by
  let f : (Fin ell → Fin (n-2)) → ℝ := fun k =>
    ∏ j, (((k j).val+3 : ℕ) : ℝ)*((n : ℝ)^2/(2*(m : ℝ)^2))^((k j).val+3)
  have hf (k) : 0 ≤ f k := by dsimp [f]; positivity
  have he : (∑ K : Finset (BlockSegment (Fin m) n),
      if 2*segmentSupportSize K ≤ n then segmentCoefficientEnergy σ ell K else 0) ≤
      ∑ k : AdmissibleLengths ell n,
        if 2*selectedLengthSum k ≤ n then
          fixedLengthEnergy (m := m) σ (selectedLengths k) k.property
            (fun j => by dsimp [selectedLengths]; omega) else 0 := by
    convert palindrome_restricted_energy σ ell (fun s => 2*s ≤ n) using 1 <;>
      apply Finset.sum_congr rfl <;> intro k _ <;> split_ifs <;> rfl
  calc
    _ ≤ _ := he
    _ ≤ ∑ k : AdmissibleLengths ell n, (160*m/Real.sqrt (n : ℝ))^ell*f k.val := by
      apply Finset.sum_le_sum
      intro k _
      split_ifs with hshort
      · exact fixedLengthEnergy_short H σ (selectedLengths k) k.property _ hell hshort hnm
      · exact mul_nonneg (by positivity) (hf k.val)
    _ = (160*m/Real.sqrt (n : ℝ))^ell*∑ k : AdmissibleLengths ell n, f k.val :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (160*m/Real.sqrt (n : ℝ))^ell*∑ k : Fin ell → Fin (n-2), f k :=
      mul_le_mul_of_nonneg_left (admissible_length_sum_le f hf) (by positivity)
    _ ≤ (160*m/Real.sqrt (n : ℝ))^ell*((n : ℝ)^6/(m : ℝ)^6)^ell :=
      mul_le_mul_of_nonneg_left (palindrome_length_vector_bound ell (n-2) n m hm hnm) (by positivity)
    _ = _ := (mul_pow _ _ _).symm

/-- The simpler complete square-energy bound used for small alphabets. -/
theorem palindrome_global_energy {n m : ℕ} (σ : Equiv.Perm (Fin n)) (ell : ℕ)
    (hm : 0 < m) (hnm : n ≤ m) :
    (∑ K : Finset (BlockSegment (Fin m) n), segmentCoefficientEnergy σ ell K) ≤
      ((n : ℝ)^6/(m : ℝ)^5)^ell/(ell.factorial : ℝ) := by
  let f : (Fin ell → Fin (n-2)) → ℝ := fun k =>
    ∏ j, (((k j).val+3 : ℕ) : ℝ)*((n : ℝ)^2/(2*(m : ℝ)^2))^((k j).val+3)
  have hf (k) : 0 ≤ f k := by dsimp [f]; positivity
  have he := palindrome_restricted_energy (m := m) σ ell (fun _ => True)
  simp only [if_pos (show True from trivial)] at he
  calc
    _ ≤ _ := he
    _ ≤ ∑ k : AdmissibleLengths ell n, ((m : ℝ)^ell/(ell.factorial : ℝ))*f k.val := by
      apply Finset.sum_le_sum
      intro k _
      exact fixedLengthEnergy_global σ (selectedLengths k) k.property _ hm hnm
    _ = ((m : ℝ)^ell/(ell.factorial : ℝ))*∑ k : AdmissibleLengths ell n, f k.val :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ ((m : ℝ)^ell/(ell.factorial : ℝ))*∑ k : Fin ell → Fin (n-2), f k :=
      mul_le_mul_of_nonneg_left (admissible_length_sum_le f hf) (by positivity)
    _ ≤ ((m : ℝ)^ell/(ell.factorial : ℝ))*((n : ℝ)^6/(m : ℝ)^6)^ell :=
      mul_le_mul_of_nonneg_left (palindrome_length_vector_bound ell (n-2) n m hm hnm) (by positivity)
    _ = _ := by
      have hm0 : (m : ℝ)≠0 := by exact_mod_cast (by omega : m≠0)
      rw [div_mul_eq_mul_div,← mul_pow]
      congr 1
      field_simp

end FairDice
