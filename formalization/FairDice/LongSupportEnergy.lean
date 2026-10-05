import FairDice.SupportEnergy

open scoped Classical

namespace FairDice

theorem tilted_length_product {ell : ℕ} (k : Fin ell → ℕ) (θ z : ℝ) :
    (∏ j, (k j : ℝ)*(θ*z)^k j) =
      θ^(∑ j, k j)*(∏ j, (k j : ℝ)*z^k j) := by
  simp only [mul_pow,Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]
  ring

/-- Exponential tilting of the complete long-support energy. The support
restriction is removed only after its quantitative weight is inserted. -/
theorem palindrome_long_energy {n m : ℕ} (σ : Equiv.Perm (Fin n)) (ell : ℕ)
    (hm : 0 < m) (hnm : n ≤ m) (θ : ℝ) (hθ : 1 ≤ θ)
    (hz : θ*(n : ℝ)^2/(2*(m : ℝ)^2) ≤ 1/2) :
    (∑ K : Finset (BlockSegment (Fin m) n),
      if n < 2*segmentSupportSize K then segmentCoefficientEnergy σ ell K else 0) ≤
      θ^(-(n : ℝ)/2) *
        (8*m*(θ*(n : ℝ)^2/(2*(m : ℝ)^2))^3)^ell/(ell.factorial : ℝ) := by
  let z : ℝ := (n : ℝ)^2/(2*(m : ℝ)^2)
  let f : (Fin ell → Fin (n-2)) → ℝ := fun k =>
    ∏ j, (((k j).val+3 : ℕ) : ℝ)*(θ*z)^((k j).val+3)
  have hθ0 : 0 < θ := lt_of_lt_of_le (by norm_num) hθ
  have hf (k) : 0 ≤ f k := by dsimp [f,z]; positivity
  have htilt (k : AdmissibleLengths ell n) (hlong : n < 2*selectedLengthSum k) :
      (∏ j, (selectedLengths k j : ℝ)*z^(selectedLengths k j)) ≤
        θ^(-(n : ℝ)/2)*f k.val := by
    have hns : (n : ℝ)/2 ≤ selectedLengthSum k := by
      have hh : (n : ℝ) ≤ 2*(selectedLengthSum k : ℝ) := by
        exact_mod_cast (by omega : n ≤ 2*selectedLengthSum k)
      linarith
    have hmono := Real.rpow_le_rpow_of_exponent_le hθ hns
    rw [Real.rpow_natCast] at hmono
    have hinv : θ^(-(n : ℝ)/2)*θ^(selectedLengthSum k) ≥ 1 := by
      have hh := mul_le_mul_of_nonneg_left hmono (Real.rpow_nonneg hθ0.le (-(n : ℝ)/2))
      rw [← Real.rpow_add hθ0,show -(n : ℝ)/2+(n : ℝ)/2=0 by ring,Real.rpow_zero] at hh
      exact hh
    change _ ≤ θ^(-(n : ℝ)/2)*∏ j, (selectedLengths k j : ℝ)*(θ*z)^selectedLengths k j
    rw [tilted_length_product,← mul_assoc]
    exact le_mul_of_one_le_left (by positivity) hinv
  have he : (∑ K : Finset (BlockSegment (Fin m) n),
      if n < 2*segmentSupportSize K then segmentCoefficientEnergy σ ell K else 0) ≤
      ∑ k : AdmissibleLengths ell n,
        if n < 2*selectedLengthSum k then
          fixedLengthEnergy (m := m) σ (selectedLengths k) k.property
            (fun j => by dsimp [selectedLengths]; omega) else 0 := by
    convert palindrome_restricted_energy σ ell (fun s => n < 2*s) using 1 <;>
      apply Finset.sum_congr rfl <;> intro k _ <;> split_ifs <;> rfl
  calc
    _ ≤ _ := he
    _ ≤ ∑ k : AdmissibleLengths ell n,
        ((m : ℝ)^ell/(ell.factorial : ℝ))*(θ^(-(n : ℝ)/2)*f k.val) := by
      apply Finset.sum_le_sum
      intro k _
      split_ifs with hlong
      · exact (fixedLengthEnergy_global σ (selectedLengths k) k.property _ hm hnm).trans
          (mul_le_mul_of_nonneg_left (htilt k hlong) (by positivity))
      · positivity
    _ = (((m : ℝ)^ell/(ell.factorial : ℝ))*θ^(-(n : ℝ)/2))*
        ∑ k : AdmissibleLengths ell n, f k.val := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; ring
    _ ≤ (((m : ℝ)^ell/(ell.factorial : ℝ))*θ^(-(n : ℝ)/2))*
        ∑ k : Fin ell → Fin (n-2), f k :=
      mul_le_mul_of_nonneg_left (admissible_length_sum_le f hf) (by positivity)
    _ ≤ (((m : ℝ)^ell/(ell.factorial : ℝ))*θ^(-(n : ℝ)/2))*(8*(θ*z)^3)^ell := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      have hp := Fintype.prod_sum (ι := Fin ell) (κ := fun _ => Fin (n-2))
        (fun (_ : Fin ell) (j : Fin (n-2)) => ((j.val+3 : ℕ) : ℝ)*(θ*z)^(j.val+3))
      change (∑ k : Fin ell → Fin (n-2), ∏ j, (((k j).val+3 : ℕ) : ℝ)*(θ*z)^((k j).val+3)) ≤ _
      rw [← hp]
      simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin]
      apply pow_le_pow_left₀ (by positivity)
      apply palindrome_finite_length_series _ _ (by dsimp [z]; positivity)
      simpa [z,mul_div_assoc] using hz
    _ = _ := by dsimp [z]; simp only [mul_div_assoc,mul_pow]; ring

end FairDice
