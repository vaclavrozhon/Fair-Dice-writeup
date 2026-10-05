import FairDice.MultinomialCollision

namespace FairDice

/-- Summing the reciprocal factorial weights over one gap of unspecified
blocks. This includes the empty-gap case, with the usual `0^0=1`. -/
theorem gap_reciprocal_factorials (g a : ℕ) :
    (∑ b ∈ Finset.piAntidiag (Finset.univ : Finset (Fin g)) a,
      1/(∏ i, (b i).factorial : ℝ)) = (g : ℝ)^a/a.factorial := by
  have hf : (a.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero a
  have hm := Finset.sum_pow_eq_sum_piAntidiag (Finset.univ : Finset (Fin g))
    (fun _ => (1 : ℝ)) a
  simp only [Finset.sum_const,Fintype.card_fin,Finset.card_univ,nsmul_eq_mul,mul_one,
    one_pow,Finset.prod_const_one] at hm
  have he (b : Fin g → ℕ) (hb : b ∈ Finset.piAntidiag Finset.univ a) :
      (Nat.multinomial Finset.univ b : ℝ) = (a.factorial : ℝ)/(∏ i, (b i).factorial : ℝ) := by
    simpa [multinomialMass] using multinomialMass_factorial a (fun _ : Fin g => (1 : ℝ)) b
      (Finset.mem_piAntidiag.mp hb).1
  rw [Finset.sum_congr rfl he] at hm
  apply (eq_div_iff hf).mpr
  rw [Finset.sum_mul, hm]
  apply Finset.sum_congr rfl
  intro b hb
  ring

/-- Literal marginal summation of the uniform occupancy weights over all
unselected blocks, grouped into ordered gaps. No collision estimate enters
this definition. `s+d` is the number of letters and `k` the selected lengths. -/
noncomputable def selectedGapMass {ℓ : ℕ} (m s d : ℕ) (k : Fin ℓ → ℕ)
    (g a : Fin (ℓ+1) → ℕ) : ℝ :=
  ((s+d).factorial : ℝ)/((m : ℝ)^(s+d)*(∏ j, (k j).factorial : ℝ)) *
    ∏ j, (∑ b ∈ Finset.piAntidiag (Finset.univ : Finset (Fin (g j))) (a j),
      1/(∏ i, (b i).factorial : ℝ))

/-- The closed coefficient in `eq:palindrome-coefficient`, derived from
summing all unspecified occupancies. Identification of gap selections with
the cut-expansion indices is a separate combinatorial step. -/
theorem selected_gap_mass_formula {ℓ : ℕ} (m s d M : ℕ) (k : Fin ℓ → ℕ)
    (g a : Fin (ℓ+1) → ℕ) (hm : 0 < m) (hM : 0 < M) (ha : ∑ j, a j=d) :
    selectedGapMass m s d k g a =
      ((s+d).descFactorial s : ℝ)/((m : ℝ)^s*(∏ j, (k j).factorial : ℝ)) *
        ((M : ℝ)/m)^d * multinomialMass d (fun j => (g j : ℝ)/M) a := by
  have hmr : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hM
  have hd : (d.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero d
  have hk : (∏ j, (k j).factorial : ℝ) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => by exact_mod_cast Nat.factorial_ne_zero (k j))
  have haF : (∏ j, (a j).factorial : ℝ) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => by exact_mod_cast Nat.factorial_ne_zero (a j))
  have hfac : ((s+d).factorial : ℝ)=(d.factorial : ℝ)*((s+d).descFactorial s : ℝ) := by
    have hh := Nat.factorial_mul_descFactorial (by omega : s ≤ s+d)
    simp only [Nat.add_sub_cancel_left] at hh
    exact_mod_cast hh.symm
  have hprod : (∏ j, ((g j : ℝ)/M)^a j) = (∏ j, (g j : ℝ)^a j)/(M : ℝ)^d := by
    simp only [div_pow,Finset.prod_div_distrib,Finset.prod_pow_eq_pow_sum,ha]
  simp only [selectedGapMass,gap_reciprocal_factorials,Finset.prod_div_distrib]
  rw [multinomialMass_factorial d _ a ha,hprod,hfac,pow_add,div_pow]
  field_simp

end FairDice
