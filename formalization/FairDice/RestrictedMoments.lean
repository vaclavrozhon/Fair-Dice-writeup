import FairDice.LongSupportEnergy

open scoped Classical

namespace FairDice

noncomputable def palindromeRestrictedPart {n m : ℕ} (σ : Equiv.Perm (Fin n))
    (ell : ℕ) (D : ℕ → Prop) (ρ : Fin m → Equiv.Perm (Fin n)) : ℝ :=
  ∑ K : Finset (BlockSegment (Fin m) n),
    (if D (segmentSupportSize K) then palindromeSegmentCoefficient σ ell K else 0)*
      ∏ v ∈ K, segmentError σ v ρ

theorem palindrome_restricted_colored {n m : ℕ} (H : BonamiExternal)
    (σ : Equiv.Perm (Fin n)) (p : ℝ) (hp : 2 ≤ p) (ell : ℕ) (D : ℕ → Prop) :
    finiteLp p (palindromeRestrictedPart (m := m) σ ell D) ≤
      (2*Real.sqrt (p-1))^ell * Real.sqrt
        (∑ K : Finset (BlockSegment (Fin m) n),
          if D (segmentSupportSize K) then segmentCoefficientEnergy σ ell K else 0) := by
  let c := fun K : Finset (BlockSegment (Fin m) n) =>
    if D (segmentSupportSize K) then palindromeSegmentCoefficient σ ell K else 0
  have hc (K) (hK : K.card≠ell) : c K=0 := by
    dsimp [c]; rw [palindromeSegmentCoefficient_card σ ell K hK]; simp
  have hb (K) (hK : c K≠0) : Set.InjOn (fun v : BlockSegment (Fin m) n => v.1) K := by
    apply palindromeSegmentCoefficient_blocks σ ell K
    intro he
    apply hK
    simp [c,he]
  have hh := palindrome_colored (B := Fin m) H σ p hp ell c hc hb
  change finiteLp p (palindromeRestrictedPart σ ell D) ≤ _ at hh
  convert hh using 2
  congr 1
  apply Finset.sum_congr rfl
  intro K _
  dsimp [c,segmentCoefficientEnergy]
  split_ifs <;> simp

theorem palindrome_error_restricted_parts {n m : ℕ} (hm : 0 < m)
    (σ : Equiv.Perm (Fin n)) (ρ : Fin m → Equiv.Perm (Fin n)) :
    palindromeRelativeError ρ σ =
      ∑ ell ∈ Finset.Icc 1 m,
        (palindromeRestrictedPart σ ell (fun s => 2*s ≤ n) ρ +
          palindromeRestrictedPart σ ell (fun s => n < 2*s) ρ) := by
  rw [palindrome_error_by_degree hm]
  apply Finset.sum_congr rfl
  intro ell _
  rw [← palindrome_segment_part_expansion]
  unfold palindromeRestrictedPart
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro K _
  by_cases h : 2*segmentSupportSize K ≤ n
  · simp [h,show ¬n < 2*segmentSupportSize K by omega]
  · simp [h,show n < 2*segmentSupportSize K by omega]

theorem sqrt_nat_power (x : ℝ) (hx : 0 ≤ x) (ell : ℕ) :
    Real.sqrt (x^ell)=(Real.sqrt x)^ell := by
  induction ell with
  | zero => simp
  | succ ell ih => rw [pow_succ,Real.sqrt_mul (pow_nonneg hx ell),ih,pow_succ]

theorem geometric_nonempty_partial (a : ℝ) (ha : 0 ≤ a) (ha1 : a < 1) (m : ℕ) :
    (∑ ell ∈ Finset.Icc 1 m, a^ell) ≤ a/(1-a) := by
  have hs := hasSum_geometric_of_abs_lt_one (r := a) (by rw [abs_of_nonneg ha]; exact ha1)
  have he : (∑ ell ∈ Finset.Icc 1 m, a^ell)+1=∑ ell ∈ Finset.Icc 0 m, a^ell := by
    have hi : Finset.Icc 0 m=insert 0 (Finset.Icc 1 m) := by
      ext j; simp only [Finset.mem_Icc,Finset.mem_insert]; omega
    rw [hi,Finset.sum_insert (by simp)]
    simp [add_comm]
  have hh := hs.summable.sum_le_tsum (Finset.Icc 0 m) (fun ell _ => pow_nonneg ha ell)
  rw [hs.tsum_eq,← he] at hh
  have hcalc : 1/(1-a)-1=a/(1-a) := by
    field_simp [show 1-a≠0 by linarith]; ring
  simp only [one_div] at hcalc ⊢
  linarith

noncomputable def shortChaosScale (n m : ℕ) (p : ℝ) : ℝ :=
  2*Real.sqrt p*Real.sqrt ((160*m/Real.sqrt (n : ℝ))*((n : ℝ)^6/(m : ℝ)^6))

noncomputable def globalChaosScale (n m : ℕ) (p : ℝ) : ℝ :=
  2*Real.sqrt p*Real.sqrt ((n : ℝ)^6/(m : ℝ)^5)

noncomputable def tiltedChaosScale (n m : ℕ) (p θ : ℝ) : ℝ :=
  2*Real.sqrt p*Real.sqrt (8*m*(θ*(n : ℝ)^2/(2*(m : ℝ)^2))^3)

theorem palindrome_short_degree_norm {n m : ℕ} (B : BonamiExternal) (H : PoissonEstimates)
    (σ : Equiv.Perm (Fin n)) (p : ℝ) (hp : 2 ≤ p) (ell : ℕ) (hell : 1 ≤ ell)
    (hm : 0 < m) (hnm : n ≤ m) :
    finiteLp p (palindromeRestrictedPart (m := m) σ ell (fun s => 2*s ≤ n)) ≤
      (shortChaosScale n m p)^ell := by
  have hh := palindrome_restricted_colored (m := m) B σ p hp ell (fun s => 2*s ≤ n)
  have he : Real.sqrt (∑ K : Finset (BlockSegment (Fin m) n),
      @ite ℝ (2*segmentSupportSize K ≤ n) (Classical.propDecidable _)
        (segmentCoefficientEnergy σ ell K) 0) ≤
      Real.sqrt (((160*m/Real.sqrt (n : ℝ))*((n : ℝ)^6/(m : ℝ)^6))^ell) := by
    convert Real.sqrt_le_sqrt (palindrome_short_energy H σ ell hell hm hnm) using 1
    congr 1
    apply Finset.sum_congr rfl
    intro K _
    split_ifs <;> rfl
  have hp' : 2*Real.sqrt (p-1) ≤ 2*Real.sqrt p := by gcongr; linarith
  calc
    _ ≤ _ := hh
    _ ≤ (2*Real.sqrt p)^ell*Real.sqrt
        (((160*m/Real.sqrt (n : ℝ))*((n : ℝ)^6/(m : ℝ)^6))^ell) :=
      mul_le_mul (pow_le_pow_left₀ (by positivity) hp' ell) he (by positivity) (by positivity)
    _ = _ := by rw [sqrt_nat_power _ (by positivity),← mul_pow]; rfl

theorem palindrome_long_degree_norm {n m : ℕ} (B : BonamiExternal)
    (σ : Equiv.Perm (Fin n)) (p : ℝ) (hp : 2 ≤ p) (ell : ℕ)
    (hm : 0 < m) (hnm : n ≤ m) (θ : ℝ) (hθ : 1 ≤ θ)
    (hz : θ*(n : ℝ)^2/(2*(m : ℝ)^2) ≤ 1/2) :
    finiteLp p (palindromeRestrictedPart (m := m) σ ell (fun s => n < 2*s)) ≤
      θ^(-(n : ℝ)/4)*(tiltedChaosScale n m p θ)^ell/Real.sqrt (ell.factorial : ℝ) := by
  have hh := palindrome_restricted_colored (m := m) B σ p hp ell (fun s => n < 2*s)
  have he : Real.sqrt (∑ K : Finset (BlockSegment (Fin m) n),
      @ite ℝ (n < 2*segmentSupportSize K) (Classical.propDecidable _)
        (segmentCoefficientEnergy σ ell K) 0) ≤
      Real.sqrt (θ^(-(n : ℝ)/2)*(8*m*(θ*(n : ℝ)^2/(2*(m : ℝ)^2))^3)^ell/(ell.factorial : ℝ)) := by
    convert Real.sqrt_le_sqrt (palindrome_long_energy σ ell hm hnm θ hθ hz) using 1
    congr 1
    apply Finset.sum_congr rfl
    intro K _
    split_ifs <;> rfl
  have hp' : 2*Real.sqrt (p-1) ≤ 2*Real.sqrt p := by gcongr; linarith
  have hθ0 : 0 < θ := lt_of_lt_of_le (by norm_num) hθ
  have htroot : Real.sqrt (θ^(-(n : ℝ)/2))=θ^(-(n : ℝ)/4) := by
    rw [Real.sqrt_eq_rpow,← Real.rpow_mul hθ0.le]
    congr 1
    ring
  calc
    _ ≤ _ := hh
    _ ≤ (2*Real.sqrt p)^ell*Real.sqrt
        (θ^(-(n : ℝ)/2)*(8*m*(θ*(n : ℝ)^2/(2*(m : ℝ)^2))^3)^ell/(ell.factorial : ℝ)) :=
      mul_le_mul (pow_le_pow_left₀ (by positivity) hp' ell) he (by positivity) (by positivity)
    _ = _ := by
      rw [Real.sqrt_div (by positivity),Real.sqrt_mul (by positivity),
        sqrt_nat_power _ (by positivity),htroot]
      unfold tiltedChaosScale
      rw [mul_pow]
      ring

/-- The complete short/long norm bound, prior to scalar threshold arithmetic. -/
theorem palindrome_short_long_norm {n m : ℕ} (B : BonamiExternal) (H : PoissonEstimates)
    (σ : Equiv.Perm (Fin n)) (p : ℝ) (hp : 2 ≤ p)
    (hm : 0 < m) (hnm : n ≤ m) (ha : shortChaosScale n m p < 1)
    (θ : ℝ) (hθ : 1 ≤ θ) (hz : θ*(n : ℝ)^2/(2*(m : ℝ)^2) ≤ 1/2) :
    finiteLp p (fun ρ : Fin m → Equiv.Perm (Fin n) => palindromeRelativeError ρ σ) ≤
      shortChaosScale n m p/(1-shortChaosScale n m p) +
        Real.sqrt 2*θ^(-(n : ℝ)/4)*Real.exp ((tiltedChaosScale n m p θ)^2) := by
  simp_rw [palindrome_error_restricted_parts hm σ]
  calc
    _ ≤ _ := finiteLp_sum (by linarith : 1 ≤ p) _ _
    _ ≤ ∑ ell ∈ Finset.Icc 1 m,
        ((shortChaosScale n m p)^ell + θ^(-(n : ℝ)/4)*
          (tiltedChaosScale n m p θ)^ell/Real.sqrt (ell.factorial : ℝ)) := by
      apply Finset.sum_le_sum
      intro ell hell
      exact (finiteLp_add (by linarith : 1 ≤ p) _ _).trans (add_le_add
        (palindrome_short_degree_norm B H σ p hp ell (Finset.mem_Icc.mp hell).1 hm hnm)
        (palindrome_long_degree_norm B σ p hp ell hm hnm θ hθ hz))
    _ = (∑ ell ∈ Finset.Icc 1 m, (shortChaosScale n m p)^ell) +
        θ^(-(n : ℝ)/4)*(∑ ell ∈ Finset.Icc 1 m,
          (tiltedChaosScale n m p θ)^ell/Real.sqrt (ell.factorial : ℝ)) := by
      rw [Finset.sum_add_distrib,Finset.mul_sum]
      congr 1; apply Finset.sum_congr rfl; intro ell _; ring
    _ ≤ shortChaosScale n m p/(1-shortChaosScale n m p) +
        θ^(-(n : ℝ)/4)*(Real.sqrt 2*Real.exp ((tiltedChaosScale n m p θ)^2)) := by
      apply add_le_add (geometric_nonempty_partial _ (by unfold shortChaosScale; positivity) ha m)
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      calc
        _ ≤ ∑ ell ∈ Finset.range (m+1),
            (tiltedChaosScale n m p θ)^ell/Real.sqrt (ell.factorial : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (by intro ell he; simp only [Finset.mem_Icc] at he; simp; omega)
            (fun ell _ _ => by unfold tiltedChaosScale; positivity)
        _ ≤ _ := factorial_sqrt_series_partial _ _
    _ = _ := by ring

/-- A geometric estimate for the complete error without a lattice bound. -/
theorem palindrome_global_norm {n m : ℕ} (B : BonamiExternal)
    (σ : Equiv.Perm (Fin n)) (p : ℝ) (hp : 2 ≤ p)
    (hm : 0 < m) (hnm : n ≤ m) (hb : globalChaosScale n m p < 1) :
    finiteLp p (fun ρ : Fin m → Equiv.Perm (Fin n) => palindromeRelativeError ρ σ) ≤
      globalChaosScale n m p/(1-globalChaosScale n m p) := by
  have hh := palindrome_error_colored_bound B hm σ p hp
  apply hh.trans
  apply (Finset.sum_le_sum (fun ell _ => ?_)).trans
    (geometric_nonempty_partial _ (by unfold globalChaosScale; positivity) hb m)
  change (2*Real.sqrt (p-1))^ell*Real.sqrt
    (∑ K, segmentCoefficientEnergy σ ell K) ≤ _
  have he := Real.sqrt_le_sqrt (palindrome_global_energy σ ell hm hnm)
  have hp' : 2*Real.sqrt (p-1) ≤ 2*Real.sqrt p := by gcongr; linarith
  have hf : 1 ≤ Real.sqrt (ell.factorial : ℝ) := by
    apply Real.le_sqrt_of_sq_le
    exact_mod_cast Nat.factorial_pos ell
  calc
    _ ≤ (2*Real.sqrt p)^ell*Real.sqrt (((n : ℝ)^6/(m : ℝ)^5)^ell/(ell.factorial : ℝ)) :=
      mul_le_mul (pow_le_pow_left₀ (by positivity) hp' ell) he (by positivity) (by positivity)
    _ = (globalChaosScale n m p)^ell/Real.sqrt (ell.factorial : ℝ) := by
      rw [Real.sqrt_div (by positivity),sqrt_nat_power _ (by positivity)]
      unfold globalChaosScale; rw [mul_pow]; ring
    _ ≤ _ := div_le_self (by unfold globalChaosScale; positivity) hf

end FairDice
