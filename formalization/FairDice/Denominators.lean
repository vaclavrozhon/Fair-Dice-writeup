import FairDice.Hahn

namespace FairDice

open Polynomial

/-- `d` clears the denominator of a rational number. -/
def Clears (d : ℕ) (x : ℚ) : Prop := ∃ z : ℤ, (d : ℚ) * x = z

theorem Clears.of_dvd {d D : ℕ} {x : ℚ} (h : Clears d x) (hd : d ∣ D) : Clears D x := by
  obtain ⟨z, hz⟩ := h
  obtain ⟨t, rfl⟩ := hd
  refine ⟨(t : ℤ) * z, ?_⟩
  push_cast
  rw [mul_right_comm, hz]
  ring

theorem Clears.mul_nat {d : ℕ} {x : ℚ} (h : Clears d x) (t : ℕ) : Clears d (x * t) := by
  obtain ⟨z, hz⟩ := h
  refine ⟨z * (t : ℤ), ?_⟩
  push_cast
  rw [← mul_assoc, hz]

theorem Clears.div_nat {A L d : ℕ} {x : ℚ} (h : Clears A x)
    (hd : 0 < d) (hdiv : d ∣ L) : Clears (A * L) (x / d) := by
  obtain ⟨z, hz⟩ := h
  obtain ⟨t, rfl⟩ := hdiv
  refine ⟨z * (t : ℤ), ?_⟩
  have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hd
  push_cast
  calc
    _ = ((A : ℚ) * x) * t := by field_simp
    _ = _ := by rw [hz]

theorem clears_sum {ι : Type*} (s : Finset ι) (d : ℕ) (f : ι → ℚ)
    (h : ∀ i ∈ s, Clears d (f i)) : Clears d (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨z, hz⟩ := h i (by simp)
    obtain ⟨w, hw⟩ := ih (fun j hj => h j (by simp [hj]))
    exact ⟨z + w, by simp [Finset.sum_insert hi, mul_add, hz, hw]⟩

def smallLCM (n : ℕ) : ℕ := (Finset.range (n + 1)).lcm (fun j => j + 1)

theorem smallLCM_pos (n : ℕ) : 0 < smallLCM n := by
  apply Nat.pos_of_ne_zero
  exact Finset.lcm_ne_zero_iff.mpr (fun _ _ => by omega)

theorem succ_dvd_smallLCM {j n : ℕ} (hj : j ≤ n) : j + 1 ∣ smallLCM n :=
  Finset.dvd_lcm (Finset.mem_range.mpr (by omega))

theorem smallLCM_le_factorial (n : ℕ) : smallLCM n ≤ (n + 1).factorial := by
  apply Nat.le_of_dvd (Nat.factorial_pos _)
  apply Finset.lcm_dvd
  intro j hj
  exact Nat.dvd_factorial (by omega) (Finset.mem_range.mp hj)

theorem fallingProduct_dvd {N a k : ℕ} (ha : a ≤ k) :
    fallingProduct N a ∣ fallingProduct N k :=
  Finset.prod_dvd_prod_of_subset (Finset.range a) (Finset.range k) (fun j => N - j)
    (Finset.range_mono ha)

theorem risingProduct_dvd {N a k : ℕ} (ha : a ≤ k) :
    risingProduct N a ∣ risingProduct N k :=
  Finset.prod_dvd_prod_of_subset (Finset.range a) (Finset.range k) (fun j => N + 2 + j)
    (Finset.range_mono ha)

theorem descPochhammer_degree (a : ℕ) : (descPochhammer ℚ a).natDegree ≤ a := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [descPochhammer_succ_left]
    calc
      _ ≤ X.natDegree + ((descPochhammer ℚ a).comp (X - 1)).natDegree := natDegree_mul_le
      _ ≤ 1 + a := by
        have hdeg : (X - (1 : ℚ[X])).natDegree = 1 := natDegree_X_sub_C (1 : ℚ)
        simp only [natDegree_comp, natDegree_X, hdeg, mul_one]
        omega
      _ = a + 1 := by omega

theorem hahn_degree (N k : ℕ) : (hahn N k).natDegree ≤ k := by
  apply natDegree_sum_le_of_forall_le
  intro a ha
  exact (natDegree_C_mul_le _ _).trans ((descPochhammer_degree a).trans (by
    have := Finset.mem_range.mp ha
    omega))

/-- Equation (3.16): multiplying by the falling factorial clears every
coefficient of the Hahn polynomial. -/
theorem hahn_coefficient_denominator {N k : ℕ} (hk : k ≤ N) (j : ℕ) :
    Clears (fallingProduct N k) ((hahn N k).coeff j) := by
  unfold hahn
  rw [finsetSum_coeff]
  apply clears_sum
  intro a ha
  have hak : a ≤ k := by simpa using Finset.mem_range.mp ha
  apply Clears.of_dvd (d := fallingProduct N a) _ (fallingProduct_dvd hak)
  have hA : (fallingProduct N a : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (fallingProduct_pos (hak.trans hk))
  refine ⟨(-1 : ℤ)^a * (k.choose a : ℤ) * ((k + a).choose a : ℤ) *
    (descPochhammer ℤ a).coeff j, ?_⟩
  rw [coeff_C_mul]
  have hcoeff : (descPochhammer ℚ a).coeff j =
      ((descPochhammer ℤ a).coeff j : ℚ) := by
    rw [← descPochhammer_map (Int.castRingHom ℚ), coeff_map]
    rfl
  rw [hcoeff]
  push_cast
  field_simp

/-- Term-by-term integration introduces only the integers `1,...,n+1` as
new denominators. -/
theorem polynomialIntegral_denominator {A n : ℕ} (N : ℕ) (p : ℚ[X])
    (hp : p.natDegree ≤ n) (hc : ∀ j, Clears A (p.coeff j)) :
    Clears (A * smallLCM n) (polynomialIntegral N p) := by
  change Clears _ (∑ j ∈ p.support, _)
  apply clears_sum
  intro j hj
  have hjn : j ≤ n := (le_natDegree_of_ne_zero (mem_support_iff.mp hj)).trans hp
  change Clears _ ((N : ℚ) ^ (j + 1) / (j + 1 : ℚ) * p.coeff j)
  have ht := (hc j).mul_nat (N ^ (j + 1))
  have hd := ht.div_nat (by omega : 0 < j + 1) (succ_dvd_smallLCM hjn)
  convert hd using 1
  push_cast
  ring

theorem hahn_integral_denominator {N n k : ℕ} (hn : n ≤ N) (hk : k ≤ n) :
    Clears (fallingProduct N k * smallLCM n) (hahnIntegral N k) :=
  polynomialIntegral_denominator N (hahn N k) ((hahn_degree N k).trans hk)
    (hahn_coefficient_denominator (hk.trans hn))

theorem polynomial_eval_denominator {A : ℕ} (p : ℚ[X])
    (hc : ∀ j, Clears A (p.coeff j)) (i : ℕ) : Clears A (p.eval (i : ℚ)) := by
  rw [eval_eq_sum]
  apply clears_sum
  intro j _
  simpa only [Nat.cast_pow] using (hc j).mul_nat (i ^ j)

/-- The cancellation using the Hahn norm formula is essential: only one
falling factorial remains in the denominator, rather than three. -/
theorem hahn_term_denominator (h : HahnExternal) {N n k : ℕ}
    (hn : n ≤ N) (hk : k ≤ n) (i : ℕ) :
    Clears ((N + 1) * smallLCM n * fallingProduct N k * risingProduct N k)
      (hahnIntegral N k / hahnNorm N k * (hahn N k).eval (i : ℚ)) := by
  have hkN := hk.trans hn
  obtain ⟨z, hz⟩ := hahn_integral_denominator hn hk
  obtain ⟨w, hw⟩ := polynomial_eval_denominator (hahn N k)
    (hahn_coefficient_denominator hkN) i
  have hA : (fallingProduct N k : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (fallingProduct_pos hkN)
  have hB : (risingProduct N k : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (risingProduct_pos N k)
  have hN : ((N + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  refine ⟨z * w * (2 * k + 1 : ℤ), ?_⟩
  rw [h.norm_formula N k hkN]
  calc
    _ = (((fallingProduct N k * smallLCM n : ℕ) : ℚ) * hahnIntegral N k) *
        ((fallingProduct N k : ℚ) * (hahn N k).eval (i : ℚ)) * (2 * k + 1) := by
      push_cast
      field_simp
    _ = _ := by rw [hz, hw]; push_cast; ring

def commonDenominator (N n : ℕ) : ℕ :=
  (N + 1) * smallLCM n * fallingProduct N n * risingProduct N n

theorem commonDenominator_pos {N n : ℕ} (hn : n ≤ N) :
    0 < commonDenominator N n := by
  unfold commonDenominator
  exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by omega) (smallLCM_pos n))
    (fallingProduct_pos hn)) (risingProduct_pos N n)

/-- Equation (3.21): the single denominator clears every quadrature weight. -/
theorem hahnWeight_denominator (h : HahnExternal) {N n : ℕ} (hn : n ≤ N)
    (i : Fin (N + 1)) : Clears (commonDenominator N n) (hahnWeight N n i) := by
  apply clear_projection_denominator
  intro k j
  have hk : k.val ≤ n := by omega
  have hd := hahn_term_denominator h hn hk j.val
  apply hd.of_dvd
  exact Nat.mul_dvd_mul
    (Nat.mul_dvd_mul_left _ (fallingProduct_dvd hk)) (risingProduct_dvd hk)

end FairDice
