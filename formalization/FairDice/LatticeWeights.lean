import FairDice.CompositionWeights

namespace FairDice

/-- A decreasing weight is controlled by successive square-root differences.
This gives the lattice Riemann-sum bound without an improper integral. -/
theorem reciprocal_sqrt_step (D : ℝ) (hD : 0 < D) (j : ℕ) :
    1 / Real.sqrt (1+D*(j+1)) ≤
      (2/D) * (Real.sqrt (1+D*(j+1)) - Real.sqrt (1+D*j)) := by
  have hj : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hx : (0 : ℝ) ≤ 1+D*j := by positivity
  have hy : (0 : ℝ) < 1+D*(j+1) := by positivity
  have hr : 0 < Real.sqrt (1+D*(j+1)) := Real.sqrt_pos.mpr hy
  have hsx := Real.sq_sqrt hx
  have hsy := Real.sq_sqrt hy.le
  rw [div_le_iff₀ hr]
  have he : (2/D)*(Real.sqrt (1+D*(j+1))-Real.sqrt (1+D*j)) *
      Real.sqrt (1+D*(j+1)) =
      (2*(Real.sqrt (1+D*(j+1))-Real.sqrt (1+D*j))*Real.sqrt (1+D*(j+1)))/D := by ring
  rw [he, le_div_iff₀ hD]
  nlinarith [sq_nonneg (Real.sqrt (1+D*(j+1)) - Real.sqrt (1+D*j))]

theorem reciprocal_sqrt_partial_sum (D : ℝ) (hD : 0 < D) (M : ℕ) :
    (∑ j ∈ Finset.range (M+1), 1 / Real.sqrt (1+D*j)) ≤
      1 + (2/D)*(Real.sqrt (1+D*M)-1) := by
  rw [Finset.sum_range_succ']
  have hh := Finset.sum_le_sum (s := Finset.range M) (fun j _ => reciprocal_sqrt_step D hD j)
  have he : (∑ j ∈ Finset.range M,
      (2/D)*(Real.sqrt (1+D*(j+1)) - Real.sqrt (1+D*j))) =
        (2/D)*(Real.sqrt (1+D*M)-1) := by
    rw [← Finset.mul_sum]
    have ht := Finset.sum_range_sub (fun j : ℕ => Real.sqrt (1+D*(j : ℝ))) M
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, mul_zero, add_zero, Real.sqrt_one] at ht
    rw [ht]
  rw [he] at hh
  simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, mul_zero, add_zero, zero_add,
    Real.sqrt_one, div_one, add_comm] using add_le_add_right hh 1

/-- The one-dimensional summation estimate in `lem:palindrome-lattice`. -/
theorem lattice_weight_sum (d M : ℕ) (hM : d+1 ≤ M) :
    (∑ k : Fin (M+1), 1 / Real.sqrt (1+(d : ℝ)*k.val/M)) ≤
      3*M/Real.sqrt (d+1 : ℝ) := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hM0 : (M : ℝ) ≠ 0 := ne_of_gt hMr
  rw [Fin.sum_univ_eq_sum_range (fun k : ℕ => 1 / Real.sqrt (1+(d : ℝ)*k/M)) (M+1)]
  by_cases hd : d = 0
  · subst d
    simp only [Nat.cast_zero, zero_mul, zero_div, add_zero, Real.sqrt_one, div_one]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, Nat.cast_add, Nat.cast_one]
    have hh : (1 : ℝ) ≤ M := by exact_mod_cast hM
    linarith
  have hdr : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd
  have hd0 : (d : ℝ) ≠ 0 := ne_of_gt hdr
  have hr : 0 < Real.sqrt (d+1 : ℝ) := Real.sqrt_pos.mpr (by positivity)
  have hs := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ d+1)
  have hpartial := reciprocal_sqrt_partial_sum ((d : ℝ)/M) (div_pos hdr hMr) M
  have hpow : 1 + ((d : ℝ)/M)*M = d+1 := by field_simp; ring
  rw [hpow] at hpartial
  have hrewrite : (2/((d : ℝ)/M))*(Real.sqrt (d+1 : ℝ)-1) =
      2*M/(Real.sqrt (d+1 : ℝ)+1) := by
    have hn : Real.sqrt (d+1 : ℝ)+1 ≠ 0 := by positivity
    field_simp
    nlinarith
  rw [hrewrite] at hpartial
  have hsum : (∑ j ∈ Finset.range (M+1), 1 / Real.sqrt (1+(d : ℝ)*j/M)) =
      ∑ j ∈ Finset.range (M+1), 1 / Real.sqrt (1+((d : ℝ)/M)*j) := by
    apply Finset.sum_congr rfl
    intro j _
    congr 2
    ring
  rw [hsum]
  have hden := div_le_div_of_nonneg_left (show (0 : ℝ) ≤ 2*M by positivity)
    hr (show Real.sqrt (d+1 : ℝ) ≤ Real.sqrt (d+1 : ℝ)+1 by linarith)
  have hMreal : (d+1 : ℝ) ≤ M := by exact_mod_cast hM
  have hrM : Real.sqrt (d+1 : ℝ) ≤ M := by nlinarith [Real.sqrt_nonneg (d+1 : ℝ)]
  have hunit : (1 : ℝ) ≤ M/Real.sqrt (d+1 : ℝ) := (le_div_iff₀ hr).mpr (by simpa using hrM)
  calc
    _ ≤ 1 + 2*M/(Real.sqrt (d+1 : ℝ)+1) := hpartial
    _ ≤ 1 + 2*M/Real.sqrt (d+1 : ℝ) := by linarith [hden]
    _ ≤ M/Real.sqrt (d+1 : ℝ) + 2*M/Real.sqrt (d+1 : ℝ) := by linarith
    _ = 3*M/Real.sqrt (d+1 : ℝ) := by ring

end FairDice
