import FairDice.MultinomialCollision

namespace FairDice

/-- Two classical Poisson mass estimates, supplied as explicit hypotheses.
The dice-specific lattice summation is not part of this interface. -/
structure PoissonEstimates : Prop where
  mass_max : ∀ rate : ℝ, 0 ≤ rate → ∀ k : ℕ,
    poissonMass rate k ≤ 2 / Real.sqrt (1+rate)
  at_mean : ∀ d : ℕ,
    1 / (3 * Real.sqrt (d+1 : ℝ)) ≤ poissonMass d d

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Conditioning independent Poisson variables gives the pointwise
multinomial collision estimate used before the lattice summation. -/
theorem poisson_collision_bound (H : PoissonEstimates) (d : ℕ) (u : ι → ℝ)
    (hu0 : ∀ j, 0 ≤ u j) (hu : ∑ j, u j = 1) :
    multinomialCollision d u ≤ 3 * 2^(Fintype.card ι) * Real.sqrt (d+1 : ℝ) *
      ∏ j, (1 / Real.sqrt (1+(d : ℝ)*u j)) := by
  apply multinomialCollision_le_max d u hu0 hu
  intro a ha
  have hsum : ∑ j, a j = d := (Finset.mem_piAntidiag.mp ha).1
  have hprod := Finset.prod_le_prod (s := Finset.univ)
    (fun j _ => show 0 ≤ poissonMass (d*u j) (a j) by
      unfold poissonMass
      exact div_nonneg (mul_nonneg (Real.exp_pos _).le
        (pow_nonneg (mul_nonneg (Nat.cast_nonneg _) (hu0 j)) _)) (Nat.cast_nonneg _))
    (fun j _ => H.mass_max (d*u j) (mul_nonneg (Nat.cast_nonneg _) (hu0 j)) (a j))
  rw [poisson_multinomial_identity d u hu a hsum] at hprod
  have hlower := mul_le_mul_of_nonneg_right (H.at_mean d) (multinomialMass_nonneg d u hu0 a)
  have hpos : 0 < 3 * Real.sqrt (d+1 : ℝ) := by positivity
  have hh : multinomialMass d u a / (3 * Real.sqrt (d+1 : ℝ)) ≤
      ∏ j, 2 / Real.sqrt (1+(d : ℝ)*u j) := by
    have he : (1 / (3 * Real.sqrt (d+1 : ℝ))) * multinomialMass d u a =
        multinomialMass d u a / (3 * Real.sqrt (d+1 : ℝ)) := by ring
    rw [he] at hlower
    exact hlower.trans hprod
  have hm := (div_le_iff₀ hpos).mp hh
  have hprod2 : (∏ j, 2 / Real.sqrt (1+(d : ℝ)*u j)) =
      2^(Fintype.card ι) * ∏ j, (1 / Real.sqrt (1+(d : ℝ)*u j)) := by
    simp [div_eq_mul_inv, Finset.prod_mul_distrib]
  rw [hprod2] at hm
  calc
    _ ≤ (2^(Fintype.card ι) * ∏ j, 1 / Real.sqrt (1+(d : ℝ)*u j)) *
        (3 * Real.sqrt (d+1 : ℝ)) := hm
    _ = _ := by ring

omit [DecidableEq ι] in
/-- Every weak composition has a coordinate at least its arithmetic mean. -/
theorem composition_large_coordinate [Nonempty ι] (M : ℕ) (g : ι → ℕ)
    (hg : ∑ j, g j = M) : ∃ j : ι, (M : ℝ)/(Fintype.card ι : ℝ) ≤ g j := by
  have hcard : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  by_contra h
  push Not at h
  have hh := Finset.sum_lt_sum_of_nonempty (s := Finset.univ) Finset.univ_nonempty
    (fun j _ => h j)
  have hsum : (∑ j, (g j : ℝ)) = M := by exact_mod_cast hg
  have hconst : (∑ _ : ι, (M : ℝ)/(Fintype.card ι : ℝ)) = M := by
    simp
    field_simp
  rw [hsum, hconst] at hh
  exact lt_irrefl _ hh

/-- Suppress the distinguished large coordinate's square-root factor. -/
theorem suppress_large_coordinate (d M N g : ℕ) (hM : 0 < M) (hN : 0 < N)
    (hg : (M : ℝ)/N ≤ g) :
    Real.sqrt (d+1 : ℝ) * (1 / Real.sqrt (1+(d : ℝ)*g/M)) ≤ Real.sqrt (N : ℝ) := by
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hgr : (0 : ℝ) ≤ g := Nat.cast_nonneg _
  have hdr : (0 : ℝ) ≤ d := Nat.cast_nonneg _
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hgm : (M : ℝ) ≤ g*N := (div_le_iff₀ hNr).mp hg
  have hden : (0 : ℝ) < 1+(d : ℝ)*g/M := by positivity
  have hsden := Real.sq_sqrt hden.le
  have hsd := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ d+1)
  have hsN := Real.sq_sqrt hNr.le
  have hcomp : (d+1 : ℝ) ≤ N*(1+(d : ℝ)*g/M) := by
    have hh : (d : ℝ)*M ≤ d*g*N := by nlinarith
    apply (mul_le_mul_iff_left₀ hMr).mp
    field_simp
    nlinarith
  have hsq : (Real.sqrt (d+1 : ℝ))^2 ≤
      (Real.sqrt (N : ℝ)*Real.sqrt (1+(d : ℝ)*g/M))^2 := by
    rw [mul_pow, hsden, hsN, hsd]
    exact hcomp
  have hr : 0 < Real.sqrt (1+(d : ℝ)*g/M) := Real.sqrt_pos.mpr hden
  have hle : Real.sqrt (d+1 : ℝ) ≤ Real.sqrt (N : ℝ)*Real.sqrt (1+(d : ℝ)*g/M) := by
    nlinarith [mul_nonneg (Real.sqrt_nonneg (N : ℝ)) hr.le]
  have he : Real.sqrt (d+1 : ℝ) * (1 / Real.sqrt (1+(d : ℝ)*g/M)) =
      Real.sqrt (d+1 : ℝ) / Real.sqrt (1+(d : ℝ)*g/M) := by ring
  rw [he, div_le_iff₀ hr]
  exact hle

end FairDice
