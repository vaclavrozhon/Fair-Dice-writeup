import FairDice.SelectedEnergy
import FairDice.PalindromeSeries

namespace FairDice

/-- The cancellation of the palindrome error bound with the actual
size/residue retention probability, for `k ≥ 3` (also valid for `k = 2`). -/
theorem palindrome_color_factor (k : ℕ) (hk : 2 ≤ k) :
    (((k.factorial : ℝ)*2/(2 : ℝ)^k)^2)/((1/(2 : ℝ)^(k-2))/k) =
      (k.factorial : ℝ)^2*((k : ℝ)/(2 : ℝ)^k) := by
  rw [pow_sub₀ (2 : ℝ) (by norm_num) hk]
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k≠0)
  field_simp

/-- Exact colored energy after summing over the unselected letter counts.
In particular, all selected factorials cancel; the remaining length weight
is `∏ k / 2^k`, as used in both support estimates in the article. -/
theorem selected_gap_colored_squared_sum {ell : ℕ} (m s d M : ℕ)
    (k : Fin ell → ℕ) (g : Fin (ell+1) → ℕ)
    (hm : 0 < m) (hM : 0 < M) (hk : ∀ j, 2 ≤ k j) :
    (∑ a ∈ Finset.piAntidiag (Finset.univ : Finset (Fin (ell+1))) d,
      (selectedGapMass m s d k g a)^2 *
        ∏ j, (((k j).factorial : ℝ)*2/(2 : ℝ)^k j)^2 /
          ((1/(2 : ℝ)^(k j-2))/(k j : ℝ))) =
      (((s+d).descFactorial s : ℝ)/(m : ℝ)^s)^2 *
        ((M : ℝ)/m)^(2*d) * (∏ j, (k j : ℝ)/(2 : ℝ)^k j) *
          multinomialCollision d (fun j => (g j : ℝ)/M) := by
  simp_rw [palindrome_color_factor _ (hk _)]
  rw [← Finset.sum_mul, selected_gap_squared_sum m s d M k g hm hM,
    Finset.prod_mul_distrib, Finset.prod_pow]
  have hfac : (∏ j, ((k j).factorial : ℝ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => by exact_mod_cast Nat.factorial_ne_zero (k j))
  field_simp

/-- Colored energy summed over all block gaps, before bounding the falling
factorial and the length series. This is the common input to the short-
and long-support estimates. -/
theorem selected_colored_lattice_bound (H : PoissonEstimates) (ell m s d M : ℕ)
    (k : Fin ell → ℕ) (hell : 1 ≤ ell) (hm : 0 < m)
    (hM : d+1 ≤ M) (hk : ∀ j, 2 ≤ k j) :
    (∑ g ∈ Finset.piAntidiag (Finset.univ : Finset (Fin (ell+1))) M,
      ∑ a ∈ Finset.piAntidiag (Finset.univ : Finset (Fin (ell+1))) d,
        (selectedGapMass m s d k g a)^2 *
          ∏ j, (((k j).factorial : ℝ)*2/(2 : ℝ)^k j)^2 /
            ((1/(2 : ℝ)^(k j-2))/(k j : ℝ))) ≤
      (((s+d).descFactorial s : ℝ)/(m : ℝ)^s)^2 *
        ((M : ℝ)/m)^(2*d) * (∏ j, (k j : ℝ)/(2 : ℝ)^k j) *
          (108*M/Real.sqrt (d+1 : ℝ))^ell := by
  simp_rw [selected_gap_colored_squared_sum m s d M k _ hm (by omega) hk]
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (palindrome_lattice_bound H ell d M hell hM)
    (by positivity)

/-- The separated length weights after cancellation. -/
theorem colored_length_product {ell : ℕ} (n m s : ℕ) (k : Fin ell → ℕ)
    (hs : ∑ j, k j=s) :
    (((n : ℝ)/(m : ℝ))^s)^2 * (∏ j, (k j : ℝ)/(2 : ℝ)^k j) =
      ∏ j, (k j : ℝ)*((n : ℝ)^2/(2*(m : ℝ)^2))^k j := by
  simp only [Finset.prod_mul_distrib, Finset.prod_div_distrib,
    Finset.prod_pow_eq_pow_sum, hs, div_pow, mul_pow]
  rw [← pow_mul, ← pow_mul, Nat.mul_comm s 2, pow_mul]
  ring

/-- The coefficient square-sum for a fixed length vector of short support,
including the article's constant 160. The only analytic input is the
classical scalar Poisson estimates. -/
theorem short_selected_colored_energy (H : PoissonEstimates)
    (ell m n s d : ℕ) (k : Fin ell → ℕ) (hell : 1 ≤ ell)
    (hk : ∀ j, 3 ≤ k j) (hs : ∑ j, k j=s) (hnd : s+d=n)
    (hshort : 2*s ≤ n) (hnm : n ≤ m) :
    (∑ g ∈ Finset.piAntidiag (Finset.univ : Finset (Fin (ell+1))) (m-ell),
      ∑ a ∈ Finset.piAntidiag (Finset.univ : Finset (Fin (ell+1))) d,
        (selectedGapMass m s d k g a)^2 *
          ∏ j, (((k j).factorial : ℝ)*2/(2 : ℝ)^k j)^2 /
            ((1/(2 : ℝ)^(k j-2))/(k j : ℝ))) ≤
      (160*m/Real.sqrt (n : ℝ))^ell *
        ∏ j, (k j : ℝ)*((n : ℝ)^2/(2*(m : ℝ)^2))^k j := by
  have hsl : 3*ell ≤ s := by
    have h := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin ell)))
      (fun j _ => hk j)
    simpa [hs, Nat.mul_comm] using h
  have hn : 0 < n := by omega
  have hm : 0 < m := by omega
  have hM : d+1 ≤ m-ell := by omega
  have hbase := selected_colored_lattice_bound H ell m s d (m-ell) k hell hm hM
    (fun j => (hk j).trans' (by norm_num))
  rw [hnd] at hbase
  have hfall : ((n.descFactorial s : ℝ)/(m : ℝ)^s)^2 ≤
      (((n : ℝ)/(m : ℝ))^s)^2 := by
    have hcast : (n.descFactorial s : ℝ) ≤ (n : ℝ)^s := by
      exact_mod_cast Nat.descFactorial_le_pow n s
    have hh := pow_le_pow_left₀ (div_nonneg (Nat.cast_nonneg _) (by positivity : (0 : ℝ) ≤ (m : ℝ)^s))
      (div_le_div_of_nonneg_right hcast (by positivity : (0 : ℝ) ≤ (m : ℝ)^s)) 2
    simpa only [div_pow] using hh
  have hratio : (((m-ell : ℕ) : ℝ)/m)^(2*d) ≤ 1 := by
    apply pow_le_one₀ (by positivity)
    have hmr : (0 : ℝ) < m := by exact_mod_cast hm
    apply (div_le_one hmr).mpr
    exact_mod_cast Nat.sub_le m ell
  have hpref : ((n.descFactorial s : ℝ)/(m : ℝ)^s)^2 *
      (((m-ell : ℕ) : ℝ)/m)^(2*d) ≤ (((n : ℝ)/(m : ℝ))^s)^2 := by
    calc
      _ ≤ ((n.descFactorial s : ℝ)/(m : ℝ)^s)^2 * 1 :=
        mul_le_mul_of_nonneg_left hratio (sq_nonneg _)
      _ ≤ _ := by simpa using hfall
  have hlattice := short_lattice_constant n d m (m-ell) hn (by omega) (Nat.sub_le _ _)
  have hpow := pow_le_pow_left₀ (by positivity) hlattice ell
  calc
    _ ≤ _ := hbase
    _ ≤ (((n : ℝ)/(m : ℝ))^s)^2 * (∏ j, (k j : ℝ)/(2 : ℝ)^k j) *
        (160*m/Real.sqrt (n : ℝ))^ell :=
      mul_le_mul (mul_le_mul_of_nonneg_right hpref (by positivity)) hpow
        (by positivity) (by positivity)
    _ = _ := by rw [colored_length_product n m s k hs]; ring

/-- Finite length sums have the same bound as the infinite majorant;
there is no assumption that the target pattern admits every length. -/
theorem palindrome_finite_length_series (N : ℕ) (z : ℝ) (hz0 : 0 ≤ z) (hz : z ≤ 1/2) :
    (∑ j : Fin N, ((j.val+3 : ℕ) : ℝ)*z^(j.val+3)) ≤ 8*z^3 := by
  have habs : |z|<1 := by rw [abs_of_nonneg hz0]; linarith
  have hsum := (hasSum_coe_mul_geometric_of_norm_lt_one (r := z)
    (by simpa using habs)).summable
  have hshift : Summable (fun j : ℕ => ((j+3 : ℕ) : ℝ)*z^(j+3)) :=
    (summable_nat_add_iff 3).mpr hsum
  rw [Fin.sum_univ_eq_sum_range (fun j : ℕ => ((j+3 : ℕ) : ℝ)*z^(j+3)) N]
  exact (hshift.sum_le_tsum _ (fun j _ => by positivity)).trans
    (palindrome_length_series_bound z hz0 hz)

/-- Extending all selected length choices independently gives the product
of scalar series. This supplies the length summation in the short-support
square-energy estimate. -/
theorem palindrome_length_vector_bound (ell N n m : ℕ) (hm : 0 < m) (hnm : n ≤ m) :
    (∑ k : Fin ell → Fin N,
      ∏ j, (((k j).val+3 : ℕ) : ℝ)*
        ((n : ℝ)^2/(2*(m : ℝ)^2))^((k j).val+3)) ≤
      ((n : ℝ)^6/(m : ℝ)^6)^ell := by
  let z : ℝ := (n : ℝ)^2/(2*(m : ℝ)^2)
  have hz0 : 0 ≤ z := by positivity
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hz : z ≤ 1/2 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ)<2*(m : ℝ)^2)).mpr
    have hnmr : (n : ℝ) ≤ m := by exact_mod_cast hnm
    nlinarith [sq_nonneg ((m : ℝ)-n)]
  have he : 8*z^3=(n : ℝ)^6/(m : ℝ)^6 := by
    dsimp [z]
    ring
  have hp := Fintype.prod_sum (ι := Fin ell) (κ := fun _ => Fin N)
    (fun (_ : Fin ell) (j : Fin N) => ((j.val+3 : ℕ) : ℝ)*z^(j.val+3))
  change (∑ k : Fin ell → Fin N, ∏ j, (((k j).val+3 : ℕ) : ℝ)*z^((k j).val+3)) ≤ _
  rw [← hp]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [← he]
  exact pow_le_pow_left₀ (Finset.sum_nonneg (fun _ _ => by positivity))
    (palindrome_finite_length_series N z hz0 hz) ell

end FairDice
