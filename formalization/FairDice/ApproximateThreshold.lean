import FairDice.MomentOrder

namespace FairDice

/-- The scale appearing in the new uniform moment estimate. -/
noncomputable def palindromeMomentScale (n m p : ℝ) : ℝ :=
  n^(11/4 : ℝ)*Real.sqrt p/m^(5/2 : ℝ)

/-- Raising the prescribed moment threshold to `5/2` gives the exact
error dependence. This arithmetic step assumes no probabilistic estimate. -/
theorem palindrome_scale_threshold {n m p ε : ℝ} (hn : 0<n) (hp : 0<p)
    (hε : 0<ε) (hm : 8*n^(11/10 : ℝ)*p^(1/5 : ℝ)*ε^(-2/5 : ℝ) ≤ m) :
    32*palindromeMomentScale n m p ≤ ε/3 := by
  have hth : 0<8*n^(11/10 : ℝ)*p^(1/5 : ℝ)*ε^(-2/5 : ℝ) := by positivity
  have hm0 : 0 < m := hth.trans_le hm
  have hh := Real.rpow_le_rpow hth.le hm (by norm_num : (0 : ℝ) ≤ 5/2)
  have he : (8*n^(11/10 : ℝ)*p^(1/5 : ℝ)*ε^(-2/5 : ℝ))^(5/2 : ℝ) =
      (8 : ℝ)^(5/2 : ℝ)*n^(11/4 : ℝ)*Real.sqrt p/ε := by
    rw [Real.mul_rpow (by positivity : 0 ≤ 8*n^(11/10 : ℝ)*p^(1/5 : ℝ))
        (Real.rpow_nonneg hε.le _),
      Real.mul_rpow (by positivity : 0 ≤ 8*n^(11/10 : ℝ)) (Real.rpow_nonneg hp.le _),
      Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 8) (Real.rpow_nonneg hn.le _),
      ← Real.rpow_mul hn.le, ← Real.rpow_mul hp.le, ← Real.rpow_mul hε.le]
    norm_num
    rw [Real.sqrt_eq_rpow,Real.rpow_neg_one]
    ring

  rw [he] at hh
  have hc : (96 : ℝ) ≤ (8 : ℝ)^(5/2 : ℝ) := by
    have hmono := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 8)
      (by norm_num : (2 : ℝ) ≤ 5/2)
    norm_num at hmono
    have he8 : (8 : ℝ)^(5/2 : ℝ) = 64*Real.sqrt 8 := by
      rw [show (5/2 : ℝ)=2+1/2 by norm_num,Real.rpow_add (by norm_num),
        Real.rpow_two,← Real.sqrt_eq_rpow]
      norm_num
    rw [he8]
    have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8)
    have hs0 := Real.sqrt_nonneg (8 : ℝ)
    nlinarith
  have hnum : 0 ≤ n^(11/4 : ℝ)*Real.sqrt p := by positivity
  have hbound : 96*(n^(11/4 : ℝ)*Real.sqrt p) ≤ ε*m^(5/2 : ℝ) := by
    have hh' := (div_le_iff₀ hε).mp hh
    have hc' := mul_le_mul_of_nonneg_right hc hnum
    nlinarith
  have hd := (div_le_iff₀ (Real.rpow_pos_of_pos hm0 (5/2))).mpr hbound
  have hh' : 96*(n^(11/4 : ℝ)*Real.sqrt p/m^(5/2 : ℝ)) ≤ ε := by
    simpa only [mul_div_assoc] using hd
  unfold palindromeMomentScale
  linarith

/-- An explicit absolute constant translates `O(n log n)` moment order
into the stated `n^(13/10) (log n)^(1/5)` number of blocks. -/
theorem palindrome_chosen_threshold {n : ℕ} {m ε : ℝ} (hn : 3 ≤ n)
    (hε : 0<ε)
    (hm : 16*(n : ℝ)^(13/10 : ℝ)*(Real.log n)^(1/5 : ℝ)*ε^(-2/5 : ℝ) ≤ m) :
    8*(n : ℝ)^(11/10 : ℝ)*(palindromeMomentOrder n)^(1/5 : ℝ)*ε^(-2/5 : ℝ) ≤ m := by
  have hn0 : (0 : ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hl0 : (0 : ℝ)<Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1<n))
  have hp0 : 0 ≤ palindromeMomentOrder n := (by norm_num : (0 : ℝ) ≤ 2).trans (palindromeMomentOrder_lower n)
  have hp := Real.rpow_le_rpow hp0 (palindromeMomentOrder_log_bound hn) (by norm_num : (0 : ℝ) ≤ 1/5)
  have he : (2*(n : ℝ)*Real.log n)^(1/5 : ℝ) =
      (2 : ℝ)^(1/5 : ℝ)*(n : ℝ)^(1/5 : ℝ)*(Real.log n)^(1/5 : ℝ) := by
    rw [Real.mul_rpow (by positivity) hl0.le, Real.mul_rpow (by norm_num) hn0.le]
  rw [he] at hp
  have hc : (2 : ℝ)^(1/5 : ℝ) ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by norm_num : (1/5 : ℝ) ≤ 1)
  calc
    _ ≤ 8*(n : ℝ)^(11/10 : ℝ)*
      ((2 : ℝ)^(1/5 : ℝ)*(n : ℝ)^(1/5 : ℝ)*(Real.log n)^(1/5 : ℝ))*ε^(-2/5 : ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by positivity)) (by positivity)
    _ ≤ 8*(n : ℝ)^(11/10 : ℝ)*
      (2*(n : ℝ)^(1/5 : ℝ)*(Real.log n)^(1/5 : ℝ))*ε^(-2/5 : ℝ) := by
      gcongr
    _ = 16*(n : ℝ)^(13/10 : ℝ)*(Real.log n)^(1/5 : ℝ)*ε^(-2/5 : ℝ) := by
      rw [show (13/10 : ℝ)=11/10+1/5 by norm_num,Real.rpow_add hn0]
      ring
    _ ≤ m := hm

/-- The quantitative threshold-to-probability deduction for the concrete
word, conditional on exactly the manuscript's uniform moment estimate.
This separates proved threshold arithmetic from the still-needed moment
lemma; the latter is not classified as an external mathematical input. -/
theorem palindrome_approximate_from_uniform_moment {n m : ℕ} {ε : ℝ}
    (hn : 3 ≤ n) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hm : 16*(n : ℝ)^(13/10 : ℝ)*(Real.log n)^(1/5 : ℝ)*ε^(-2/5 : ℝ) ≤ m)
    (hmoment : ∀ p : ℝ, 2 ≤ p → p ≤ (n : ℝ)^2 →
      8*(n : ℝ)^(11/10 : ℝ)*p^(1/5 : ℝ) ≤ m →
      ∀ σ : Equiv.Perm (Fin n), finiteLp p
        (fun ρ : Fin m → Equiv.Perm (Fin n) => palindromeRelativeError ρ σ) ≤
          32*palindromeMomentScale n m p) :
    finiteEventMass (fun ρ : Fin m → Equiv.Perm (Fin n) =>
      ∃ σ : Equiv.Perm (Fin n), ε ≤ |palindromeRelativeError ρ σ|) ≤ 1/2 ∧
    ∃ ρ : Fin m → Equiv.Perm (Fin n), ∀ q : List (Fin n), q.Nodup → q.length = n →
      |(patternProbability (palindromeWord ρ) q : ℝ)-1/(n.factorial : ℝ)| ≤ ε/(n.factorial : ℝ) := by
  have hn0 : (0 : ℝ)<n := by exact_mod_cast (by omega : 0<n)
  have hp0 : 0<palindromeMomentOrder n := lt_of_lt_of_le (by norm_num) (palindromeMomentOrder_lower n)
  have ht := palindrome_chosen_threshold hn hε hm
  have hεpow : (1 : ℝ) ≤ ε^(-2/5 : ℝ) := by
    have hh := Real.rpow_le_rpow_of_exponent_ge hε hε1 (by norm_num : (-2/5 : ℝ) ≤ 0)
    simpa using hh
  have hbase : 8*(n : ℝ)^(11/10 : ℝ)*(palindromeMomentOrder n)^(1/5 : ℝ) ≤ m :=
    (le_mul_of_one_le_right (by positivity) hεpow).trans ht
  apply palindrome_good_probability_of_chosen_moments hε
  intro σ
  exact (hmoment _ (palindromeMomentOrder_lower n) (palindromeMomentOrder_upper hn) hbase σ).trans
    (palindrome_scale_threshold hn0 hp0 hε ht)

end FairDice
