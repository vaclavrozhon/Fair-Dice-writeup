import FairDice.FiniteMarkov

namespace FairDice

noncomputable def palindromeMomentOrder (n : ℕ) : ℝ :=
  max 2 (Real.log (2*(n.factorial : ℝ))/Real.log 3)

theorem log_three_gt_one : (1 : ℝ) < Real.log 3 := by
  exact (Real.lt_log_iff_exp_lt (by norm_num)).mpr Real.exp_one_lt_three

theorem palindromeMomentOrder_lower (n : ℕ) : 2 ≤ palindromeMomentOrder n := le_max_left _ _

private theorem log_factorial_bound {n : ℕ} (hn : 0 < n) :
    Real.log (n.factorial : ℝ) ≤ n * Real.log (n : ℝ) := by
  have hpos : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hfac : (n.factorial : ℝ) ≤ (n : ℝ)^n := by exact_mod_cast Nat.factorial_le_pow n
  have hh := Real.log_le_log hpos hfac
  rwa [Real.log_pow] at hh

/-- The chosen moment exponent lies in the range required by the new
moment lemma, including the small endpoint `n=3`. -/
theorem palindromeMomentOrder_upper {n : ℕ} (hn : 3 ≤ n) :
    palindromeMomentOrder n ≤ (n : ℝ)^2 := by
  have hnr : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hlog := log_factorial_bound (by omega : 0 < n)
  have hlogn := Real.log_le_sub_one_of_pos hn0
  have hlog2 := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
  have hlog3 := log_three_gt_one
  unfold palindromeMomentOrder
  apply max_le (by nlinarith)
  apply (div_le_iff₀ (by linarith : 0 < Real.log 3)).mpr
  rw [Real.log_mul (by norm_num) hfac.ne']
  have hh := mul_le_mul_of_nonneg_left hlogn hn0.le
  nlinarith

/-- The explicit order `O(n log n)` bound, with constant two. -/
theorem palindromeMomentOrder_log_bound {n : ℕ} (hn : 3 ≤ n) :
    palindromeMomentOrder n ≤ 2*n*Real.log (n : ℝ) := by
  have hnr : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hlog3 := log_three_gt_one
  have hlogn := (Real.log_le_log (by norm_num : (0 : ℝ) < 3) hnr)
  have hlog2 := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith : (2 : ℝ) ≤ n)
  have hlogfac := log_factorial_bound (by omega : 0 < n)
  unfold palindromeMomentOrder
  apply max_le (by nlinarith)
  apply (div_le_iff₀ (by linarith : 0 < Real.log 3)).mpr
  rw [Real.log_mul (by norm_num) hfac.ne']
  have hh : 2*n*Real.log (n : ℝ) ≤ (2*n*Real.log (n : ℝ))*Real.log 3 :=
    le_mul_of_one_le_right (by positivity) hlog3.le
  nlinarith

/-- The factorial union-bound cost is at most one half for this exponent. -/
theorem palindromeMomentOrder_tail (n : ℕ) :
    (n.factorial : ℝ) * (1/3 : ℝ)^(palindromeMomentOrder n) ≤ 1/2 := by
  have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hl3 : (0 : ℝ) < Real.log 3 := by linarith [log_three_gt_one]
  have hp := le_max_right (2 : ℝ) (Real.log (2*(n.factorial : ℝ))/Real.log 3)
  have hex : Real.log (2*(n.factorial : ℝ)) ≤ palindromeMomentOrder n * Real.log 3 :=
    (div_le_iff₀ hl3).mp hp
  have hl : Real.log (1/3 : ℝ) = -Real.log 3 := by rw [one_div, Real.log_inv]
  have he := Real.exp_le_exp.mpr (show Real.log (1/3 : ℝ)*palindromeMomentOrder n ≤
    -Real.log (2*(n.factorial : ℝ)) by rw [hl]; nlinarith)
  rw [← Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 1/3), Real.exp_neg,
    Real.exp_log (by positivity : 0 < 2*(n.factorial : ℝ))] at he
  have hh := mul_le_mul_of_nonneg_left he hfac.le
  have heq : (n.factorial : ℝ) * (2*(n.factorial : ℝ))⁻¹ = 1/2 := by field_simp
  rwa [heq] at hh

/-- The final probability argument requires only the moment margin; the
choice of exponent and its factorial cost are supplied internally. -/
theorem palindrome_good_probability_of_chosen_moments {n m : ℕ} {ε : ℝ}
    (hε : 0 < ε)
    (hmoment : ∀ σ : Equiv.Perm (Fin n), finiteLp (palindromeMomentOrder n)
      (fun ρ : Fin m → Equiv.Perm (Fin n) => palindromeRelativeError ρ σ) ≤ ε/3) :
    finiteEventMass (fun ρ : Fin m → Equiv.Perm (Fin n) =>
      ∃ σ : Equiv.Perm (Fin n), ε ≤ |palindromeRelativeError ρ σ|) ≤ 1/2 ∧
    ∃ ρ : Fin m → Equiv.Perm (Fin n), ∀ q : List (Fin n), q.Nodup → q.length = n →
      |(patternProbability (palindromeWord ρ) q : ℝ) - 1/(n.factorial : ℝ)| ≤ ε/(n.factorial : ℝ) := by
  exact palindrome_good_probability_of_moments
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (palindromeMomentOrder_lower n))
    hε hmoment (palindromeMomentOrder_tail n)

end FairDice
