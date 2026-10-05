import FairDice.ExponentialLowerBound

namespace FairDice

variable {α : Type*} [DecidableEq α]

theorem restrict_length_sum (A : Finset α) (s : List α) :
    (restrict A s).length = ∑ a ∈ A, s.count a := by
  induction s with
  | nil => simp [restrict]
  | cons b s ih =>
    have hc (a : α) : (b :: s).count a = s.count a + if a = b then 1 else 0 := by
      simpa only [count_singleton, count_nil] using count_cons_cons a b [] s
    simp only [hc, Finset.sum_add_distrib]
    by_cases hb : b ∈ A <;> simp [restrict, hb, ← ih, Nat.add_comm]

/-- A quantitative form of the many-large-dice argument: for every admissible
restriction size `r`, fewer than `r` dice can have fewer than `2^(c r)/r` faces.
This records the threshold before absorbing the polynomial factor. -/
theorem many_large_finite (hext : PrimorialExternal) :
    ∃ c : ℝ, 0 < c ∧ ∃ r₀ : ℕ, ∀ (α : Type) [DecidableEq α] [Fintype α]
      (s : List α), PermutationFair s → ∀ r : ℕ, max 1 r₀ ≤ r →
      ((Finset.univ : Finset α).filter (fun a =>
        (s.count a : ℝ) < (2 : ℝ)^(c * r) / r)).card < r := by
  obtain ⟨c, hc, r₀, hlen⟩ := exponential_length_lower hext
  refine ⟨c, hc, r₀, ?_⟩
  intro α _ _ s hs r hr
  classical
  have hrpos : 0 < r := by have := (le_max_left 1 r₀).trans hr; omega
  have hr₀ : r₀ ≤ r := (le_max_right 1 r₀).trans hr
  by_contra hbad
  obtain ⟨A, hA, hcard⟩ := Finset.exists_subset_card_eq (Nat.le_of_not_gt hbad)
  have hAlen := hlen A (restrict A s) (by simpa [hcard] using hr₀)
    (permutationFair_restrict hs A)
  have hsum : ∑ a ∈ A, (s.count a : ℝ) <
      ∑ _a ∈ A, (2 : ℝ)^(c * r) / r := by
    apply Finset.sum_lt_sum_of_nonempty (Finset.card_pos.mp (by omega : 0 < A.card))
    intro a ha
    exact (Finset.mem_filter.mp (hA ha)).2
  have hsumlen : (∑ a ∈ A, (s.count a : ℝ)) = ((restrict A s).length : ℝ) := by
    exact_mod_cast (restrict_length_sum A s).symm
  rw [hsumlen] at hsum
  simp only [Finset.sum_const, nsmul_eq_mul, hcard] at hsum
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hrpos
  have hcancel : (r : ℝ) * ((2 : ℝ)^(c * r) / r) = (2 : ℝ)^(c * r) := by field_simp
  rw [hcancel] at hsum
  simp only [Fintype.card_coe, hcard] at hAlen
  linarith

theorem eventually_linear_le_exponential {a : ℝ} (ha : 0 < a) :
    ∃ r₀ : ℕ, ∀ r ≥ r₀, (r : ℝ) ≤ (2 : ℝ)^(a * r) := by
  let b := Real.log 2 * a
  have hb : 0 < b := mul_pos (Real.log_pos (by norm_num)) ha
  obtain ⟨r₀, hr₀⟩ := exists_nat_ge (2 / b^2)
  refine ⟨r₀, ?_⟩
  intro r hr
  have hrR : (r₀ : ℝ) ≤ r := by exact_mod_cast hr
  have hbr : 2 ≤ (r : ℝ) * b^2 := (div_le_iff₀ (sq_pos_of_pos hb)).mp (hr₀.trans hrR)
  have hquad : (r : ℝ) ≤ (b * r)^2 / 2 := by
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ r by positivity) (sub_nonneg.mpr hbr)]
  have hexp := Real.pow_div_factorial_le_exp (b * r)
    (mul_nonneg hb.le (show (0 : ℝ) ≤ r by positivity)) 2
  norm_num at hexp
  apply hquad.trans
  have heq : (2 : ℝ)^(a * r) = Real.exp (b * r) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    congr 1
    dsimp [b]
    ring
  rw [heq]
  exact hexp

/-- Theorem 4.1, with the fraction of large dice and all asymptotic quantifiers
explicit. The constant `c` is independent of the chosen fraction. -/
theorem many_large_exponential (hext : PrimorialExternal) :
    ∃ c : ℝ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → ε < 1 →
      ∃ n₀ : ℕ, ∀ (α : Type) [DecidableEq α] [Fintype α] (s : List α),
        n₀ ≤ Fintype.card α → PermutationFair s →
        (1 - ε) * Fintype.card α ≤
          (((Finset.univ : Finset α).filter (fun a =>
            (2 : ℝ)^(c * ε * Fintype.card α) ≤ s.count a)).card : ℝ) := by
  obtain ⟨c, hc, r₀, hsmall⟩ := many_large_finite hext
  obtain ⟨r₁, habsorb⟩ := eventually_linear_le_exponential (show 0 < c / 2 by positivity)
  refine ⟨c / 4, by positivity, ?_⟩
  intro ε hε _
  let t := max 1 (max r₀ r₁)
  obtain ⟨n₀, hn₀⟩ := exists_nat_ge (2 * (t + 1 : ℝ) / ε)
  refine ⟨n₀, ?_⟩
  intro α _ _ s hn hs
  classical
  let n := Fintype.card α
  let r := ⌊ε * n⌋₊
  have hnR : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
  have hx : 2 * (t + 1 : ℝ) ≤ ε * n := by
    have hdiv := hn₀.trans hnR
    have := (div_le_iff₀ hε).mp hdiv
    nlinarith
  have hfloor : ε * n < (r : ℝ) + 1 := Nat.lt_floor_add_one _
  have hrle : (r : ℝ) ≤ ε * n := Nat.floor_le (by positivity)
  have htr : t ≤ r := by
    have htrR : (t : ℝ) ≤ r := by linarith
    exact_mod_cast htrR
  have hrpos : 0 < r := by have := (le_max_left 1 (max r₀ r₁)).trans htr; omega
  have hr₀ : max 1 r₀ ≤ r := by dsimp [t] at htr; omega
  have hr₁ : r₁ ≤ r := by dsimp [t] at htr; omega
  have hrhalf : ε * n / 2 ≤ r := by
    have htpos : (1 : ℝ) ≤ t := by exact_mod_cast (le_max_left 1 (max r₀ r₁))
    linarith
  have hthreshold : (2 : ℝ)^(c / 4 * ε * n) ≤ (2 : ℝ)^(c * r) / r := by
    apply (Real.rpow_le_rpow_of_exponent_le (by norm_num)
      (show c / 4 * ε * n ≤ c / 2 * r by nlinarith)).trans
    apply (le_div_iff₀ (by exact_mod_cast hrpos : (0 : ℝ) < r)).mpr
    have hprod := mul_le_mul_of_nonneg_left (habsorb r hr₁)
      (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (c / 2 * r))
    have hid : (2 : ℝ)^(c / 2 * r) * (2 : ℝ)^(c / 2 * r) = (2 : ℝ)^(c * r) := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring
    simpa [hid] using hprod
  have hbad : ((Finset.univ : Finset α).filter (fun a =>
      (s.count a : ℝ) < (2 : ℝ)^(c / 4 * ε * n))).card < r := by
    apply lt_of_le_of_lt (Finset.card_le_card ?_) (hsmall α s hs r hr₀)
    intro a ha
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ a,
      (Finset.mem_filter.mp ha).2.trans_le hthreshold⟩
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset α))
    (fun a => (s.count a : ℝ) < (2 : ℝ)^(c / 4 * ε * n))
  simp only [not_lt, Finset.card_univ] at hpartition
  have hbadR : (((Finset.univ : Finset α).filter (fun a =>
      (s.count a : ℝ) < (2 : ℝ)^(c / 4 * ε * n))).card : ℝ) < r := by exact_mod_cast hbad
  have hpartitionR := congrArg (fun k : ℕ => (k : ℝ)) hpartition
  push_cast at hpartitionR
  change (1 - ε) * n ≤ _
  linarith

end FairDice
