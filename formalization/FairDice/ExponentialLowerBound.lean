import FairDice.Arithmetic

namespace FairDice

/-- The classical primorial estimate cited in Section 4, in the lower-bound
form actually needed. The upper primorial estimate is already in mathlib. -/
def PrimorialExternal : Prop :=
  ∃ δ : ℝ, 0 < δ ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, (2 : ℝ)^(δ * n) ≤ primorial n

/-- Lemma 4.2, with its asymptotic quantifiers and its external number-theory
input made explicit. -/
theorem exponential_length_lower (hext : PrimorialExternal) :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ (α : Type) [DecidableEq α] [Fintype α]
      (s : List α), n₀ ≤ Fintype.card α → PermutationFair s →
      (2 : ℝ)^(c * Fintype.card α) ≤ s.length := by
  obtain ⟨δ, hδ, n₀, hprime⟩ := hext
  refine ⟨δ / 9, by positivity, max 4 (2 * n₀ + 2), ?_⟩
  intro α _ _ s hn hs
  let n := Fintype.card α
  let m := n / 2
  have hn4 : 4 ≤ n := (le_max_left _ _).trans hn
  have hn₀ : 2 * n₀ + 2 ≤ n := (le_max_right _ _).trans hn
  have hm₀ : n₀ ≤ m := by dsimp [m]; omega
  have hnm : n ≤ 3 * m := by dsimp [m]; omega
  have hnmR : (n : ℝ) ≤ 3 * m := by exact_mod_cast hnm
  have hsq : (n : ℝ)^2 ≤ 9 * (m : ℝ)^2 := by nlinarith
  have hexp : (δ / 9 * n) * n ≤ (δ * m) * m := by
    nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hsq)]
  have hpow : ((2 : ℝ)^(δ / 9 * n))^n ≤ (s.length : ℝ)^n := by
    calc
      _ = (2 : ℝ)^((δ / 9 * n) * n) := (Real.rpow_mul_natCast (by norm_num) _ n).symm
      _ ≤ (2 : ℝ)^((δ * m) * m) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
      _ = ((2 : ℝ)^(δ * m))^m := Real.rpow_mul_natCast (by norm_num) _ m
      _ ≤ (primorial m : ℝ)^m := pow_le_pow_left₀ (Real.rpow_nonneg (by norm_num) _) (hprime m hm₀) _
      _ ≤ (s.length : ℝ)^n := by exact_mod_cast primorial_length_bound hs
  exact le_of_pow_le_pow_left₀ (by omega : n ≠ 0) (by positivity) hpow

end FairDice
