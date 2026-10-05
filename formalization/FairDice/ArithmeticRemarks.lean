import FairDice.Hereditary
import FairDice.ExponentialLowerBound

namespace FairDice

variable {α : Type*} [DecidableEq α] [Fintype α]

/-- All subset-factorial tests admit the vector `(1,n!,...,n!)`.
This is an arithmetic example, not an assertion that such dice exist. -/
theorem factorial_constraints_allow_one (a : α) (S : Finset α) :
    S.card.factorial ∣ ∏ b ∈ S, if b = a then 1 else (Fintype.card α).factorial := by
  classical
  by_cases hsmall : S.card ≤ 1
  · have hf : S.card.factorial = 1 := by
      interval_cases h : S.card <;> simp
    simp [hf]
  · have hex : ∃ b ∈ S, b ≠ a := by
      by_contra h
      have hsub : S ⊆ {a} := by
        intro b hb
        apply Finset.mem_singleton.mpr
        by_contra hba
        exact h ⟨b, hb, hba⟩
      have := Finset.card_le_card hsub
      simp at this
      omega
    obtain ⟨b, hb, hba⟩ := hex
    have hd := Finset.dvd_prod_of_mem (fun b : α =>
      if b = a then 1 else (Fintype.card α).factorial) hb
    rw [if_neg hba] at hd
    exact (Nat.factorial_dvd_factorial (Finset.card_le_univ S)).trans hd

/-- `primorial n` is the product of the distinct prime factors of `n!`,
usually written `rad(n!)` in the paper. -/
theorem hereditary_equal_primorial_dvd {s : List α} (hs : HereditaryGoFirstFair s)
    (m : ℕ) (hm : ∀ a, s.count a = m) : primorial (Fintype.card α) ∣ m := by
  classical
  apply Finset.prod_primes_dvd
  · intro p hp
    exact (Finset.mem_filter.mp hp).2.prime
  · intro p hp
    have hp' := (Finset.mem_filter.mp hp).2
    have hpn : p ≤ Fintype.card α := by
      have := Finset.mem_range.mp (Finset.mem_filter.mp hp).1
      omega
    by_contra hd
    have hf : ((Finset.univ : Finset α).filter (fun a => ¬p ∣ s.count a)) = Finset.univ := by
      ext a
      simp [hm, hd]
    have hh := hereditary_few_not_dvd hs p hp'
    rw [hf, Finset.card_univ] at hh
    omega

theorem hereditary_primorial_face_bound {s : List α} (hs : HereditaryGoFirstFair s) :
    (primorial (Fintype.card α / 2))^(Fintype.card α / 2) ≤ outcomeCount s := by
  classical
  let n := Fintype.card α
  let P := (Finset.range (n + 1)).filter Nat.Prime
  let Q := (Finset.range (n / 2 + 1)).filter Nat.Prime
  have hQP : Q ⊆ P := by
    intro p hp
    simp only [Q, P, Finset.mem_filter, Finset.mem_range] at hp ⊢
    exact ⟨by omega, hp.2⟩
  calc
    _ = ∏ p ∈ Q, p^(n / 2) := (Finset.prod_pow Q (n / 2) id).symm
    _ ≤ ∏ p ∈ Q, p^(n + 1 - p) := by
      apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
      intro p hp
      have hp' := Finset.mem_range.mp (Finset.mem_filter.mp hp).1
      exact Nat.pow_le_pow_right (Finset.mem_filter.mp hp).2.pos (by omega)
    _ ≤ ∏ p ∈ P, p^(n + 1 - p) := by
      exact Finset.prod_le_prod_of_subset_of_one_le hQP
        (fun _ _ => Nat.zero_le _)
        (fun p hp _ => Nat.one_le_pow _ _ (Finset.mem_filter.mp hp).2.pos)
    _ ≤ outcomeCount s := hereditary_prime_product hs

/-- Isolate the numerical use of the cited primorial estimate, so it can
also be applied to the maximum face count for hereditary fairness. -/
theorem exponential_of_primorial_power (hext : PrimorialExternal) :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n B : ℕ, n₀ ≤ n →
      (primorial (n / 2))^(n / 2) ≤ B^n → (2 : ℝ)^(c * n) ≤ B := by
  obtain ⟨δ, hδ, n₀, hprime⟩ := hext
  refine ⟨δ / 9, by positivity, max 4 (2 * n₀ + 2), ?_⟩
  intro n B hn hB
  let m := n / 2
  have hn4 : 4 ≤ n := (le_max_left _ _).trans hn
  have hn₀ : 2 * n₀ + 2 ≤ n := (le_max_right _ _).trans hn
  have hm₀ : n₀ ≤ m := by dsimp [m]; omega
  have hnm : n ≤ 3 * m := by dsimp [m]; omega
  have hnmR : (n : ℝ) ≤ 3 * m := by exact_mod_cast hnm
  have hsq : (n : ℝ)^2 ≤ 9 * (m : ℝ)^2 := by nlinarith
  have hexp : (δ / 9 * n) * n ≤ (δ * m) * m := by
    nlinarith [mul_nonneg hδ.le (sub_nonneg.mpr hsq)]
  have hpow : ((2 : ℝ)^(δ / 9 * n))^n ≤ (B : ℝ)^n := by
    calc
      _ = (2 : ℝ)^((δ / 9 * n) * n) := (Real.rpow_mul_natCast (by norm_num) _ n).symm
      _ ≤ (2 : ℝ)^((δ * m) * m) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
      _ = ((2 : ℝ)^(δ * m))^m := Real.rpow_mul_natCast (by norm_num) _ m
      _ ≤ (primorial m : ℝ)^m := pow_le_pow_left₀ (Real.rpow_nonneg (by norm_num) _) (hprime m hm₀) _
      _ ≤ (B : ℝ)^n := by exact_mod_cast hB
  exact le_of_pow_le_pow_left₀ (by omega : n ≠ 0) (by positivity) hpow

theorem hereditary_exponentially_large_die (hext : PrimorialExternal) :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ (α : Type) [DecidableEq α] [Fintype α]
      (s : List α), n₀ ≤ Fintype.card α → HereditaryGoFirstFair s →
      ∃ a : α, (2 : ℝ)^(c * Fintype.card α) ≤ s.count a := by
  obtain ⟨c, hc, n₀, hbound⟩ := exponential_of_primorial_power hext
  refine ⟨c, hc, max 1 n₀, ?_⟩
  intro α _ _ s hn hs
  classical
  have hnpos : 0 < Fintype.card α := by omega
  letI : Nonempty α := Fintype.card_pos_iff.mp hnpos
  obtain ⟨a, _, ha⟩ := Finset.exists_max_image (Finset.univ : Finset α)
    (fun a => s.count a) Finset.univ_nonempty
  refine ⟨a, hbound _ _ (by omega) ?_⟩
  apply (hereditary_primorial_face_bound hs).trans
  simpa [outcomeCount] using Finset.prod_le_pow_card (Finset.univ : Finset α)
    (fun b => s.count b) (s.count a) (fun b hb => ha b hb)

end FairDice
