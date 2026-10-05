import FairDice.FiniteLp
import FairDice.PalindromeBlocks
import FairDice.Symmetrization

namespace FairDice

noncomputable def finiteEventMass {Ω : Type*} [Fintype Ω] (P : Ω → Prop) : ℝ := by
  classical
  exact finiteMean (fun x => if P x then 1 else 0)

variable {Ω : Type*} [Fintype Ω]

theorem finiteEventMass_nonneg (P : Ω → Prop) : 0 ≤ finiteEventMass P := by
  classical
  unfold finiteEventMass
  exact finiteMean_nonneg _ (fun x => by split <;> norm_num)

/-- Markov's inequality proved directly for the uniform finite space. -/
theorem finite_markov {p ε : ℝ} (hp : 0 < p) (hε : 0 < ε) (f : Ω → ℝ) :
    finiteEventMass (fun x => ε ≤ |f x|) ≤
      finiteMean (fun x => |f x|^p) / ε^p := by
  classical
  have hpow : 0 < ε^p := Real.rpow_pos_of_pos hε p
  have hh : ∀ x, (if ε ≤ |f x| then (1 : ℝ) else 0) ≤ |f x|^p / ε^p := by
    intro x
    split_ifs with hx
    · apply (le_div_iff₀ hpow).mpr
      simpa using Real.rpow_le_rpow hε.le hx hp.le
    · exact div_nonneg (Real.rpow_nonneg (abs_nonneg _) _) hpow.le
  have h := finiteMean_mono hh
  simpa [finiteEventMass, div_eq_mul_inv, finiteMean_mul_const] using h

theorem finite_event_union {ι : Type*} [Fintype ι] (P : ι → Ω → Prop) :
    finiteEventMass (fun x => ∃ i, P i x) ≤ ∑ i, finiteEventMass (P i) := by
  classical
  have hh (x : Ω) : (if ∃ i, P i x then (1 : ℝ) else 0) ≤
      ∑ i, if P i x then (1 : ℝ) else 0 := by
    split_ifs with hx
    · obtain ⟨i,hi⟩ := hx
      have h := Finset.single_le_sum (f := fun i => if P i x then (1 : ℝ) else 0)
        (fun j _ => by split <;> norm_num) (Finset.mem_univ i)
      simpa [hi] using h
    · exact Finset.sum_nonneg (fun i _ => by split <;> norm_num)
  calc
    _ = finiteMean (fun x => if ∃ i, P i x then (1 : ℝ) else 0) := by
      unfold finiteEventMass
      congr 1
      funext x
      by_cases hx : ∃ i, P i x <;> simp [hx]
    _ ≤ finiteMean (fun x => ∑ i, if P i x then (1 : ℝ) else 0) := finiteMean_mono hh
    _ = ∑ i, finiteEventMass (P i) := by
      rw [finiteMean_sum Finset.univ (fun i x => if P i x then (1 : ℝ) else 0)]
      apply Finset.sum_congr rfl
      intro i _
      unfold finiteEventMass
      rfl

theorem finite_good_point [Nonempty Ω] (P : Ω → Prop) (h : finiteEventMass P < 1) :
    ∃ x, ¬ P x := by
  classical
  by_contra hn
  have hall : ∀ x, P x := by simpa using hn
  have he : finiteEventMass P = 1 := by simp [finiteEventMass, hall]
  linarith

/-- A `1/3` moment margin yields the exact `3^(-p)` tail used in the paper. -/
theorem finiteLp_one_third_tail {p ε : ℝ} (hp : 0 < p) (hε : 0 < ε) (f : Ω → ℝ)
    (hf : finiteLp p f ≤ ε/3) :
    finiteEventMass (fun x => ε ≤ |f x|) ≤ (1/3 : ℝ)^p := by
  have hh := Real.rpow_le_rpow (finiteLp_nonneg p f) hf hp.le
  rw [finiteLp_pow hp] at hh
  calc
    _ ≤ finiteMean (fun x => |f x|^p)/ε^p := finite_markov hp hε f
    _ ≤ (ε/3)^p/ε^p := div_le_div_of_nonneg_right hh (Real.rpow_nonneg hε.le _)
    _ = (1/3 : ℝ)^p := by
      rw [Real.div_rpow hε.le (by norm_num) p]
      have he : ε^p ≠ 0 := (Real.rpow_pos_of_pos hε p).ne'
      rw [Real.div_rpow (by norm_num : (0 : ℝ) ≤ 1) (by norm_num) p, Real.one_rpow]
      field_simp

noncomputable def palindromeRelativeError {n m : ℕ}
    (ρ : Fin m → Equiv.Perm (Fin n)) (σ : Equiv.Perm (Fin n)) : ℝ :=
  (n.factorial : ℝ) * (patternProbability (palindromeWord ρ) ((List.finRange n).map σ) : ℝ) - 1

/-- The Markov/union-bound conclusion for the actual palindrome word. The
new moment estimate is a visible hypothesis, not an external premise. -/
theorem palindrome_good_probability_of_moments {n m : ℕ} {p ε : ℝ}
    (hp : 0 < p) (hε : 0 < ε)
    (hmoment : ∀ σ : Equiv.Perm (Fin n),
      finiteLp p (fun ρ : Fin m → Equiv.Perm (Fin n) => palindromeRelativeError ρ σ) ≤ ε/3)
    (hcard : (n.factorial : ℝ)*(1/3 : ℝ)^p ≤ 1/2) :
    finiteEventMass (fun ρ : Fin m → Equiv.Perm (Fin n) =>
      ∃ σ : Equiv.Perm (Fin n), ε ≤ |palindromeRelativeError ρ σ|) ≤ 1/2 ∧
    ∃ ρ : Fin m → Equiv.Perm (Fin n), ∀ q : List (Fin n), q.Nodup → q.length = n →
      |(patternProbability (palindromeWord ρ) q : ℝ) - 1/(n.factorial : ℝ)| ≤ ε/(n.factorial : ℝ) := by
  have hbad : finiteEventMass (fun ρ : Fin m → Equiv.Perm (Fin n) =>
      ∃ σ : Equiv.Perm (Fin n), ε ≤ |palindromeRelativeError ρ σ|) ≤ 1/2 := by
    apply (finite_event_union _).trans
    apply (Finset.sum_le_sum (fun σ _ => finiteLp_one_third_tail hp hε _ (hmoment σ))).trans
    simpa [Fintype.card_perm] using hcard
  refine ⟨hbad, ?_⟩
  obtain ⟨ρ,hρ⟩ := finite_good_point _ (hbad.trans_lt (by norm_num))
  refine ⟨ρ, fun q hq hlen => ?_⟩
  obtain ⟨σ,hσ⟩ := exists_relabel (List.finRange n) q (List.nodup_finRange n) hq (by simpa using hlen.symm)
  have he : |palindromeRelativeError ρ σ| < ε := lt_of_not_ge (fun h => hρ ⟨σ,h⟩)
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  rw [← hσ]
  have hid : (patternProbability (palindromeWord ρ) ((List.finRange n).map σ) : ℝ) -
      1/(n.factorial : ℝ) = palindromeRelativeError ρ σ / (n.factorial : ℝ) := by
    unfold palindromeRelativeError
    field_simp
  rw [hid, abs_div, abs_of_pos hf]
  exact div_le_div_of_nonneg_right he.le hf.le

end FairDice
