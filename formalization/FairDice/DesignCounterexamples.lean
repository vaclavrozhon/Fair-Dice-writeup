import FairDice.RationalDesigns
import FairDice.Elementary

namespace FairDice

/-- Conjecture 4.3, with all asymptotic quantifiers explicit. -/
def EveryDieExponential : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ (α : Type) [DecidableEq α] [Fintype α]
    (s : List α), n₀ ≤ Fintype.card α → PermutationFair s →
    ∀ a : α, (2 : ℝ)^(c * Fintype.card α) ≤ s.count a

/-- Subexponential designs in unbounded degrees, in the exponential-inequality
form used by the corollary. -/
def SubexponentialRationalDesigns : Prop :=
  ∀ c : ℝ, 0 < c → ∀ r₀ : ℕ, ∃ r ≥ r₀, ∃ K : ℕ,
    0 < K ∧ (K : ℝ) < (2 : ℝ)^(c * r) ∧ Nonempty (RationalDesign K r)

/-- Corollary 4.6: the rational-design hypothesis refutes the per-die
exponential conjecture. This theorem does not assert that such designs exist. -/
theorem rational_design_counterexamples (h : SubexponentialRationalDesigns) :
    ¬ EveryDieExponential := by
  rintro ⟨c, hc, n₀, hall⟩
  obtain ⟨r, hr, K, hK, hsmall, ⟨D⟩⟩ := h c hc (max n₀ 1)
  have hrpos : 0 < r := by omega
  have hs := (elementary_construction r hrpos).1
  have D' : RationalDesign K (Fintype.card (Fin r)) := by simpa using D
  obtain ⟨N, _, t, ht, hnew, _⟩ := rational_design_insertion hK D' hs
  have hl := hall (Option (Fin r)) t (by simp; omega) ht none
  simp only [Fintype.card_option, Fintype.card_fin] at hl
  rw [hnew] at hl
  have he : (2 : ℝ)^(c * r) ≤ (2 : ℝ)^(c * (r + 1 : ℕ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    push_cast
    nlinarith
  exact (hsmall.trans_le (he.trans hl)).false

/-- The logarithmic sequence formulation of Corollary 4.6. Unboundedness is
required on every tail, so no monotonicity of the sequence is assumed. -/
theorem rational_design_sequence_counterexample (r K : ℕ → ℕ)
    (hunbounded : ∀ r₀ ν₀ : ℕ, ∃ ν ≥ ν₀, r₀ ≤ r ν)
    (hK : ∀ ν, 0 < K ν) (hD : ∀ ν, Nonempty (RationalDesign (K ν) (r ν)))
    (hlog : Filter.Tendsto (fun ν => Real.log (K ν) / r ν)
      Filter.atTop (nhds 0)) : ¬ EveryDieExponential := by
  apply rational_design_counterexamples
  intro c hc r₀
  have hcL : 0 < c * Real.log 2 := mul_pos hc (Real.log_pos (by norm_num))
  have hev : ∀ᶠ ν in Filter.atTop, Real.log (K ν) / r ν < c * Real.log 2 :=
    hlog.eventually (gt_mem_nhds hcL)
  obtain ⟨ν₀, hν₀⟩ := Filter.eventually_atTop.mp hev
  obtain ⟨ν, hν, hr⟩ := hunbounded (max r₀ 1) ν₀
  have hrR : (0 : ℝ) < r ν := by exact_mod_cast (show 0 < r ν by omega)
  have hlogsmall := (div_lt_iff₀ hrR).mp (hν₀ ν hν)
  have hKR : (0 : ℝ) < K ν := by exact_mod_cast hK ν
  refine ⟨r ν, by omega, K ν, hK ν, ?_, hD ν⟩
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
  apply (Real.log_lt_iff_lt_exp hKR).mp
  nlinarith

end FairDice
