import FairDice.Quadrature

namespace FairDice

open Polynomial

def fallingProduct (N k : ℕ) : ℕ := ∏ a ∈ Finset.range k, (N - a)

def risingProduct (N k : ℕ) : ℕ := ∏ a ∈ Finset.range k, (N + 2 + a)

/-- Equation (3.5), fixing the normalization and the grid-size convention. -/
noncomputable def hahn (N k : ℕ) : ℚ[X] :=
  ∑ a ∈ Finset.range (k + 1),
    C ((-1 : ℚ) ^ a * (k.choose a : ℚ) * ((k + a).choose a : ℚ) /
      (fallingProduct N a : ℚ)) * descPochhammer ℚ a

noncomputable def hahnNorm (N k : ℕ) : ℚ :=
  ∑ i : Fin (N + 1), (hahn N k).eval (i.val : ℚ) ^ 2

noncomputable def hahnIntegral (N k : ℕ) : ℚ :=
  polynomialIntegral N (hahn N k)

noncomputable def hahnWeight (N n : ℕ) (i : Fin (N + 1)) : ℚ :=
  projectionWeight (fun k : Fin (n + 1) => hahn N k.val)
    (fun j : Fin (N + 1) => (j.val : ℚ))
    (fun k => hahnNorm N k.val) (polynomialIntegral N) i

/-- The cited classical input, as hypotheses rather than new Lean axioms.

`orthogonal`, `norm_formula`, and `span` are the standard Hahn identities
cited before Equation (3.6) (Karlin--McGregor, Dette, Koekoek, DLMF).
`zaremba` is the quoted nodal estimate. `wilson_odd` and `wilson_even` are
the quoted Wilson integral estimates, in the paper's normalization.
No positivity of quadrature weights or denominator claim is assumed here. -/
structure HahnExternal : Prop where
  orthogonal : ∀ N n, n ≤ N → ∀ k l : Fin (n + 1),
    ∑ i : Fin (N + 1), (hahn N k.val).eval (i.val : ℚ) *
      (hahn N l.val).eval (i.val : ℚ) =
      if k = l then hahnNorm N k.val else 0
  norm_formula : ∀ N k, k ≤ N →
    hahnNorm N k = ((N + 1 : ℕ) : ℚ) * risingProduct N k /
      (((2 * k + 1 : ℕ) : ℚ) * fallingProduct N k)
  span : ∀ N n, n ≤ N → ∀ p : ℚ[X], p.natDegree ≤ n →
    p ∈ Submodule.span ℚ (Set.range (fun k : Fin (n + 1) => hahn N k.val))
  zaremba : ∀ N k, k * (k + 1) ≤ N → ∀ i : Fin (N + 1),
    |(hahn N k).eval (i.val : ℚ)| ≤ 1
  wilson_odd : ∀ N k, k ≤ N → Odd k → hahnIntegral N k = 0
  wilson_even : ∀ N k, 1 ≤ N → 2 ≤ k → k ≤ N → Even k → (k + 1)^2 ≤ N + 1 →
    0 < -hahnIntegral N k ∧
    -hahnIntegral N k ≤ ((N : ℚ) + 1) / N *
      (1 + ((k : ℚ) - 1) * (k + 2) / (4 * (N - 1 : ℚ)))

@[simp] theorem fallingProduct_zero (N : ℕ) : fallingProduct N 0 = 1 := by
  simp [fallingProduct]

@[simp] theorem risingProduct_zero (N : ℕ) : risingProduct N 0 = 1 := by
  simp [risingProduct]

@[simp] theorem hahn_zero (N : ℕ) : hahn N 0 = 1 := by
  simp [hahn]

@[simp] theorem hahnIntegral_zero (N : ℕ) : hahnIntegral N 0 = N := by
  simp [hahnIntegral]

@[simp] theorem hahnNorm_zero (N : ℕ) : hahnNorm N 0 = N + 1 := by
  simp [hahnNorm]

theorem fallingProduct_pos {N k : ℕ} (hk : k ≤ N) : 0 < fallingProduct N k := by
  apply Finset.prod_pos
  intro a ha
  have := Finset.mem_range.mp ha
  omega

theorem risingProduct_pos (N k : ℕ) : 0 < risingProduct N k := by
  apply Finset.prod_pos
  intro a _
  omega

theorem fallingProduct_le_risingProduct (N k : ℕ) :
    fallingProduct N k ≤ risingProduct N k := by
  apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
  intro a _
  omega

/-- The lower norm bound in Equation (3.7), derived from the cited norm formula. -/
theorem hahnNorm_lower (h : HahnExternal) {N k : ℕ} (hk : k ≤ N) :
    ((N : ℚ) + 1) / (2 * k + 1) ≤ hahnNorm N k := by
  have hA : (0 : ℚ) < fallingProduct N k := by exact_mod_cast fallingProduct_pos hk
  have hAB : (fallingProduct N k : ℚ) ≤ risingProduct N k := by
    exact_mod_cast fallingProduct_le_risingProduct N k
  have hd : (0 : ℚ) < 2 * k + 1 := by positivity
  rw [h.norm_formula N k hk]
  push_cast
  apply (div_le_div_iff₀ hd (mul_pos hd hA)).mpr
  nlinarith [mul_nonneg (show (0 : ℚ) ≤ N + 1 by positivity) (sub_nonneg.mpr hAB)]

theorem hahnNorm_pos (h : HahnExternal) {N k : ℕ} (hk : k ≤ N) :
    0 < hahnNorm N k :=
  lt_of_lt_of_le (div_pos (by positivity) (by positivity)) (hahnNorm_lower h hk)

/-- Exactness in Proposition 3.4, conditional only on the classical Hahn facts. -/
theorem hahnWeight_exact (h : HahnExternal) {N n : ℕ} (hn : n ≤ N)
    (p : ℚ[X]) (hp : p.natDegree ≤ n) :
    ∑ i : Fin (N + 1), hahnWeight N n i * p.eval (i.val : ℚ) =
      polynomialIntegral N p := by
  apply projection_exact_span
  · intro k
    exact ne_of_gt (hahnNorm_pos h (by omega))
  · exact h.orthogonal N n hn
  · exact h.span N n hn p hp

theorem hahnWeight_sum (h : HahnExternal) {N n : ℕ} (hn : n ≤ N) :
    ∑ i : Fin (N + 1), hahnWeight N n i = N := by
  simpa using hahnWeight_exact h hn 1 (by simp)

end FairDice
