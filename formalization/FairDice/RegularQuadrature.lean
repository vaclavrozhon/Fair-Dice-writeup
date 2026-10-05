import FairDice.RegularPerturbation
import FairDice.CorrectedFamily

namespace FairDice

open Polynomial

/-- Every positive-cardinality starting quadrature of degree `2m+2`
can be made distinct and interior at the same cardinality, retaining
exactness through degree `m`. This is the article's own regularization. -/
theorem regularize_real_rule {m K : ℕ} (hK : 0<K)
    (Q : EqualWeightRealRule K (2*m+2)) :
    ∃ R : EqualWeightRealRule K m, Function.Injective R.node ∧
      ∀ q, 0<R.node q ∧ R.node q<1 := by
  obtain ⟨e,he,hpiv⟩ := real_rule_pivots hK Q
  obtain ⟨w,hw,hunit,hmom⟩ := regular_moment_perturbation hK e Q.node he hpiv Q.in_unit
  have hKr : (K : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hK
  have hexact (p : ℝ[X]) (hp : p.natDegree ≤ m) :
      (∑ q, p.eval (w q)) = K*realPolynomialIntegral p := by
    let L : ℝ[X] →ₗ[ℝ] ℝ := ∑ q, Polynomial.leval (w q)
    let B : ℝ[X] →ₗ[ℝ] ℝ := (K : ℝ) • realPolynomialIntegral
    suffices hh : L p = B p by simpa [L,B] using hh
    apply polynomial_functionals_ext L B m ?_ p hp
    intro s hs
    cases s with
    | zero => simp [L,B]
    | succ s =>
      have hh := congrFun hmom (⟨s,by omega⟩ : Fin m)
      change (∑ q, w q^(s+1))/(K : ℝ)=(∑ q, Q.node q^(s+1))/(K : ℝ) at hh
      have hsums := (div_left_inj' hKr).mp hh
      have hQ := Q.exactness (X^(s+1)) (by simp; omega)
      simp only [eval_pow, eval_X] at hQ
      simpa [L,B,eval_pow,eval_X] using hsums.trans hQ
  exact ⟨⟨w,fun q => ⟨(hunit q).1.le,(hunit q).2.le⟩,hexact⟩,hw,hunit⟩

/-- The cited Gilboa--Peled input, restricted to constant weight. Nodes
may repeat and may be endpoints; the regularity conclusion is proved above.
The threshold applies to *every* sufficiently large cardinality. -/
def GilboaPeledExternal : Prop :=
  ∃ C : ℕ, 0 < C ∧ ∀ d K : ℕ, 0 < d → C*d^2 ≤ K →
    Nonempty (EqualWeightRealRule K d)

/-- `individual-real-rule`, including the quadratic cardinality threshold
and the reserve `K >= m^2` needed for disjoint corrections. -/
theorem regular_starting_quadrature (H : GilboaPeledExternal) :
    ∃ C₀ : ℕ, 0 < C₀ ∧ ∀ m K : ℕ, 0 < m → C₀*(m+1)^2 ≤ K →
      m^2 ≤ K ∧ ∃ Q : EqualWeightRealRule K m, Function.Injective Q.node ∧
        ∀ q, 0<Q.node q ∧ Q.node q<1 := by
  obtain ⟨C,hC,hGP⟩ := H
  refine ⟨4*C,by omega,fun m K hm hsize => ?_⟩
  have hdeg : C*(2*m+2)^2 ≤ K := by nlinarith
  have hK : 0<K := by nlinarith
  obtain ⟨Q⟩ := hGP (2*m+2) K (by omega) hdeg
  refine ⟨by nlinarith,regularize_real_rule hK Q⟩

/-- The entire positive rational density family is now obtained from the
classical quadrature threshold, with no regularity premise remaining. -/
theorem prescribed_density_family (H : GilboaPeledExternal) :
    ∃ C₀ : ℕ, 0 < C₀ ∧ ∀ m K : ℕ, 0 < m → C₀*(m+1)^2 ≤ K →
      Nonempty (CorrectedFamily m K) := by
  obtain ⟨C₀,hC,hreg⟩ := regular_starting_quadrature H
  refine ⟨C₀,hC,fun m K hm hsize => ?_⟩
  obtain ⟨hsize',Q,hQ,hunit⟩ := hreg m K hm hsize
  have hK : 0<K := by nlinarith
  exact corrected_family_exists hm hK hsize' Q hQ hunit

end FairDice
