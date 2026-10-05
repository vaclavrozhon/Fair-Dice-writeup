import FairDice.MonotoneMoments

namespace FairDice

open Polynomial

/-- A positive real quadrature rule for the uniform unit interval. -/
structure RealQuadrature (N degree : ℕ) where
  node : Fin N → ℝ
  weight : Fin N → ℝ
  weight_pos : ∀ i, 0 < weight i
  exactness : ∀ p : ℝ[X], p.natDegree ≤ degree →
    ∑ i, weight i * p.eval (node i) = realPolynomialIntegral p

structure GaussianData (d : ℕ) extends RealQuadrature (d + 1) (2 * d + 1) where
  increasing : StrictMono node
  interior : ∀ i, 0 < node i ∧ node i < 1
  /-- Classical Legendre/Jacobi-matrix comparison with the constant
  off-diagonal matrix whose largest eigenvalue is `cos (π/(D+1))`. -/
  cosine_bound : (1 + Real.cos (Real.pi / (d + 2))) / 2 ≤ node (Fin.last d)

structure RadauData (e : ℕ) extends RealQuadrature (e + 1) (2 * e) where
  increasing : StrictMono node
  interior : ∀ i : Fin e, 0 < node i.castSucc ∧ node i.castSucc < 1
  endpoint : node (Fin.last e) = 1
  endpoint_weight : weight (Fin.last e) = 1 / ((e + 1 : ℕ) : ℝ)^2
  reciprocal_sum : (∑ i : Fin e, 1 / (1 - node i.castSucc)) =
    (e : ℝ) * (e + 2) / 2

/-- The classical univariate Gaussian/Radau facts used in the paper.
There are no assumptions about dice, monotone mixed moments, the last-row
bound, or the prescribed-size construction. -/
def ClassicalQuadratureExternal : Prop :=
  (∀ d : ℕ, Nonempty (GaussianData d)) ∧ (∀ e : ℕ, Nonempty (RadauData e))

/-- The Gaussian endpoint estimate in `individual-gaussian-edge`, derived
from the classical Jacobi comparison and the cosine inequality in mathlib. -/
theorem GaussianData.edge_bound {d : ℕ} (G : GaussianData d) :
    1 - G.node (Fin.last d) ≤ Real.pi^2 / (4 * (d + 2 : ℝ)^2) := by
  have hc := Real.one_sub_sq_div_two_le_cos (x := Real.pi / (d + 2 : ℝ))
  have hden : (0 : ℝ) < d + 2 := by positivity
  have hbound := G.cosine_bound
  have he : (Real.pi / (d + 2 : ℝ))^2 / 2 = Real.pi^2 / (2 * (d + 2 : ℝ)^2) := by
    field_simp
  rw [he] at hc
  have htwo : Real.pi^2 / (2 * (d + 2 : ℝ)^2) =
      2 * (Real.pi^2 / (4 * (d + 2 : ℝ)^2)) := by field_simp; norm_num
  rw [htwo] at hc
  linarith

end FairDice
