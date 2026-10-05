import FairDice.InsertionFairness
import FairDice.Bernstein
import FairDice.Denominators

namespace FairDice

open Polynomial

theorem rational_nodes_common_grid {ι : Type*} [Fintype ι] (x : ι → ℚ)
    (hx : ∀ i, 0 ≤ x i ∧ x i ≤ 1) :
    ∃ N : ℕ, 0 < N ∧ ∃ a : ι → Fin (N + 1), ∀ i, (a i).val = (N : ℚ) * x i := by
  classical
  let N := ∏ i, (x i).den
  have hN : 0 < N := Finset.prod_pos (fun i _ => Rat.den_pos (x i))
  have hc (i : ι) : Clears N (x i) := by
    apply Clears.of_dvd (d := (x i).den) _
      (Finset.dvd_prod_of_mem (fun j : ι => (x j).den) (Finset.mem_univ i))
    refine ⟨(x i).num, ?_⟩
    have hq := Rat.num_div_den (x i)
    have hden : ((x i).den : ℚ) ≠ 0 := by exact_mod_cast (x i).den_ne_zero
    calc
      _ = ((x i).den : ℚ) * ((x i).num / (x i).den) := by rw [hq]
      _ = _ := by field_simp
  have hi (i : ι) : ∃ a : Fin (N + 1), (a.val : ℚ) = (N : ℚ) * x i := by
    obtain ⟨z, hz⟩ := hc i
    have hz0 : 0 ≤ z := by
      exact_mod_cast (hz ▸ mul_nonneg (show (0 : ℚ) ≤ N by positivity) (hx i).1)
    have hzN : z ≤ (N : ℤ) := by
      have hb := mul_le_mul_of_nonneg_left (hx i).2 (show (0 : ℚ) ≤ N by positivity)
      rw [hz, mul_one] at hb
      exact_mod_cast hb
    refine ⟨⟨z.toNat, by omega⟩, ?_⟩
    have he : ((z.toNat : ℤ) : ℚ) = (z : ℚ) := by rw [Int.toNat_of_nonneg hz0]
    exact he.trans hz.symm
  choose a ha using hi
  exact ⟨N, hN, a, ha⟩

theorem polynomialIntegral_scale_up (N : ℚ) (hN : N ≠ 0) (p : ℚ[X]) :
    polynomialIntegral 1 (p.comp (C N * X)) = polynomialIntegral N p / N := by
  have hscale := polynomialIntegral_scale N hN (p.comp (C N * X))
  have hcomp : (C N * X : ℚ[X]).comp (C N⁻¹ * X) = X := by
    rw [mul_comp, C_comp, X_comp, ← mul_assoc, ← C_mul]
    simp [hN]
  rw [comp_assoc, hcomp, comp_X] at hscale
  apply (eq_div_iff hN).mpr
  nlinarith

def nodeMultiplicity {K N : ℕ} (a : Fin K → Fin (N + 1)) (i : Fin (N + 1)) : ℕ :=
  (Finset.univ.filter (fun j => a j = i)).card

theorem nodeMultiplicity_sum {K N : ℕ} (a : Fin K → Fin (N + 1)) :
    ∑ i, nodeMultiplicity a i = K := by
  classical
  symm
  simpa [nodeMultiplicity] using Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (Fin K))) (t := Finset.univ) (f := a)
    (fun _ _ => Finset.mem_univ _)

theorem nodeMultiplicity_weighted_sum {K N : ℕ} (a : Fin K → Fin (N + 1))
    (f : Fin (N + 1) → ℚ) : ∑ i, (nodeMultiplicity a i : ℚ) * f i = ∑ j, f (a j) := by
  classical
  calc
    _ = ∑ i : Fin (N + 1), ∑ j : Fin K, if a j = i then f i else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      simp [nodeMultiplicity, ← Finset.sum_filter]
    _ = _ := by rw [Finset.sum_comm]; simp

/-- A rational equal-weight design on the unit interval. The moment equation
is written without division by `K`; `K > 0` is required by the insertion theorem. -/
structure RationalDesign (K r : ℕ) where
  node : Fin K → ℚ
  in_unit : ∀ i, 0 ≤ node i ∧ node i ≤ 1
  exactness : ∀ p : ℚ[X], p.natDegree ≤ r →
    ∑ i : Fin K, p.eval (node i) = K * polynomialIntegral 1 p

variable {α : Type*} [DecidableEq α] [Fintype α]
local instance instBEqOptionRationalDesigns : BEq (Option α) := instBEqOfDecidableEq

/-- Proposition 4.5: rational equal-weight quadrature yields one new die
with exactly `K` faces, while multiplying all old face counts by a common `N`. -/
theorem rational_design_insertion_on_grid {K : ℕ} (hK : 0 < K)
    (D : RationalDesign K (Fintype.card α)) {s : List α} (hs : PermutationFair s)
    (N : ℕ) (hN : 0 < N) (a : Fin K → Fin (N + 1))
    (ha : ∀ l, ((a l).val : ℚ) = (N : ℚ) * D.node l) :
    ∃ t : List (Option α), PermutationFair t ∧
      t.count none = K ∧ ∀ a : α, t.count (some a) = N * s.count a := by
  let k := nodeMultiplicity a
  have hsum : ∑ i, k i = K := nodeMultiplicity_sum a
  refine ⟨insertGaps s N k, ?_, ?_, ?_⟩
  · apply insertion_fair_general hs N hN k (by rwa [hsum])
      ((K : ℚ) * (N : ℚ)^(Fintype.card α) / (Fintype.card α + 1).factorial)
    intro j hj
    let p := rankPolynomial (N : ℚ) (Fintype.card α) j
    have hp : (p.comp (C (N : ℚ) * X)).natDegree ≤ Fintype.card α := by
      rw [natDegree_comp]
      have hdeg : (C (N : ℚ) * X).natDegree ≤ 1 := by simpa using natDegree_C_mul_le (N : ℚ) X
      exact (Nat.mul_le_mul (rankPolynomial_degree N hj) hdeg).trans (by omega)
    have hdesign := D.exactness (p.comp (C (N : ℚ) * X)) hp
    have hNq : (N : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
    rw [polynomialIntegral_scale_up N hNq,
      polynomialIntegral_rank N hNq hj] at hdesign
    calc
      _ = ∑ i : Fin (N + 1), (k i : ℚ) * p.eval (i.val : ℚ) := by
        apply Finset.sum_congr rfl
        intro i _
        simp only [p, rankPolynomial_eval]
        ring
      _ = ∑ l : Fin K, p.eval ((a l).val : ℚ) := nodeMultiplicity_weighted_sum a _
      _ = ∑ l : Fin K, (p.comp (C (N : ℚ) * X)).eval (D.node l) := by
        apply Finset.sum_congr rfl
        intro l _
        simp only [eval_comp, eval_mul, eval_C, eval_X, ha]
      _ = _ := by rw [hdesign, pow_succ]; field_simp
  · rw [insertGaps_new_multiplicity, hsum]
  · exact insertGaps_old_multiplicity s N k

theorem rational_design_insertion {K : ℕ} (hK : 0 < K)
    (D : RationalDesign K (Fintype.card α)) {s : List α} (hs : PermutationFair s) :
    ∃ N : ℕ, 0 < N ∧ ∃ t : List (Option α), PermutationFair t ∧
      t.count none = K ∧ ∀ a : α, t.count (some a) = N * s.count a := by
  obtain ⟨N, hN, a, ha⟩ := rational_nodes_common_grid D.node D.in_unit
  exact ⟨N, hN, rational_design_insertion_on_grid hK D hs N hN a ha⟩

end FairDice
