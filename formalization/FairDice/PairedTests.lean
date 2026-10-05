import FairDice.IntervalRules

namespace FairDice

open Polynomial

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : ℕ}

theorem MonotoneMoments.injective_shifted_identity (A : MonotoneMoments ι K)
    {η : Type*} [Fintype η] [DecidableEq η] (e : η ↪ ι) (b : η → ℝ) :
    (∑ q, A.weight q * ∏ i : η, (A.row q (e i) - b i)) =
      realPolynomialIntegral (∏ i : η, (X - C (b i))) := by
  classical
  rcases isEmpty_or_nonempty η with hη | hη
  · letI := hη
    simpa using A.weight_sum
  · letI := hη
    let S := Finset.univ.map e
    let c : ι → ℝ := fun i => b (Function.invFun e i)
    have hbi (i : η) : c (e i) = b i := by
      dsimp [c]
      rw [Function.leftInverse_invFun e.injective i]
    have h := A.shifted_identity S c
    simpa only [S, shiftedTest, Finset.prod_map, hbi] using h

theorem MonotoneMoments.extra_coordinate_identity (A : MonotoneMoments ι K)
    {η : Type*} [Fintype η] [DecidableEq η] (e : η ↪ ι) (b : η → ℝ)
    (i : ι) (hi : ∀ j, e j ≠ i) (a : ℝ) :
    (∑ q, A.weight q * (a - A.row q i) * ∏ j : η, (A.row q (e j) - b j)) =
      realPolynomialIntegral ((C a - X) * ∏ j : η, (X - C (b j))) := by
  classical
  let e' : Option η ↪ ι :=
    ⟨fun j => j.elim i e, by
      intro j k h
      cases j with
      | none =>
        cases k with
        | none => rfl
        | some k => exact False.elim (hi k h.symm)
      | some j =>
        cases k with
        | none => exact False.elim (hi j h)
        | some k => exact congrArg some (e.injective h)⟩
  let b' : Option η → ℝ := fun j => j.elim a b
  have h := A.injective_shifted_identity e' b'
  simp only [Fintype.prod_option, e', b', Function.Embedding.coeFn_mk, Option.elim_none,
    Option.elim_some] at h
  have hh := congrArg Neg.neg h
  rw [← map_neg] at hh
  convert hh using 1
  · simp only [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro q _
    ring
  · congr 1
    ring

/-- All coordinates in a product test are distinct, grouped into pairs. -/
structure PairedTest (ι : Type*) (d : ℕ) where
  index : (Fin d × Fin 2) ↪ ι
  threshold : Fin d × Fin 2 → ℝ

noncomputable def PairedTest.polynomial {d : ℕ} (T : PairedTest ι d) : ℝ[X] :=
  ∏ j : Fin d × Fin 2, (X - C (T.threshold j))

noncomputable def PairedTest.value {d : ℕ} (T : PairedTest ι d) (x : ι → ℝ) : ℝ :=
  ∏ j : Fin d × Fin 2, (x (T.index j) - T.threshold j)

omit [Fintype ι] [DecidableEq ι] in
theorem PairedTest.eval {d : ℕ} (T : PairedTest ι d) (x : ℝ) :
    T.polynomial.eval x = ∏ j : Fin d × Fin 2, (x - T.threshold j) := by
  simp [PairedTest.polynomial, Polynomial.eval_prod]

omit [Fintype ι] [DecidableEq ι] in
theorem PairedTest.degree {d : ℕ} (T : PairedTest ι d) :
    T.polynomial.natDegree ≤ 2 * d := by
  apply (natDegree_prod_le Finset.univ _).trans
  have hh := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin d × Fin 2)))
    (fun j _ => (natDegree_sub_le (X : ℝ[X]) (C (T.threshold j))).trans
      (max_le (by simp) (by simp) : max X.natDegree (C (T.threshold j)).natDegree ≤ 1))
  simp_all [Fintype.card_prod, Nat.mul_comm]

theorem PairedTest.identity {d : ℕ} (T : PairedTest ι d) (A : MonotoneMoments ι K) :
    (∑ q, A.weight q * T.value (A.row q)) = realPolynomialIntegral T.polynomial :=
  A.injective_shifted_identity T.index T.threshold

theorem PairedTest.extra_identity {d : ℕ} (T : PairedTest ι d) (A : MonotoneMoments ι K)
    (i : ι) (hi : ∀ j, T.index j ≠ i) (a : ℝ) :
    (∑ q, A.weight q * (a - A.row q i) * T.value (A.row q)) =
      realPolynomialIntegral ((C a - X) * T.polynomial) :=
  A.extra_coordinate_identity T.index T.threshold i hi a

omit [DecidableEq ι] in
theorem exists_paired_test (A : MonotoneMoments ι K) {d : ℕ}
    (idx : (Fin d × Fin 2) ↪ ι) (t : Fin d → ℝ) (ht : ∀ l, 0 < t l) :
    ∃ T : PairedTest ι d, T.index = idx ∧
      (∀ l j, 0 ≤ T.threshold (l, j) ∧ T.threshold (l, j) ≤ t l) ∧
      (∀ l, T.threshold (l, 0) = t l ∨ T.threshold (l, 1) = t l) ∧
      (∀ q, 0 ≤ T.value (A.row q)) := by
  classical
  have hex (l : Fin d) := paired_thresholds
    (fun q => A.row q (idx (l, 0))) (fun q => A.row q (idx (l, 1)))
    (A.monotone _) (A.monotone _) (fun q => (A.in_unit q _).1)
    (fun q => (A.in_unit q _).1) (t l) (ht l)
  choose α β hα0 hβ0 hαt hβt hhit hpos using hex
  let T : PairedTest ι d := ⟨idx, fun j => if j.2 = 0 then α j.1 else β j.1⟩
  refine ⟨T, rfl, ?_, ?_, ?_⟩
  · intro l j
    fin_cases j <;> simp [T, hα0, hβ0, hαt, hβt]
  · intro l
    simpa [T] using hhit l
  · intro q
    dsimp [PairedTest.value]
    rw [Fintype.prod_prod_type]
    simp only [Fin.prod_univ_two]
    apply Finset.prod_nonneg
    intro l _
    simpa [T] using hpos l q

omit [Fintype ι] [DecidableEq ι] in
theorem PairedTest.zero_at_node {d : ℕ} (T : PairedTest ι d)
    (t : Fin d → ℝ) (hhit : ∀ l, T.threshold (l, 0) = t l ∨ T.threshold (l, 1) = t l)
    (l : Fin d) : T.polynomial.eval (t l) = 0 := by
  rw [T.eval]
  rcases hhit l with h | h
  · exact Finset.prod_eq_zero (Finset.mem_univ (l, 0)) (by simp [h])
  · exact Finset.prod_eq_zero (Finset.mem_univ (l, 1)) (by simp [h])

omit [Fintype ι] [DecidableEq ι] in
theorem PairedTest.positive_above {d : ℕ} (T : PairedTest ι d)
    (t : Fin d → ℝ) (hb : ∀ l j, T.threshold (l, j) ≤ t l)
    (x : ℝ) (hx : ∀ l, t l < x) : 0 < T.polynomial.eval x := by
  rw [T.eval]
  apply Finset.prod_pos
  intro j _
  exact sub_pos.mpr ((hb j.1 j.2).trans_lt (hx j.1))

end FairDice
