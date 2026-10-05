import FairDice.PairedTests
import FairDice.CollisionBound

namespace FairDice

open Polynomial

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {K : ℕ}

/-- The Gaussian test prevents any coordinate of the last row from lying
below the largest Gaussian node. -/
theorem last_row_gaussian (A : MonotoneMoments ι K) (last : Fin K)
    (hlast : ∀ q, q ≤ last) (i : ι) {d : ℕ} (hd : 2 * d + 1 ≤ Fintype.card ι)
    (G : GaussianData d) : G.node (Fin.last d) ≤ A.row last i := by
  classical
  have hi : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i⟩
  have hcard : Fintype.card (Fin d × Fin 2) ≤ Fintype.card {j : ι // j ≠ i} := by
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_subtype_compl,
      Fintype.card_unique]
    omega
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  let idx := e.trans (Function.Embedding.subtype (fun j : ι => j ≠ i))
  obtain ⟨T, hidx, hb, hhit, hnonneg⟩ := exists_paired_test A idx
    (fun l : Fin d => G.node l.castSucc) (fun l => (G.interior _).1)
  have hextra : ∀ j, T.index j ≠ i := by
    intro j
    rw [hidx]
    exact (e j).property
  have hdegree : ((C (A.row last i) - X) * T.polynomial).natDegree ≤ 2 * d + 1 := by
    apply natDegree_mul_le.trans
    have hlin : (C (A.row last i) - X : ℝ[X]).natDegree ≤ 1 :=
      (natDegree_sub_le (C (A.row last i)) X).trans (max_le (by simp) (by simp))
    have ht := T.degree
    omega
  have hs : 0 ≤ realPolynomialIntegral ((C (A.row last i) - X) * T.polynomial) := by
    rw [← T.extra_identity A i hextra]
    apply Finset.sum_nonneg
    intro q _
    exact mul_nonneg (mul_nonneg (A.weight_pos q).le
      (sub_nonneg.mpr (A.monotone i (hlast q)))) (hnonneg q)
  rw [← G.exactness _ hdegree, Fin.sum_univ_castSucc] at hs
  have hz (l : Fin d) : T.polynomial.eval (G.node l.castSucc) = 0 :=
    T.zero_at_node _ hhit l
  simp only [eval_mul, eval_sub, eval_C, eval_X, hz, mul_zero,
    Finset.sum_const_zero, zero_add] at hs
  have hP : 0 < T.polynomial.eval (G.node (Fin.last d)) :=
    T.positive_above _ (fun l j => (hb l j).2) _
      (fun l => G.increasing (by show l.val < d; exact l.isLt))
  have hw := G.weight_pos (Fin.last d)
  have hh := nonneg_of_mul_nonneg_right hs hw
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_left hh hP)

theorem last_row_endpoint_lower (hext : ClassicalQuadratureExternal)
    (A : MonotoneMoments ι K) (last : Fin K) (hlast : ∀ q, q ≤ last) (i : ι) :
    1 - Real.pi^2 / ((Fintype.card ι : ℝ) + 1)^2 ≤ A.row last i := by
  let m := Fintype.card ι
  let d := (m - 1) / 2
  have hm : 0 < m := Fintype.card_pos_iff.mpr ⟨i⟩
  have hd : 2 * d + 1 ≤ m := by dsimp [d]; omega
  obtain ⟨G⟩ := hext.1 d
  have hrow := last_row_gaussian A last hlast i hd G
  have hedge := G.edge_bound
  have hdm : (m : ℝ) + 1 ≤ 2 * ((d : ℝ) + 2) := by
    exact_mod_cast (show m + 1 ≤ 2 * (d + 2) by dsimp [d]; omega)
  have hden : ((m : ℝ) + 1)^2 ≤ 4 * ((d : ℝ) + 2)^2 := by nlinarith
  have hfrac : Real.pi^2 / (4 * ((d : ℝ) + 2)^2) ≤ Real.pi^2 / ((m : ℝ) + 1)^2 :=
    div_le_div_of_nonneg_left (sq_nonneg _) (by positivity) hden
  dsimp [m] at hfrac
  linarith

omit [Fintype ι] [DecidableEq ι] in
/-- Product estimate used by the Radau test. This version lists both
coordinates of each pair, so the final loss is twice the reciprocal sum. -/
theorem paired_last_ratio {d : ℕ} (T : PairedTest ι d) (x : ι → ℝ)
    (t : Fin d → ℝ) (δ : ℝ) (hδ : 0 ≤ δ)
    (ht : ∀ l, t l < 1) (hb : ∀ l j, T.threshold (l, j) ≤ t l)
    (hx : ∀ j, 1 - δ ≤ x (T.index j))
    (hz : ∀ l, δ / (1 - t l) ≤ 1) :
    (1 - 2 * ∑ l : Fin d, δ / (1 - t l)) * T.polynomial.eval 1 ≤ T.value x := by
  have hdpos (j : Fin d × Fin 2) : 0 < 1 - T.threshold j :=
    sub_pos.mpr ((hb j.1 j.2).trans_lt (ht j.1))
  have hr (j : Fin d × Fin 2) :
      1 - δ / (1 - t j.1) ≤ (x (T.index j) - T.threshold j) / (1 - T.threshold j) := by
    have hden := hdpos j
    have hfrac := div_le_div_of_nonneg_left hδ (sub_pos.mpr (ht j.1))
      (sub_le_sub_left (hb j.1 j.2) 1)
    apply (le_div_iff₀ hden).mpr
    have hh := (div_le_iff₀ hden).mp hfrac
    nlinarith [hx j]
  have hn (j : Fin d × Fin 2) : 0 ≤ 1 - δ / (1 - t j.1) := sub_nonneg.mpr (hz j.1)
  have hh := prod_one_sub_lower (Finset.univ : Finset (Fin d × Fin 2))
    (fun j => δ / (1 - t j.1))
    (fun j _ => ⟨div_nonneg hδ (sub_pos.mpr (ht j.1)).le, hz j.1⟩)
  have hsum : (∑ j : Fin d × Fin 2, δ / (1 - t j.1)) =
      2 * ∑ l : Fin d, δ / (1 - t l) := by
    rw [Fintype.sum_prod_type]
    simp [two_mul, Finset.sum_add_distrib]
  rw [hsum] at hh
  have hprod := Finset.prod_le_prod (s := Finset.univ) (fun j _ => hn j) (fun j _ => hr j)
  have he : (∏ j : Fin d × Fin 2,
      (x (T.index j) - T.threshold j) / (1 - T.threshold j)) =
      T.value x / T.polynomial.eval 1 := by
    rw [Finset.prod_div_distrib, T.eval]
    rfl
  rw [he] at hprod
  exact (le_div_iff₀ (by rw [T.eval]; exact Finset.prod_pos (fun j _ => hdpos j))).mp
    (hh.trans hprod)

/-- Lemma `individual-last-row`: the last atom of any monotone mixed-moment
representation has weight at most `200/m²`. -/
theorem last_row_weight_bound (hext : ClassicalQuadratureExternal)
    (A : MonotoneMoments ι K) (last : Fin K) (hlast : ∀ q, q ≤ last)
    (hm : 0 < Fintype.card ι) :
    A.weight last ≤ 200 / (Fintype.card ι : ℝ)^2 := by
  classical
  let m := Fintype.card ι
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hw1 : A.weight last ≤ 1 := by
    rw [← A.weight_sum]
    exact Finset.single_le_sum (fun q _ => (A.weight_pos q).le) (Finset.mem_univ last)
  by_cases hsmall : m < 10
  · have hm10 : (m : ℝ) < 10 := by exact_mod_cast hsmall
    have hbound : (1 : ℝ) ≤ 200 / (m : ℝ)^2 := by
      apply (le_div_iff₀ (by positivity)).mpr
      nlinarith
    exact hw1.trans hbound
  · have hm10 : 10 ≤ m := by omega
    let e := m / 10
    let δ := Real.pi^2 / ((m : ℝ) + 1)^2
    have hδ : 0 ≤ δ := by dsimp [δ]; positivity
    have hepos : 0 < e := by dsimp [e]; omega
    have hedim : 2 * e ≤ m := by dsimp [e]; omega
    obtain ⟨R⟩ := hext.2 e
    have hcard : Fintype.card (Fin e × Fin 2) ≤ Fintype.card ι := by
      simpa [Fintype.card_prod, Nat.mul_comm] using hedim
    obtain ⟨idx⟩ := Function.Embedding.nonempty_of_card_le hcard
    obtain ⟨T, _, hb, hhit, hnonneg⟩ := exists_paired_test A idx
      (fun l : Fin e => R.node l.castSucc) (fun l => (R.interior _).1)
    have ht (l : Fin e) : R.node l.castSucc < 1 := (R.interior l).2
    have hsum : (∑ l : Fin e, δ / (1 - R.node l.castSucc)) =
        δ * ((e : ℝ) * (e + 2) / 2) := by
      simp_rw [div_eq_mul_inv]
      rw [← Finset.mul_sum]
      simpa [div_eq_mul_inv] using congrArg (fun x : ℝ => δ * x) R.reciprocal_sum
    have he10 : 10 * (e : ℝ) ≤ m := by
      exact_mod_cast (show 10 * e ≤ m by dsimp [e]; omega)
    have heplus : 10 * ((e : ℝ) + 2) ≤ 3 * m := by
      exact_mod_cast (show 10 * (e + 2) ≤ 3 * m by dsimp [e]; omega)
    have he0 : (0 : ℝ) ≤ e := by positivity
    have hp := mul_le_mul he10 heplus (by positivity : (0 : ℝ) ≤ 10 * ((e : ℝ) + 2)) hmR.le
    have hS : (e : ℝ) * (e + 2) / 2 ≤ 3 * (m : ℝ)^2 / 200 := by nlinarith
    have hπ : Real.pi^2 < 10 := by nlinarith [Real.pi_pos, Real.pi_lt_d2]
    have hsumlt : (∑ l : Fin e, δ / (1 - R.node l.castSucc)) < 1 / 4 := by
      rw [hsum]
      dsimp [δ]
      rw [div_mul_eq_mul_div]
      apply (div_lt_iff₀ (by positivity)).mpr
      have hmul := mul_le_mul_of_nonneg_left hS (sq_nonneg Real.pi)
      have hmul' := mul_lt_mul_of_pos_right hπ (by positivity : (0 : ℝ) < 3 * (m : ℝ)^2 / 200)
      nlinarith
    have hz (l : Fin e) : δ / (1 - R.node l.castSucc) ≤ 1 := by
      have hle := Finset.single_le_sum (s := Finset.univ)
        (f := fun l : Fin e => δ / (1 - R.node l.castSucc))
        (fun j _ => div_nonneg hδ (sub_pos.mpr (ht j)).le) (Finset.mem_univ l)
      linarith
    have ha (j : Fin e × Fin 2) : 1 - δ ≤ A.row last (T.index j) :=
      last_row_endpoint_lower hext A last hlast _
    have hratio := paired_last_ratio T (A.row last) _ δ hδ ht
      (fun l j => (hb l j).2) ha hz
    have hP : 0 < T.polynomial.eval 1 := T.positive_above _ (fun l j => (hb l j).2) 1 ht
    have hlastval : T.polynomial.eval 1 / 2 ≤ T.value (A.row last) := by
      have hfactor : (1 / 2 : ℝ) ≤ 1 - 2 * ∑ l : Fin e, δ / (1 - R.node l.castSucc) := by linarith
      have hmul := mul_le_mul_of_nonneg_right hfactor hP.le
      linarith
    have hsumT : (∑ q, A.weight q * T.value (A.row q)) =
        T.polynomial.eval 1 / ((e + 1 : ℕ) : ℝ)^2 := by
      rw [T.identity A, ← R.exactness T.polynomial T.degree, Fin.sum_univ_castSucc]
      have hzero (l : Fin e) := T.zero_at_node (fun l : Fin e => R.node l.castSucc) hhit l
      simp only [hzero, mul_zero, Finset.sum_const_zero, zero_add,
        R.endpoint, R.endpoint_weight]
      ring
    have hwT : A.weight last * T.value (A.row last) ≤
        T.polynomial.eval 1 / ((e + 1 : ℕ) : ℝ)^2 := by
      rw [← hsumT]
      exact Finset.single_le_sum (fun q _ => mul_nonneg (A.weight_pos q).le (hnonneg q))
        (Finset.mem_univ last)
    have hw : A.weight last ≤ 2 / ((e + 1 : ℕ) : ℝ)^2 := by
      have hmul := mul_le_mul_of_nonneg_left hlastval (A.weight_pos last).le
      have hbnd := hmul.trans hwT
      have hdiv : (A.weight last / 2) * T.polynomial.eval 1 ≤
          (1 / ((e + 1 : ℕ) : ℝ)^2) * T.polynomial.eval 1 := by
        simpa only [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, one_mul] using hbnd
      have hc := (mul_le_mul_iff_left₀ hP).mp hdiv
      calc
        _ = 2 * (A.weight last / 2) := by ring
        _ ≤ 2 * (1 / ((e + 1 : ℕ) : ℝ)^2) := mul_le_mul_of_nonneg_left hc (by norm_num)
        _ = _ := by ring
    have hme : (m : ℝ) ≤ 10 * ((e + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show m ≤ 10 * (e + 1) by dsimp [e]; omega)
    have hfin : 2 / ((e + 1 : ℕ) : ℝ)^2 ≤ 200 / (m : ℝ)^2 := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      nlinarith
    exact hw.trans hfin

end FairDice
