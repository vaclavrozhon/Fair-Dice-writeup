import FairDice.IntervalRules

namespace FairDice

open Polynomial

structure EqualWeightRealRule (K degree : ℕ) where
  node : Fin K → ℝ
  in_unit : ∀ q, 0 ≤ node q ∧ node q ≤ 1
  exactness : ∀ p : ℝ[X], p.natDegree ≤ degree →
    (∑ q, p.eval (node q)) = K * realPolynomialIntegral p

theorem realPolynomialIntegral_square_pos (p : ℝ[X]) (hp : p ≠ 0) :
    0 < realPolynomialIntegral (p*p) := by
  have hex : ∃ x ∈ Set.Icc (0 : ℝ) 1, p.eval x ≠ 0 := by
    by_contra h
    push Not at h
    apply hp
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply (Set.Icc_infinite (by norm_num : (0 : ℝ) < 1)).mono
    intro x hx
    exact h x hx
  obtain ⟨x, hx, hx0⟩ := hex
  have hpos := intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
    (by norm_num : (0 : ℝ) < 1) continuous_const.continuousOn
    (p.continuous.mul p.continuous).continuousOn
    (fun y _ => mul_self_nonneg (p.eval y)) ⟨x, hx, mul_self_pos.mpr hx0⟩
  rw [realPolynomialIntegral_eq_integral]
  simpa using hpos

/-- The support of a degree-`2m+2` rule has at least `m+2` distinct points.
Repeated starting nodes are allowed; the support-size conclusion is proved. -/
theorem real_rule_support_card {K m : ℕ} (hK : 0 < K)
    (Q : EqualWeightRealRule K (2*m+2)) :
    m+2 ≤ (Finset.univ.image Q.node).card := by
  classical
  let S := Finset.univ.image Q.node
  let p : ℝ[X] := ∏ x ∈ S, (X-C x)
  have hp0 : p ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun x _ => X_sub_C_ne_zero x)
  have hdeg : p.natDegree ≤ S.card := by
    apply (natDegree_prod_le S (fun x => (X : ℝ[X])-C x)).trans
    simp
  by_contra h
  change ¬ m+2 ≤ S.card at h
  have hcard : S.card ≤ m+1 := by omega
  have hdegree : (p*p).natDegree ≤ 2*m+2 :=
    (natDegree_mul_le).trans (by omega)
  have hz (q : Fin K) : p.eval (Q.node q) = 0 := by
    simp only [p, eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_image.mpr ⟨q, Finset.mem_univ q, rfl⟩) (by simp)
  have hh := Q.exactness (p*p) hdegree
  simp only [eval_mul, hz, zero_mul, Finset.sum_const_zero] at hh
  have hpos := realPolynomialIntegral_square_pos p hp0
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK
  nlinarith

/-- The starting rule supplies `m` distinct interior pivot nodes, with
actual indices in its list of `K` nodes. -/
theorem real_rule_pivots {K m : ℕ} (hK : 0 < K)
    (Q : EqualWeightRealRule K (2*m+2)) :
    ∃ e : Fin m ↪ Fin K, Function.Injective (fun j => Q.node (e j)) ∧
      ∀ j, 0 < Q.node (e j) ∧ Q.node (e j) < 1 := by
  classical
  let S := Finset.univ.image Q.node
  let T := S \ {0, 1}
  have hST : S ⊆ T ∪ {0, 1} := by
    intro x hx
    by_cases he : x ∈ ({0, 1} : Finset ℝ)
    · exact Finset.mem_union_right T he
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx, he⟩)
  have hcard : m ≤ T.card := by
    have hh := real_rule_support_card hK Q
    have hle := (Finset.card_mono hST).trans (Finset.card_union_le T {0, 1})
    have hp : ({0, 1} : Finset ℝ).card = 2 := by norm_num
    rw [hp] at hle
    dsimp [S] at hle
    omega
  obtain ⟨f⟩ := Function.Embedding.nonempty_of_card_le (α := Fin m) (β := ↥T)
    (by simpa using hcard)
  have hf (j : Fin m) : ∃ q : Fin K, Q.node q = (f j).val := by
    have hh := (Finset.mem_sdiff.mp (f j).property).1
    exact Finset.mem_image.mp hh |>.imp fun q h => h.2
  choose e he using hf
  have hinj : Function.Injective (fun j => Q.node (e j)) := by
    intro i j hh
    apply f.injective
    apply Subtype.ext
    simpa only [he] using hh
  have hei : Function.Injective e := fun i j hh => hinj (congrArg Q.node hh)
  refine ⟨⟨e, hei⟩, hinj, fun j => ?_⟩
  have hu := Q.in_unit (e j)
  have hnot := (Finset.mem_sdiff.mp (f j).property).2
  have hn0 : Q.node (e j) ≠ 0 := by simpa [he] using (show (f j).val ≠ 0 from fun h => hnot (by simp [h]))
  have hn1 : Q.node (e j) ≠ 1 := by simpa [he] using (show (f j).val ≠ 1 from fun h => hnot (by simp [h]))
  exact ⟨lt_of_le_of_ne hu.1 (Ne.symm hn0), lt_of_le_of_ne hu.2 hn1⟩

end FairDice
