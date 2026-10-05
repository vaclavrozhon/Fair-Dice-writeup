import Mathlib

namespace FairDice

/-- A point on a monotone line segment at which the first of the two
coordinates reaches `t`. The other coordinate is no larger than `t`. -/
theorem paired_segment_threshold (x₀ y₀ x₁ y₁ t : ℝ)
    (hx : x₀ ≤ x₁) (hy : y₀ ≤ y₁) (hx₀ : 0 ≤ x₀) (hy₀ : 0 ≤ y₀)
    (hlo : max x₀ y₀ ≤ t) (hhi : t ≤ max x₁ y₁) :
    ∃ α β : ℝ, x₀ ≤ α ∧ α ≤ x₁ ∧ y₀ ≤ β ∧ β ≤ y₁ ∧
      0 ≤ α ∧ 0 ≤ β ∧ α ≤ t ∧ β ≤ t ∧ (α = t ∨ β = t) := by
  let f : ℝ → ℝ := fun u => max (x₀ + u * (x₁ - x₀)) (y₀ + u * (y₁ - y₀))
  have hf : Continuous f := by dsimp [f]; fun_prop
  have ht : t ∈ Set.Icc (f 0) (f 1) := by simpa [f] using And.intro hlo hhi
  obtain ⟨u, hu, he⟩ := intermediate_value_Icc (by norm_num : (0 : ℝ) ≤ 1)
    hf.continuousOn ht
  let α := x₀ + u * (x₁ - x₀)
  let β := y₀ + u * (y₁ - y₀)
  have hxlo : x₀ ≤ α := by dsimp [α]; nlinarith [mul_nonneg hu.1 (sub_nonneg.mpr hx)]
  have hxhi : α ≤ x₁ := by dsimp [α]; nlinarith [mul_nonneg (sub_nonneg.mpr hu.2) (sub_nonneg.mpr hx)]
  have hylo : y₀ ≤ β := by dsimp [β]; nlinarith [mul_nonneg hu.1 (sub_nonneg.mpr hy)]
  have hyhi : β ≤ y₁ := by dsimp [β]; nlinarith [mul_nonneg (sub_nonneg.mpr hu.2) (sub_nonneg.mpr hy)]
  change max α β = t at he
  have ha := (le_max_left α β).trans he.le
  have hb := (le_max_right α β).trans he.le
  refine ⟨α, β, hxlo, hxhi, hylo, hyhi, hx₀.trans hxlo, hy₀.trans hylo, ha, hb, ?_⟩
  rcases le_total α β with h | h
  · exact Or.inr (by simpa [max_eq_right h] using he)
  · exact Or.inl (by simpa [max_eq_left h] using he)

/-- Lemma `individual-paired-thresholds`. This proof chooses the first
crossing row and interpolates only that segment; no rows or weights are
added to the moment system. -/
theorem paired_thresholds {K : ℕ} (x y : Fin K → ℝ)
    (hx : Monotone x) (hy : Monotone y)
    (hx₀ : ∀ q, 0 ≤ x q) (hy₀ : ∀ q, 0 ≤ y q)
    (t : ℝ) (ht : 0 < t) :
    ∃ α β : ℝ, 0 ≤ α ∧ 0 ≤ β ∧ α ≤ t ∧ β ≤ t ∧
      (α = t ∨ β = t) ∧ ∀ q, 0 ≤ (x q - α) * (y q - β) := by
  classical
  by_cases hcross : ∃ q, t ≤ max (x q) (y q)
  · let r := Fin.find (fun q => t ≤ max (x q) (y q)) hcross
    have hr : t ≤ max (x r) (y r) := Fin.find_spec hcross
    let x₀ := if h : 0 < r.val then x ⟨r.val - 1, by omega⟩ else 0
    let y₀ := if h : 0 < r.val then y ⟨r.val - 1, by omega⟩ else 0
    have hxle : x₀ ≤ x r := by
      dsimp [x₀]
      split_ifs with h
      · exact hx (by show r.val - 1 ≤ r.val; omega)
      · exact hx₀ r
    have hyle : y₀ ≤ y r := by
      dsimp [y₀]
      split_ifs with h
      · exact hy (by show r.val - 1 ≤ r.val; omega)
      · exact hy₀ r
    have hx0 : 0 ≤ x₀ := by dsimp [x₀]; split_ifs; exact hx₀ _; exact le_rfl
    have hy0 : 0 ≤ y₀ := by dsimp [y₀]; split_ifs; exact hy₀ _; exact le_rfl
    have hlo : max x₀ y₀ ≤ t := by
      dsimp [x₀, y₀]
      split_ifs with h
      · have hh := Fin.find_min hcross (j := ⟨r.val - 1, by omega⟩)
          (by show r.val - 1 < r.val; omega)
        exact (lt_of_not_ge hh).le
      · simpa using ht.le
    obtain ⟨α, β, hαlo, hαhi, hβlo, hβhi, hα0, hβ0, hαt, hβt, hhit⟩ :=
      paired_segment_threshold x₀ y₀ (x r) (y r) t hxle hyle hx0 hy0 hlo hr
    refine ⟨α, β, hα0, hβ0, hαt, hβt, hhit, ?_⟩
    intro q
    by_cases hqr : r ≤ q
    · exact mul_nonneg (sub_nonneg.mpr (hαhi.trans (hx hqr)))
        (sub_nonneg.mpr (hβhi.trans (hy hqr)))
    · have hqr' : q.val < r.val := by simpa using lt_of_not_ge hqr
      have hpos : 0 < r.val := by omega
      have hqx : x q ≤ x₀ := by dsimp [x₀]; rw [dif_pos hpos]; exact hx (by show q.val ≤ r.val - 1; omega)
      have hqy : y q ≤ y₀ := by dsimp [y₀]; rw [dif_pos hpos]; exact hy (by show q.val ≤ r.val - 1; omega)
      exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr (hqx.trans hαlo))
        (sub_nonpos.mpr (hqy.trans hβlo))
  · by_cases hK : 0 < K
    · let last : Fin K := ⟨K - 1, by omega⟩
      have hh : max (x last) (y last) < t := by
        exact lt_of_not_ge (fun h => hcross ⟨last, h⟩)
      refine ⟨t, y last, ht.le, hy₀ last, le_rfl, (le_max_right _ _).trans hh.le, Or.inl rfl, ?_⟩
      intro q
      exact mul_nonneg_of_nonpos_of_nonpos
        (sub_nonpos.mpr ((hx (by show q.val ≤ K - 1; omega)).trans ((le_max_left _ _).trans hh.le)))
        (sub_nonpos.mpr (hy (by show q.val ≤ K - 1; omega)))
    · refine ⟨t, 0, ht.le, le_rfl, le_rfl, ht.le, Or.inl rfl, ?_⟩
      intro q
      have := q.isLt
      omega

end FairDice
