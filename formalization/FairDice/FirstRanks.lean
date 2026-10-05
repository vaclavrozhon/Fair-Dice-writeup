import FairDice.ApproximateGoFirst

namespace FairDice

variable {α : Type*} [DecidableEq α] [Fintype α]

omit [DecidableEq α] in
theorem exists_rank_equiv (f : α → ℕ) (hf : Function.Injective f) :
    ∃ e : Fin (Fintype.card α) ≃ α, ∀ i,
      ((Finset.univ : Finset α).filter (fun b => f b < f (e i))).card = i.val := by
  classical
  letI : LinearOrder α := LinearOrder.lift' f hf
  let e := Fintype.orderIsoFinOfCardEq α rfl
  refine ⟨e.toEquiv, ?_⟩
  intro i
  have hcard : ((Finset.univ : Finset α).filter (fun b => f b < f (e i))).card =
      (Finset.Iio i).card := by
    apply Finset.card_bij (fun b _ => e.symm b)
    · intro b hb
      apply Finset.mem_Iio.mpr
      have hlt : b < e i := (Finset.mem_filter.mp hb).2
      simpa using e.symm.strictMono hlt
    · intro b _ c _ he
      exact e.symm.injective he
    · intro j hj
      refine ⟨e j, ?_, by simp⟩
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, e.strictMono (Finset.mem_Iio.mp hj)⟩
  simpa [Fin.card_Iio] using hcard

theorem approximate_first_ranks {s : List α} (hpos : ∀ a : α, a ∈ s)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hwin : ∀ a : α, (winCount a s : ℝ) ≤
      (1 + δ) / Fintype.card α * outcomeCount s) :
    ∃ e : Fin (Fintype.card α) ≃ α, ∀ i,
      max 0 ((Fintype.card α : ℝ) / (1 + δ) - i.val) ≤ s.count (e i) := by
  obtain ⟨e, he⟩ := exists_rank_equiv (fun a => s.idxOf a)
    (fun a b h => (List.idxOf_inj (hpos a)).mp h)
  refine ⟨e, ?_⟩
  intro i
  have hi : s.idxOf (e i) < s.length := List.idxOf_lt_length_iff.mpr (hpos _)
  have hsplit : s = s.take (s.idxOf (e i)) ++ e i :: s.drop (s.idxOf (e i) + 1) := by
    conv_lhs => rw [← List.take_append_drop (s.idxOf (e i)) s]
    rw [List.drop_eq_getElem_cons hi, List.getElem_idxOf hi]
  have hnot : e i ∉ s.take (s.idxOf (e i)) := by
    rw [List.mem_take_iff_idxOf_lt (hpos _)]
    omega
  have hh := approximate_first_occurrence_bound hpos hsplit hnot hδ hwin
  have hcard : (s.take (s.idxOf (e i))).toFinset.card = i.val := by
    rw [← he i]
    congr 1
    ext b
    simp [List.mem_take_iff_idxOf_lt (hpos b)]
  simpa [hcard] using hh

/-- An explicit version of the final `Omega(n^2)` total-length conclusion
for every fixed nonnegative marginal error. -/
theorem approximate_goFirst_quadratic {s : List α} (hpos : ∀ a : α, a ∈ s)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hlarge : 4 * (1 + δ) ≤ Fintype.card α)
    (hwin : ∀ a : α, (winCount a s : ℝ) ≤
      (1 + δ) / Fintype.card α * outcomeCount s) :
    (Fintype.card α : ℝ)^2 / (8 * (1 + δ)^2) ≤ s.length := by
  classical
  let n := Fintype.card α
  let A : ℝ := n / (2 * (1 + δ))
  let K := ⌊A⌋₊
  have hden : 0 < 2 * (1 + δ) := by positivity
  have hd : 1 + δ ≠ 0 := by positivity
  have hnR : (0 : ℝ) < n := by dsimp [n]; linarith
  have hA2 : 2 ≤ A := by apply (le_div_iff₀ hden).mpr; dsimp [n]; linarith
  have hAn : A < n := by apply (div_lt_iff₀ hden).mpr; nlinarith
  have hKle : (K : ℝ) ≤ A := Nat.floor_le (by linarith)
  have hKgt : A < (K : ℝ) + 1 := Nat.lt_floor_add_one A
  have hKn : K < n := by exact_mod_cast hKle.trans_lt hAn
  obtain ⟨e, he⟩ := approximate_first_ranks hpos hδ hwin
  have hfaces (i : Fin n) (hi : i ∈ Finset.Iio (⟨K, hKn⟩ : Fin n)) :
      A ≤ (s.count (e i) : ℝ) := by
    have hiK : (i.val : ℝ) < K := by exact_mod_cast Finset.mem_Iio.mp hi
    have hh := (le_max_right 0 ((n : ℝ) / (1 + δ) - i.val)).trans (he i)
    have heA : (n : ℝ) / (1 + δ) = 2 * A := by dsimp [A]; field_simp [hd]
    rw [heA] at hh
    linarith
  have hsum : (K : ℝ) * A ≤ (s.length : ℝ) := by
    calc
      _ = ∑ _i ∈ Finset.Iio (⟨K, hKn⟩ : Fin n), A := by simp [Fin.card_Iio]
      _ ≤ ∑ i ∈ Finset.Iio (⟨K, hKn⟩ : Fin n), (s.count (e i) : ℝ) :=
        Finset.sum_le_sum hfaces
      _ ≤ ∑ i : Fin n, (s.count (e i) : ℝ) :=
        Finset.sum_le_univ_sum_of_nonneg (fun _ => by positivity)
      _ = ∑ a : α, (s.count a : ℝ) := Fintype.sum_equiv e _ _ (by intro i; rfl)
      _ = _ := by exact_mod_cast sum_multiplicities s
  have hAA : A^2 / 2 ≤ (s.length : ℝ) := by nlinarith
  have hid : (n : ℝ)^2 / (8 * (1 + δ)^2) = A^2 / 2 := by dsimp [A]; field_simp [hd]; ring
  rw [hid]
  exact hAA

end FairDice
