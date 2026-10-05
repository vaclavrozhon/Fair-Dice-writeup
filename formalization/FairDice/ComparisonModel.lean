import FairDice.MonotoneMoments

namespace FairDice

variable {α : Type*} [DecidableEq α]

theorem sublist_of_mem_faceSuffixes (a : α) (s t : List α) (ht : t ∈ faceSuffixes a s) :
    t.Sublist s := by
  induction s with
  | nil => simp [faceSuffixes] at ht
  | cons b s ih =>
    by_cases hab : a = b
    · simp only [faceSuffixes, if_pos hab, List.mem_cons] at ht
      rcases ht with rfl | ht
      · exact List.Sublist.cons _ (List.Sublist.refl _)
      · exact List.Sublist.cons _ (ih ht)
    · simp only [faceSuffixes, if_neg hab] at ht
      exact List.Sublist.cons _ (ih ht)

theorem faceSuffixes_pairwise (a : α) (s : List α) :
    (faceSuffixes a s).Pairwise (fun u v => v.Sublist u) := by
  induction s with
  | nil => simp [faceSuffixes]
  | cons b s ih =>
    by_cases hab : a = b
    · simp only [faceSuffixes, if_pos hab, List.pairwise_cons]
      exact ⟨fun t ht => sublist_of_mem_faceSuffixes a s t ht, ih⟩
    · simpa only [faceSuffixes, if_neg hab] using ih

theorem real_tailProduct (s t p : List α) :
    (tailProduct s t p : ℝ) = (p.map (fun b => (t.count b : ℝ) / s.count b)).prod := by
  simp [tailProduct, Function.comp_def]

variable [Fintype α]

/-- Reflect the distinguished faces. The suffix comparison probabilities
then increase with the row index. This is the order-reversed version of the
paper's `Pr(D_i < x_q)` model and has exactly the same mixed moments. -/
noncomputable def comparisonModel {s : List α} (hs : PermutationFair s) (a : α) :
    MonotoneMoments {b : α // b ≠ a} (faceSuffixes a s).reverse.length := by
  classical
  let L := (faceSuffixes a s).reverse
  have hca : (0 : ℝ) < s.count a := by exact_mod_cast List.count_pos_iff.mpr (hs.1 a)
  have hcb (b : {b : α // b ≠ a}) : (0 : ℝ) < s.count b.val := by
    exact_mod_cast List.count_pos_iff.mpr (hs.1 b.val)
  have hL : L.length = s.count a := by simp [L, length_faceSuffixes]
  refine
    { row := fun q b => ((L.get q).count b.val : ℝ) / s.count b.val
      weight := fun _ => 1 / (s.count a : ℝ)
      weight_pos := fun _ => by positivity
      weight_sum := ?_
      in_unit := ?_
      monotone := ?_
      moments := ?_ }
  · simp [length_faceSuffixes, hca.ne']
  · intro q b
    have ht : L.get q ∈ faceSuffixes a s := by
      apply List.mem_reverse.mp
      exact List.get_mem _ _
    have hh := (sublist_of_mem_faceSuffixes a s _ ht).count_le b.val
    have hhR : ((L.get q).count b.val : ℝ) ≤ s.count b.val := by exact_mod_cast hh
    exact ⟨by positivity, (div_le_one (hcb b)).mpr hhR⟩
  · intro b i j hij
    have hp : L.Pairwise (fun u v => u.Sublist v) := by
      rw [List.pairwise_reverse]
      exact faceSuffixes_pairwise a s
    have hh : (L.get i).Sublist (L.get j) := by
      rcases eq_or_lt_of_le hij with he | hlt
      · subst j; exact List.Sublist.refl _
      · exact hp.rel_get_of_lt hlt
    have hc := hh.count_le b.val
    exact div_le_div_of_nonneg_right (by exact_mod_cast hc) (hcb b).le
  · intro S
    let p := S.toList.map Subtype.val
    have hpa : (a :: p).Nodup := by
      apply List.nodup_cons.mpr
      constructor
      · intro ha
        obtain ⟨b, _, hb⟩ := List.mem_map.mp ha
        exact b.property hb
      · exact (Finset.nodup_toList S).map Subtype.val_injective
    have hp := faceSuffixes_moment hs a p hpa
    have hpR : (((faceSuffixes a s).map (fun t =>
        (p.map (fun b => (t.count b : ℝ) / s.count b)).prod)).sum) =
        (s.count a : ℝ) / (S.card + 1 : ℝ) := by
      have hh := congrArg (fun z : ℚ => (z : ℝ)) hp
      simpa [Function.comp_def, real_tailProduct, p] using hh
    have hsum : (∑ q : Fin L.length, ∏ b ∈ S,
        ((L.get q).count b.val : ℝ) / s.count b.val) =
        (s.count a : ℝ) / (S.card + 1 : ℝ) := by
      rw [← List.sum_ofFn]
      have he : (List.ofFn (fun q : Fin L.length => ∏ b ∈ S,
          ((L.get q).count b.val : ℝ) / s.count b.val)) =
          L.map (fun t => (p.map (fun b => (t.count b : ℝ) / s.count b)).prod) := by
        have haux := List.ofFn_getElem_eq_map L (fun t => ∏ b ∈ S,
          (t.count b.val : ℝ) / s.count b.val)
        rw [show (List.ofFn (fun q : Fin L.length => ∏ b ∈ S,
          ((L.get q).count b.val : ℝ) / s.count b.val)) =
            L.map (fun t => ∏ b ∈ S, (t.count b.val : ℝ) / s.count b.val) by
              simpa only [List.get_eq_getElem] using haux]
        apply List.map_congr_left
        intro t _
        simpa only [p, List.map_map, Function.comp_def] using
          (Finset.prod_map_toList S (fun b => (t.count b.val : ℝ) / s.count b.val)).symm
      rw [he]
      simpa [L, List.map_reverse, List.sum_reverse] using hpR
    rw [← Finset.mul_sum, hsum]
    field_simp

end FairDice
