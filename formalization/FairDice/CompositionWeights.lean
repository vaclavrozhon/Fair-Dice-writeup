import FairDice.MultinomialCollision

namespace FairDice

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem sum_injection_le {β γ : Type*} [Fintype β] [Fintype γ]
    (f : β → γ) (hf : Function.Injective f) (g : γ → ℝ) (hg : ∀ c, 0 ≤ g c) :
    (∑ b, g (f b)) ≤ ∑ c, g c := by
  classical
  calc
    _ = ∑ c ∈ Finset.univ.image f, g c := (Finset.sum_image (fun _ _ _ _ h => hf h)).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun c _ _ => hg c)

/-- Dropping one coordinate of a weak composition is injective. Therefore
its remaining nonnegative weights can be summed independently. -/
theorem composition_product_sum_le (M : ℕ) (j : ι) (w : ℕ → ℝ) (hw : ∀ k, 0 ≤ w k) :
    (∑ g ∈ Finset.piAntidiag (Finset.univ : Finset ι) M, ∏ i : {i : ι // i ≠ j}, w (g i.val)) ≤
      (∑ k : Fin (M+1), w k.val)^(Fintype.card {i : ι // i ≠ j}) := by
  classical
  let S := Finset.piAntidiag (Finset.univ : Finset ι) M
  let β := {g : ι → ℕ // g ∈ S}
  have hsum (g : β) : ∑ i, g.val i = M := (Finset.mem_piAntidiag.mp g.property).1
  have hle (g : β) (i : ι) : g.val i ≤ M := by
    rw [← hsum g]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  let F (g : β) : ({i : ι // i ≠ j} → Fin (M+1)) :=
    fun i => ⟨g.val i, by have := hle g i; omega⟩
  have hinj : Function.Injective F := by
    intro g h he
    have hrest (i : ι) (hi : i ≠ j) : g.val i = h.val i :=
      congrArg Fin.val (congrFun he ⟨i, hi⟩)
    have hsumrest : (∑ i ∈ Finset.univ.erase j, g.val i) = ∑ i ∈ Finset.univ.erase j, h.val i := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hrest i (Finset.mem_erase.mp hi).1
    have hg := hsum g
    have hh := hsum h
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j)] at hg hh
    apply Subtype.ext
    funext i
    by_cases hi : i = j
    · subst i
      omega
    · exact hrest i hi
  let G : ({i : ι // i ≠ j} → Fin (M+1)) → ℝ := fun f => ∏ i, w (f i).val
  have hh := sum_injection_le F hinj G (fun f => Finset.prod_nonneg (fun i _ => hw _))
  have hleft : (∑ g : β, G (F g)) =
      ∑ g ∈ S, ∏ i : {i : ι // i ≠ j}, w (g i.val) := by
    simpa only [F, G] using Finset.sum_coe_sort S
      (fun g : ι → ℕ => ∏ i : {i : ι // i ≠ j}, w (g i.val))
  rw [hleft] at hh
  have hright : (∑ f : ({i : ι // i ≠ j} → Fin (M+1)), G f) =
      (∑ k : Fin (M+1), w k.val)^(Fintype.card {i : ι // i ≠ j}) := by
    unfold G
    have h := Fintype.prod_sum (ι := {i : ι // i ≠ j}) (κ := fun _ => Fin (M+1))
      (fun (_ : {i : ι // i ≠ j}) (k : Fin (M+1)) => w k.val)
    simpa using h.symm
  rw [hright] at hh
  simpa only [S] using hh

/-- The lattice summation step separated from the pointwise probability
bound. The chosen coordinate may depend on the composition. -/
theorem composition_sum_le (M : ℕ) (w : ℕ → ℝ) (hw : ∀ k, 0 ≤ w k)
    (F : (ι → ℕ) → ℝ) (B : ℝ) (hB : 0 ≤ B)
    (hF : ∀ g ∈ Finset.piAntidiag (Finset.univ : Finset ι) M,
      ∃ j : ι, F g ≤ B * ∏ i : {i : ι // i ≠ j}, w (g i.val)) :
    (∑ g ∈ Finset.piAntidiag (Finset.univ : Finset ι) M, F g) ≤
      B * ∑ j : ι, (∑ k : Fin (M+1), w k.val)^(Fintype.card {i : ι // i ≠ j}) := by
  calc
    _ ≤ ∑ g ∈ Finset.piAntidiag (Finset.univ : Finset ι) M,
        B * ∑ j : ι, ∏ i : {i : ι // i ≠ j}, w (g i.val) := by
      apply Finset.sum_le_sum
      intro g hg
      obtain ⟨j, hj⟩ := hF g hg
      have hnn (j : ι) : 0 ≤ ∏ i : {i : ι // i ≠ j}, w (g i.val) :=
        Finset.prod_nonneg (fun i _ => hw _)
      have hh := Finset.single_le_sum (f := fun j : ι => ∏ i : {i : ι // i ≠ j}, w (g i.val))
        (fun j _ => hnn j) (Finset.mem_univ j)
      exact hj.trans (mul_le_mul_of_nonneg_left hh hB)
    _ = B * ∑ j : ι, ∑ g ∈ Finset.piAntidiag (Finset.univ : Finset ι) M,
        ∏ i : {i : ι // i ≠ j}, w (g i.val) := by rw [← Finset.mul_sum, Finset.sum_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Finset.sum_le_sum (fun j _ => composition_product_sum_le M j w hw)) hB

end FairDice
