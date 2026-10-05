import FairDice.PrimitiveCorrections

namespace FairDice

open MeasureTheory Set

noncomputable def correctionIterate : ℕ → (ℝ → ℝ) → ℝ → ℝ
  | 0,f => f
  | r+1,f => correctionPrimitive (correctionIterate r f)

@[simp] theorem correctionIterate_zero (f : ℝ → ℝ) : correctionIterate 0 f=f := rfl
@[simp] theorem correctionIterate_succ (r : ℕ) (f : ℝ → ℝ) :
    correctionIterate (r+1) f=correctionPrimitive (correctionIterate r f) := rfl

theorem correctionIterate_local {f : ℝ → ℝ} (hf : LocallyIntegrable f volume) (r : ℕ) :
    LocallyIntegrable (correctionIterate r f) volume := by
  induction r with
  | zero => exact hf
  | succ r ih => exact correctionPrimitive_local ih

/-- Repeated uniform integrations preserve the literal correction support
as long as the available vanishing moments have not been exhausted. -/
theorem correctionIterate_support_moments {f : ℝ → ℝ} (hf : LocallyIntegrable f volume)
    {L R : ℝ} (hL : 0 ≤ L) (hR : R ≤ 1) (hLR : L < R)
    (hs : Function.support f ⊆ Ioo L R) (D : ℕ)
    (hmom : ∀ k < D, (∫ x in (0 : ℝ)..1, f x*x^k)=0)
    (r : ℕ) (hr : r ≤ D) :
    Function.support (correctionIterate r f) ⊆ Ioo L R ∧
      ∀ k, k+r < D → (∫ x in (0 : ℝ)..1, correctionIterate r f x*x^k)=0 := by
  induction r with
  | zero => exact ⟨hs,fun k hk => hmom k (by omega)⟩
  | succ r ih =>
    obtain ⟨hs',hm'⟩ := ih (by omega)
    have hzero : (∫ x in (0 : ℝ)..1, correctionIterate r f x)=0 := by
      simpa using hm' 0 (by omega)
    refine ⟨correctionPrimitive_support hL hR hLR hs' hzero,?_⟩
    intro k hk
    apply correctionPrimitive_moment_zero (correctionIterate_local hf r) 1 k
    · exact hzero
    · exact hm' (k+1) (by omega)

/-- Evaluation moments at a cut become zero moments after one integration.
Every further uniform integration therefore vanishes at that cut. -/
theorem correctionIterate_cut_moments {f : ℝ → ℝ} (hf : LocallyIntegrable f volume)
    (t c : ℝ) (D : ℕ)
    (hmom : ∀ k < D, (∫ x in (0 : ℝ)..t, f x*x^k)=c*t^k)
    (r : ℕ) (hr : r+1 ≤ D) :
    correctionIterate (r+1) f t=(if r=0 then c else 0) ∧
      ∀ k, k+r+1 < D → (∫ x in (0 : ℝ)..t, correctionIterate (r+1) f x*x^k)=0 := by
  induction r with
  | zero =>
    have hzero : correctionPrimitive f t=c := by simpa [correctionPrimitive] using hmom 0 (by omega)
    refine ⟨by simpa using hzero,?_⟩
    intro k hk
    exact correctionPrimitive_cut_moment hf t c k hzero (hmom (k+1) (by omega))
  | succ r ih =>
    obtain ⟨_,hm'⟩ := ih (by omega)
    have hzero : correctionPrimitive (correctionIterate (r+1) f) t=0 := by
      simpa [correctionPrimitive] using hm' 0 (by omega)
    refine ⟨by simpa using hzero,?_⟩
    intro k hk
    exact correctionPrimitive_moment_zero (correctionIterate_local hf (r+1)) t k hzero
      (hm' (k+1) (by omega))

end FairDice
