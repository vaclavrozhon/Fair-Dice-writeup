import FairDice.PalindromeSeries
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.Jensen

namespace FairDice

/-- Expectation on a finite uniform probability space. -/
noncomputable def finiteMean {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) : ℝ :=
  (∑ x, f x)/(Fintype.card Ω : ℝ)

variable {Ω : Type*} [Fintype Ω]

theorem finiteMean_nonneg (f : Ω → ℝ) (hf : ∀ x, 0 ≤ f x) : 0 ≤ finiteMean f := by
  unfold finiteMean
  exact div_nonneg (Finset.sum_nonneg (fun x _ => hf x)) (by positivity)

theorem finiteMean_mono {f g : Ω → ℝ} (h : ∀ x, f x ≤ g x) : finiteMean f ≤ finiteMean g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum (fun x _ => h x)) (by positivity)

@[simp] theorem finiteMean_const [Nonempty Ω] (c : ℝ) : finiteMean (fun _ : Ω => c) = c := by
  simp [finiteMean, Fintype.card_ne_zero]

@[simp] theorem finiteMean_add (f g : Ω → ℝ) :
    finiteMean (fun x => f x+g x) = finiteMean f + finiteMean g := by
  simp [finiteMean, Finset.sum_add_distrib, add_div]

@[simp] theorem finiteMean_sub (f g : Ω → ℝ) :
    finiteMean (fun x => f x-g x) = finiteMean f - finiteMean g := by
  simp [finiteMean, Finset.sum_sub_distrib, sub_div]

@[simp] theorem finiteMean_mul_const (f : Ω → ℝ) (c : ℝ) :
    finiteMean (fun x => f x*c) = finiteMean f * c := by
  simp only [finiteMean, ← Finset.sum_mul]
  ring

@[simp] theorem finiteMean_const_mul (c : ℝ) (f : Ω → ℝ) :
    finiteMean (fun x => c*f x) = c * finiteMean f := by
  simp only [finiteMean, ← Finset.mul_sum]
  ring

theorem finiteMean_sum {ι : Type*} (s : Finset ι) (f : ι → Ω → ℝ) :
    finiteMean (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, finiteMean (f i) := by
  simp only [finiteMean]
  rw [Finset.sum_comm, Finset.sum_div]

theorem finiteMean_equiv {Γ : Type*} [Fintype Γ] (e : Ω ≃ Γ) (f : Γ → ℝ) :
    finiteMean (fun x => f (e x)) = finiteMean f := by
  unfold finiteMean
  rw [Fintype.card_congr e, Fintype.sum_equiv e _ _ (fun _ => rfl)]

theorem finiteMean_prod {Γ : Type*} [Fintype Γ] (f : Ω × Γ → ℝ) :
    finiteMean f = finiteMean (fun x => finiteMean (fun y => f (x,y))) := by
  simp only [finiteMean, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul, ← Finset.sum_div]
  ring

theorem finiteMean_pi_product {ι : Type*} [Fintype ι] [DecidableEq ι] (Γ : ι → Type*)
    [∀ i, Fintype (Γ i)] (f : ∀ i, Γ i → ℝ) :
    finiteMean (fun x : ∀ i, Γ i => ∏ i, f i (x i)) = ∏ i, finiteMean (f i) := by
  classical
  simp only [finiteMean, Fintype.card_pi, Nat.cast_prod, ← Fintype.prod_sum, Finset.prod_div_distrib]

theorem finiteMean_pi_subproduct {ι : Type*} [Fintype ι] [DecidableEq ι] (Γ : ι → Type*)
    [∀ i, Fintype (Γ i)] [∀ i, Nonempty (Γ i)]
    (A : Finset ι) (f : ∀ i, Γ i → ℝ) :
    finiteMean (fun x : ∀ i, Γ i => ∏ i ∈ A, f i (x i)) = ∏ i ∈ A, finiteMean (f i) := by
  classical
  have hp (x : ∀ i, Γ i) : (∏ i, if i ∈ A then f i (x i) else 1) = ∏ i ∈ A, f i (x i) := by
    simpa using Finset.prod_ite_mem Finset.univ A (fun i => f i (x i))
  have hm (i : ι) : finiteMean (fun x : Γ i => if i ∈ A then f i x else 1) =
      if i ∈ A then finiteMean (f i) else 1 := by
    by_cases hi : i ∈ A <;> simp [hi]
  rw [show (fun x : ∀ i, Γ i => ∏ i ∈ A, f i (x i)) =
      (fun x => ∏ i, if i ∈ A then f i (x i) else 1) from funext (fun x => (hp x).symm),
    finiteMean_pi_product Γ (fun i x => if i ∈ A then f i x else 1)]
  simp only [hm]
  simpa using Finset.prod_ite_mem Finset.univ A (fun i => finiteMean (f i))

/-- Finite Jensen inequality needed for the independent-copy argument.
This is derived from mathlib's convexity of the real power function. -/
theorem finiteMean_abs_rpow [Nonempty Ω] (f : Ω → ℝ) (p : ℝ) (hp : 1 ≤ p) :
    |finiteMean f|^p ≤ finiteMean (fun x => |f x|^p) := by
  have hcard : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  have habs : |finiteMean f| ≤ finiteMean (fun x => |f x|) := by
    unfold finiteMean
    rw [abs_div, abs_of_pos hcard]
    exact div_le_div_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) hcard.le
  have hj := (convexOn_rpow hp).map_sum_le (t := Finset.univ)
    (w := fun _ : Ω => (Fintype.card Ω : ℝ)⁻¹) (p := fun x => |f x|)
    (fun _ _ => inv_nonneg.mpr hcard.le) (by simp [hcard.ne'])
    (fun x _ => abs_nonneg (f x))
  have he (g : Ω → ℝ) : (∑ x, (Fintype.card Ω : ℝ)⁻¹ • g x) = finiteMean g := by
    simp only [finiteMean, smul_eq_mul, ← Finset.mul_sum]
    ring
  rw [he, he] at hj
  exact (Real.rpow_le_rpow (abs_nonneg _) habs (by linarith)).trans hj

noncomputable def finiteLp {Ω : Type*} [Fintype Ω] (p : ℝ) (f : Ω → ℝ) : ℝ :=
  (finiteMean (fun x => |f x|^p))^(p⁻¹)

theorem finiteLp_le_of_moment {p C : ℝ} (hp : 0 < p) (hC : 0 ≤ C) (f : Ω → ℝ)
    (h : finiteMean (fun x => |f x|^p) ≤ C^p) : finiteLp p f ≤ C := by
  unfold finiteLp
  have hn : 0 ≤ finiteMean (fun x => |f x|^p) :=
    finiteMean_nonneg _ (fun x => Real.rpow_nonneg (abs_nonneg _) _)
  calc
    _ ≤ (C^p)^(p⁻¹) := Real.rpow_le_rpow hn h (inv_nonneg.mpr hp.le)
    _ = C := by rw [← Real.rpow_mul hC, mul_inv_cancel₀ hp.ne', Real.rpow_one]

end FairDice
