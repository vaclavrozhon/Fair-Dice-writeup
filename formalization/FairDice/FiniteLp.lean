import FairDice.FiniteAverages
import Mathlib.Analysis.MeanInequalities

namespace FairDice

variable {Ω : Type*} [Fintype Ω]

theorem finiteLp_nonneg (p : ℝ) (f : Ω → ℝ) : 0 ≤ finiteLp p f := by
  unfold finiteLp
  exact Real.rpow_nonneg (finiteMean_nonneg _ (fun x => Real.rpow_nonneg (abs_nonneg _) _)) _

@[simp] theorem finiteLp_zero {p : ℝ} (hp : 0 < p) : finiteLp p (fun _ : Ω => 0) = 0 := by
  simp [finiteLp, finiteMean, hp.ne', (inv_pos.mpr hp).ne']

theorem finiteLp_const_mul {p : ℝ} (hp : 0 < p) (c : ℝ) (f : Ω → ℝ) :
    finiteLp p (fun x => c*f x) = |c| * finiteLp p f := by
  unfold finiteLp
  have he : (fun x => |c*f x|^p) = (fun x => |c|^p * |f x|^p) := by
    funext x
    rw [abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
  rw [he, finiteMean_const_mul, Real.mul_rpow (Real.rpow_nonneg (abs_nonneg _) _)
    (finiteMean_nonneg _ (fun x => Real.rpow_nonneg (abs_nonneg _) _)),
    ← Real.rpow_mul (abs_nonneg c), mul_inv_cancel₀ hp.ne', Real.rpow_one]

theorem finiteLp_add {p : ℝ} (hp : 1 ≤ p) (f g : Ω → ℝ) :
    finiteLp p (fun x => f x+g x) ≤ finiteLp p f + finiteLp p g := by
  have he (h : Ω → ℝ) : finiteLp p h =
      ((∑ x, |h x|^p)^(p⁻¹))/(Fintype.card Ω : ℝ)^(p⁻¹) := by
    unfold finiteLp finiteMean
    exact Real.div_rpow (Finset.sum_nonneg (fun _ _ => Real.rpow_nonneg (abs_nonneg _) _)) (by positivity) _
  simp only [he, ← add_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  simpa only [one_div] using Real.Lp_add_le Finset.univ f g hp

theorem finiteLp_sum {ι : Type*} {p : ℝ} (hp : 1 ≤ p) (A : Finset ι) (f : ι → Ω → ℝ) :
    finiteLp p (fun x => ∑ i ∈ A, f i x) ≤ ∑ i ∈ A, finiteLp p (f i) := by
  classical
  induction A using Finset.induction_on with
  | empty => simp [finiteLp_zero (by linarith : 0 < p)]
  | @insert i A hi ih =>
    simp only [Finset.sum_insert hi]
    exact (finiteLp_add hp _ _).trans (add_le_add le_rfl ih)

theorem finiteLp_mean {Γ : Type*} [Fintype Γ] {p : ℝ} (hp : 1 ≤ p) (f : Γ → Ω → ℝ) :
    finiteLp p (fun x => finiteMean (fun y => f y x)) ≤ finiteMean (fun y => finiteLp p (f y)) := by
  have he : (fun x => finiteMean (fun y => f y x)) =
      (fun x => (Fintype.card Γ : ℝ)⁻¹ * ∑ y, f y x) := by
    funext x
    simp [finiteMean, div_eq_mul_inv, mul_comm]
  rw [he, finiteLp_const_mul (by linarith : 0 < p)]
  rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ (Fintype.card Γ : ℝ)⁻¹)]
  have hh := mul_le_mul_of_nonneg_left (finiteLp_sum hp Finset.univ f)
    (by positivity : (0 : ℝ) ≤ (Fintype.card Γ : ℝ)⁻¹)
  simpa [finiteMean, div_eq_mul_inv, mul_comm] using hh

theorem finiteMean_sqrt_le [Nonempty Ω] (f : Ω → ℝ) (hf : ∀ x, 0 ≤ f x) :
    finiteMean (fun x => Real.sqrt (f x)) ≤ Real.sqrt (finiteMean f) := by
  have hj := finiteMean_abs_rpow (fun x => Real.sqrt (f x)) 2 (by norm_num)
  have hn : 0 ≤ finiteMean (fun x => Real.sqrt (f x)) := finiteMean_nonneg _ (fun _ => Real.sqrt_nonneg _)
  have he : (fun x => |Real.sqrt (f x)|^(2 : ℝ)) = f := by
    funext x
    simp [abs_of_nonneg (Real.sqrt_nonneg _), Real.rpow_two, Real.sq_sqrt (hf x)]
  rw [he, abs_of_nonneg hn, Real.rpow_two] at hj
  have hs := Real.sq_sqrt (finiteMean_nonneg f hf)
  nlinarith [Real.sqrt_nonneg (finiteMean f)]

@[simp] theorem finiteLp_pow {p : ℝ} (hp : 0 < p) (f : Ω → ℝ) :
    (finiteLp p f)^p = finiteMean (fun x => |f x|^p) := by
  exact Real.rpow_inv_rpow
    (finiteMean_nonneg _ (fun x => Real.rpow_nonneg (abs_nonneg _) _)) hp.ne'

end FairDice
