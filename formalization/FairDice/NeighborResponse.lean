import FairDice.DensityCorrection

namespace FairDice

open Polynomial MeasureTheory

/-- The literal kernel left after integrating the uniform variables
around a chosen bump before the distinguished variable. -/
noncomputable def predecessorKernel (a b c : ℕ) (t : ℝ) : ℝ[X] :=
  C ((1-t)^c/((a.factorial : ℝ)*b.factorial*c.factorial)) * X^a * (C t-X)^b

/-- The corresponding kernel for a chosen bump after the distinguished
variable. Here `a` counts variables between it and the distinguished one. -/
noncomputable def successorKernel (k a b : ℕ) (t : ℝ) : ℝ[X] :=
  C (t^k/((k.factorial : ℝ)*a.factorial*b.factorial)) * (X-C t)^a * (1-X)^b

theorem predecessorKernel_degree (a b c : ℕ) (t : ℝ) :
    (predecessorKernel a b c t).natDegree ≤ a+b := by
  apply natDegree_mul_le.trans
  have hC : (C ((1-t)^c/((a.factorial : ℝ)*b.factorial*c.factorial))*X^a).natDegree ≤ a := by
    simpa using natDegree_C_mul_le _ (X^a : ℝ[X])
  have ht : (C t-X : ℝ[X]).natDegree ≤ 1 := by
    apply (natDegree_sub_le _ _).trans
    simp
  have hb : ((C t-X : ℝ[X])^b).natDegree ≤ b := by
    rw [natDegree_pow]
    nlinarith
  omega

theorem successorKernel_degree (k a b : ℕ) (t : ℝ) :
    (successorKernel k a b t).natDegree ≤ a+b := by
  apply natDegree_mul_le.trans
  have ht : (X-C t : ℝ[X]).natDegree ≤ 1 := by simp
  have ha : ((X-C t : ℝ[X])^a).natDegree ≤ a := by
    rw [natDegree_pow]
    nlinarith
  have hC : (C (t^k/((k.factorial : ℝ)*a.factorial*b.factorial))*(X-C t)^a).natDegree ≤ a :=
    (natDegree_C_mul_le _ _).trans ha
  have h1 : (1-X : ℝ[X]).natDegree ≤ 1 := by apply (natDegree_sub_le _ _).trans; simp
  have hb : ((1-X : ℝ[X])^b).natDegree ≤ b := by rw [natDegree_pow]; nlinarith
  omega

/-- Every one-bump contribution before the distinguished variable is zero
unless that variable is its immediate predecessor. The integral is the
actual piecewise-constant bump integral. -/
theorem predecessor_bump_response {m : ℕ} (I : CorrectionIntervals m) (t : ℝ)
    (ht : I.admissible t) (a b c : ℕ) (hdeg : a+b < m) :
    (∫ x in (0 : ℝ)..t, I.bump t x *
      (x^a*(t-x)^b*(1-t)^c/((a.factorial : ℝ)*b.factorial*c.factorial))) =
      if b=0 then t^a*(1-t)^c/((a.factorial : ℝ)*c.factorial) else 0 := by
  have hh := I.left_moments t ht (predecessorKernel a b c t)
    ((predecessorKernel_degree a b c t).trans_lt hdeg)
  have he (x : ℝ) : (predecessorKernel a b c t).eval x =
      x^a*(t-x)^b*(1-t)^c/((a.factorial : ℝ)*b.factorial*c.factorial) := by
    simp [predecessorKernel]
    ring
  simp only [he] at hh
  rw [hh]
  by_cases hb : b=0
  · subst b
    simp
  · simp [hb]

/-- The right moment identity gives a negative correction from the immediate
successor, and zero from all more distant successors. -/
theorem successor_bump_response {m : ℕ} (I : CorrectionIntervals m) (t : ℝ)
    (ht : I.admissible t) (k a b : ℕ) (hdeg : a+b < m) :
    (∫ x in t..(1 : ℝ), I.bump t x *
      (t^k*(x-t)^a*(1-x)^b/((k.factorial : ℝ)*a.factorial*b.factorial))) =
      if a=0 then -(t^k*(1-t)^b/((k.factorial : ℝ)*b.factorial)) else 0 := by
  have hh := I.right_moments t ht (successorKernel k a b t)
    ((successorKernel_degree k a b t).trans_lt hdeg)
  have he (x : ℝ) : (successorKernel k a b t).eval x =
      t^k*(x-t)^a*(1-x)^b/((k.factorial : ℝ)*a.factorial*b.factorial) := by
    simp [successorKernel]
    ring
  simp only [he] at hh
  rw [hh]
  by_cases ha : a=0
  · subst a
    simp
  · simp [ha]

end FairDice
