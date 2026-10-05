import FairDice.LocalCorrections

namespace FairDice

open Polynomial MeasureTheory Set

/-- Fixed rational support intervals to the left and right of a moving cut. -/
structure CorrectionIntervals (m : ℕ) where
  la : Fin m → ℚ
  lb : Fin m → ℚ
  ra : Fin m → ℚ
  rb : Fin m → ℚ
  left_pos : ∀ j, la j < lb j
  right_pos : ∀ j, ra j < rb j
  left_order : ∀ i j, i < j → lb i < la j
  right_order : ∀ i j, i < j → rb i < ra j
  left_unit : ∀ j, 0 ≤ la j ∧ lb j ≤ 1
  right_unit : ∀ j, 0 ≤ ra j ∧ rb j ≤ 1

variable {m : ℕ}

abbrev CorrectionIntervals.leftA (I : CorrectionIntervals m) (j : Fin m) : ℝ := I.la j
abbrev CorrectionIntervals.leftB (I : CorrectionIntervals m) (j : Fin m) : ℝ := I.lb j
abbrev CorrectionIntervals.rightA (I : CorrectionIntervals m) (j : Fin m) : ℝ := I.ra j
abbrev CorrectionIntervals.rightB (I : CorrectionIntervals m) (j : Fin m) : ℝ := I.rb j

noncomputable abbrev CorrectionIntervals.leftCoefficients (I : CorrectionIntervals m) (t : ℝ) :=
  intervalCorrection I.leftA I.leftB t
noncomputable abbrev CorrectionIntervals.rightCoefficients (I : CorrectionIntervals m) (t : ℝ) :=
  intervalCorrection I.rightA I.rightB t

/-- The actual centered piecewise constant bump from
`individual-centered-bumps`. Its support breakpoints are rational and fixed. -/
noncomputable def CorrectionIntervals.bump (I : CorrectionIntervals m) (t x : ℝ) : ℝ :=
  momentStep I.leftA I.leftB (I.leftCoefficients t) x -
    momentStep I.rightA I.rightB (I.rightCoefficients t) x

def CorrectionIntervals.admissible (I : CorrectionIntervals m) (t : ℝ) : Prop :=
  0 ≤ t ∧ t ≤ 1 ∧ (∀ j, I.leftB j < t) ∧ ∀ j, t ≤ I.rightA j

private theorem left_pos_real (I : CorrectionIntervals m) (j : Fin m) : I.leftA j < I.leftB j := by
  exact_mod_cast I.left_pos j
private theorem right_pos_real (I : CorrectionIntervals m) (j : Fin m) : I.rightA j < I.rightB j := by
  exact_mod_cast I.right_pos j
private theorem left_order_real (I : CorrectionIntervals m) (i j : Fin m) (hij : i < j) :
    I.leftB i < I.leftA j := by exact_mod_cast I.left_order i j hij
private theorem right_order_real (I : CorrectionIntervals m) (i j : Fin m) (hij : i < j) :
    I.rightB i < I.rightA j := by exact_mod_cast I.right_order i j hij

theorem CorrectionIntervals.left_moments (I : CorrectionIntervals m) (t : ℝ)
    (ht : I.admissible t) (p : ℝ[X]) (hp : p.natDegree < m) :
    (∫ x in (0 : ℝ)..t, I.bump t x * p.eval x) = p.eval t := by
  have hL := momentStep_integrable I.leftA I.leftB (I.leftCoefficients t)
    (fun j => (left_pos_real I j).le) p
  have hR := momentStep_integrable I.rightA I.rightB (I.rightCoefficients t)
    (fun j => (right_pos_real I j).le) p
  simp only [bump, sub_mul]
  rw [intervalIntegral.integral_sub hL.intervalIntegrable hR.intervalIntegrable,
    momentStep_integral I.leftA I.leftB _ (fun j => (left_pos_real I j).le) 0 t
      (fun j => by exact_mod_cast (I.left_unit j).1) (fun j => (ht.2.2.1 j).le),
    momentStep_integral_before I.rightA I.rightB _ 0 t ht.1 ht.2.2.2 p, sub_zero]
  exact intervalCorrection_exact _ _ (left_pos_real I) (left_order_real I) t p hp

theorem CorrectionIntervals.right_moments (I : CorrectionIntervals m) (t : ℝ)
    (ht : I.admissible t) (p : ℝ[X]) (hp : p.natDegree < m) :
    (∫ x in t..(1 : ℝ), I.bump t x * p.eval x) = -p.eval t := by
  have hL := momentStep_integrable I.leftA I.leftB (I.leftCoefficients t)
    (fun j => (left_pos_real I j).le) p
  have hR := momentStep_integrable I.rightA I.rightB (I.rightCoefficients t)
    (fun j => (right_pos_real I j).le) p
  simp only [bump, sub_mul]
  rw [intervalIntegral.integral_sub hL.intervalIntegrable hR.intervalIntegrable,
    momentStep_integral_after I.leftA I.leftB _ t 1 ht.2.1 ht.2.2.1 p,
    momentStep_integral I.rightA I.rightB _ (fun j => (right_pos_real I j).le) t 1
      ht.2.2.2 (fun j => by exact_mod_cast (I.right_unit j).2)]
  rw [intervalCorrection_exact _ _ (right_pos_real I) (right_order_real I) t p hp]
  ring

theorem CorrectionIntervals.full_moments (I : CorrectionIntervals m) (t : ℝ)
    (ht : I.admissible t) (p : ℝ[X]) (hp : p.natDegree < m) :
    (∫ x in (0 : ℝ)..1, I.bump t x * p.eval x) = 0 := by
  have hi : Integrable (fun x => I.bump t x * p.eval x) volume := by
    simp only [bump, sub_mul]
    exact (momentStep_integrable _ _ _ (fun j => (left_pos_real I j).le) p).sub
      (momentStep_integrable _ _ _ (fun j => (right_pos_real I j).le) p)
  rw [← intervalIntegral.integral_add_adjacent_intervals hi.intervalIntegrable hi.intervalIntegrable,
    I.left_moments t ht p hp, I.right_moments t ht p hp]
  ring

/-- Rationality includes the actual values of the step function, not just
the moment matrices. -/
theorem CorrectionIntervals.bump_rational (I : CorrectionIntervals m) (t : ℚ) (x : ℝ) :
    ∃ r : ℚ, I.bump t x = r := by
  classical
  obtain ⟨l, hl⟩ := intervalCorrection_rational I.la I.lb I.left_pos I.left_order t
  obtain ⟨r, hr⟩ := intervalCorrection_rational I.ra I.rb I.right_pos I.right_order t
  refine ⟨(∑ j, if x ∈ Ioc (I.leftA j) (I.leftB j) then l j else 0) -
    (∑ j, if x ∈ Ioc (I.rightA j) (I.rightB j) then r j else 0), ?_⟩
  simp only [bump, momentStep, leftCoefficients, rightCoefficients]
  push_cast
  congr 1 <;> apply Finset.sum_congr rfl <;> intro j _
  · rw [hl j]
    by_cases hx : x ∈ Ioc (I.leftA j) (I.leftB j) <;> simp [hx]
  · rw [hr j]
    by_cases hx : x ∈ Ioc (I.rightA j) (I.rightB j) <;> simp [hx]

theorem momentStep_bound (a b : Fin m → ℝ) (c : Fin m → ℝ) (x : ℝ) :
    |momentStep a b c x| ≤ ∑ j, |c j| := by
  unfold momentStep
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j _
  by_cases hx : x ∈ Ioc (a j) (b j) <;> simp [hx]

noncomputable def CorrectionIntervals.coefficientBound (I : CorrectionIntervals m) (t : ℝ) : ℝ :=
  (∑ j, |I.leftCoefficients t j|) + ∑ j, |I.rightCoefficients t j|

theorem CorrectionIntervals.bump_bound (I : CorrectionIntervals m) (t x : ℝ) :
    |I.bump t x| ≤ I.coefficientBound t := by
  exact (abs_sub _ _).trans (add_le_add (momentStep_bound _ _ _ _) (momentStep_bound _ _ _ _))

theorem CorrectionIntervals.coefficientBound_continuous (I : CorrectionIntervals m) :
    Continuous I.coefficientBound := by
  exact (continuous_finsetSum _ (fun j _ =>
    (intervalCorrection_continuous I.leftA I.leftB j).abs)).add
    (continuous_finsetSum _ (fun j _ => (intervalCorrection_continuous I.rightA I.rightB j).abs))

/-- Uniform boundedness in an explicit open neighborhood follows from the
continuous coefficient vectors, with no assumption on the moving cut. -/
theorem CorrectionIntervals.locally_bounded (I : CorrectionIntervals m) (u : ℝ) :
    ∃ V : Set ℝ, IsOpen V ∧ u ∈ V ∧ ∃ C : ℝ, 0 < C ∧
      ∀ t ∈ V, ∀ x : ℝ, |I.bump t x| ≤ C := by
  let C := I.coefficientBound u + 1
  refine ⟨{t | I.coefficientBound t < C},
    isOpen_lt I.coefficientBound_continuous continuous_const, by dsimp [C]; linarith,
    C, ?_, fun t ht x => (I.bump_bound t x).trans ht.le⟩
  have h : 0 ≤ I.coefficientBound u := by
    unfold coefficientBound
    exact add_nonneg (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
      (Finset.sum_nonneg (fun _ _ => abs_nonneg _))
  dsimp [C]
  linarith

/-- The support stays inside any interval containing all fixed breakpoints. -/
theorem CorrectionIntervals.support_subset (I : CorrectionIntervals m) (t L R : ℝ)
    (hL : ∀ j, L < I.leftA j ∧ L < I.rightA j)
    (hR : ∀ j, I.leftB j < R ∧ I.rightB j < R) :
    Function.support (I.bump t) ⊆ Ioo L R := by
  intro x hx
  by_contra h
  have hleft (j : Fin m) : x ∉ Ioc (I.leftA j) (I.leftB j) := by
    intro hh
    exact h ⟨(hL j).1.trans hh.1, hh.2.trans_lt (hR j).1⟩
  have hright (j : Fin m) : x ∉ Ioc (I.rightA j) (I.rightB j) := by
    intro hh
    exact h ⟨(hL j).2.trans hh.1, hh.2.trans_lt (hR j).2⟩
  exact hx (by simp [bump, momentStep, hleft, hright])

end FairDice
