import Mathlib

namespace FairDice

open MeasureTheory

noncomputable def unitIntervalMeasure : Measure ℝ := volume.restrict (Set.Icc 0 1)

instance unitIntervalMeasure_probability : IsProbabilityMeasure unitIntervalMeasure where
  measure_univ := by norm_num [unitIntervalMeasure]

noncomputable def independentLabels (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi (fun _ : ι => unitIntervalMeasure)

instance independentLabels_probability (ι : Type*) [Fintype ι] :
    IsProbabilityMeasure (independentLabels ι) := by
  unfold independentLabels
  infer_instance

def orderedLabels {ι : Type*} {n : ℕ} (e : Fin n → ι) (x : ι → ℝ) : Prop :=
  ∀ i j, i < j → x (e i) < x (e j)

theorem orderedLabels_measurable {ι : Type*} {n : ℕ} (e : Fin n → ι) :
    MeasurableSet {x : ι → ℝ | orderedLabels e x} := by
  unfold orderedLabels
  simp only [Set.setOf_forall]
  exact MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun j =>
    MeasurableSet.iInter (fun _ => measurableSet_lt (measurable_pi_apply _) (measurable_pi_apply _))))

/-- Classical exchangeability/no-ties fact for independent continuous
uniform labels, stated for arbitrary injective coordinate selections. -/
def ContinuousOrderExternal : Prop :=
  ∀ (ι : Type) [Fintype ι] (n : ℕ) (e : Fin n → ι), Function.Injective e →
    (independentLabels ι).real {x | orderedLabels e x} = 1 / (n.factorial : ℝ)

/-- McDiarmid's general bounded-differences inequality, not a dice-specific
conclusion. Measurability, each coordinate bound and the substitution into
the inequality are established below. -/
def BoundedDifferencesExternal : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (F : (ι → ℝ) → ℝ) (c : ι → ℝ),
    Measurable F → (∀ i, 0 ≤ c i) →
    (∀ x y i, (∀ j, j ≠ i → x j = y j) → |F x - F y| ≤ c i) →
    ∀ t : ℝ, 0 < t → 0 < ∑ i, (c i)^2 →
      (independentLabels ι).real {x | t ≤ |F x - ∫ y, F y ∂independentLabels ι|} ≤
        2 * Real.exp (-2 * t^2 / (∑ i, (c i)^2))

noncomputable def orderIndicator {ι : Type*} {n : ℕ} (e : Fin n → ι) (x : ι → ℝ) : ℝ := by
  classical
  exact if orderedLabels e x then 1 else 0

theorem orderIndicator_eq_indicator {ι : Type*} {n : ℕ} (e : Fin n → ι) :
    orderIndicator e = {x | orderedLabels e x}.indicator (fun _ => 1) := by
  classical
  funext x
  simp [orderIndicator, Set.indicator_apply]

theorem orderIndicator_measurable {ι : Type*} {n : ℕ} (e : Fin n → ι) :
    Measurable (orderIndicator e) := by
  rw [orderIndicator_eq_indicator]
  exact measurable_const.indicator (orderedLabels_measurable e)

theorem orderIndicator_integrable {ι : Type*} [Fintype ι] {n : ℕ} (e : Fin n → ι) :
    Integrable (orderIndicator e) (independentLabels ι) := by
  rw [orderIndicator_eq_indicator]
  exact (integrable_const 1).indicator (orderedLabels_measurable e)

/-- One independently chosen face of each die, listed in permutation order. -/
def selectedFaces {n m : ℕ} (p : Equiv.Perm (Fin n)) (f : Fin n → Fin m) :
    Fin n → Fin n × Fin m := fun i => (p i, f (p i))

theorem selectedFaces_injective {n m : ℕ} (p : Equiv.Perm (Fin n)) (f : Fin n → Fin m) :
    Function.Injective (selectedFaces p f) := by
  intro i j h
  exact p.injective (congrArg Prod.fst h)

/-- The overlapping indicator sum in the random-construction paragraph. -/
noncomputable def randomPatternCount {n m : ℕ} (p : Equiv.Perm (Fin n))
    (x : (Fin n × Fin m) → ℝ) : ℝ :=
  ∑ f : Fin n → Fin m, orderIndicator (selectedFaces p f) x

theorem randomPatternCount_measurable {n m : ℕ} (p : Equiv.Perm (Fin n)) :
    Measurable (randomPatternCount (m := m) p) :=
  Finset.measurable_sum _ (fun _ _ => orderIndicator_measurable _)

theorem randomPatternCount_expectation (hext : ContinuousOrderExternal) {n m : ℕ}
    (p : Equiv.Perm (Fin n)) :
    (∫ x, randomPatternCount (m := m) p x ∂independentLabels (Fin n × Fin m)) =
      (m : ℝ)^n / (n.factorial : ℝ) := by
  unfold randomPatternCount
  rw [integral_finsetSum _ (fun _ _ => orderIndicator_integrable _)]
  have hterm (f : Fin n → Fin m) :
      (∫ x, orderIndicator (selectedFaces p f) x ∂independentLabels (Fin n × Fin m)) =
        1 / (n.factorial : ℝ) := by
    rw [orderIndicator_eq_indicator]
    calc
      _ = (independentLabels (Fin n × Fin m)).real
          {x | orderedLabels (selectedFaces p f) x} := by
        exact integral_indicator_one (orderedLabels_measurable _)
      _ = _ := hext _ n _ (selectedFaces_injective p f)
  simp [hterm, div_eq_mul_inv]

theorem face_fiber_card {n m : ℕ} (a : Fin n) (u : Fin m) :
    ((Finset.univ : Finset (Fin n → Fin m)).filter (fun f => f a = u)).card = m^(n - 1) := by
  simpa using Fintype.card_filter_piFinset_const_eq_of_mem
    (ι := Fin n) (Finset.univ : Finset (Fin m)) a (Finset.mem_univ u)

theorem randomPatternCount_bounded_difference {n m : ℕ} (p : Equiv.Perm (Fin n))
    (x y : (Fin n × Fin m) → ℝ) (a : Fin n × Fin m)
    (hxy : ∀ b, b ≠ a → x b = y b) :
    |randomPatternCount p x - randomPatternCount p y| ≤ (m : ℝ)^(n - 1) := by
  classical
  have hterm (f : Fin n → Fin m) :
      |orderIndicator (selectedFaces p f) x - orderIndicator (selectedFaces p f) y| ≤
        if f a.1 = a.2 then 1 else 0 := by
    by_cases hf : f a.1 = a.2
    · simp only [if_pos hf, orderIndicator]
      split_ifs <;> norm_num
    · have he : orderedLabels (selectedFaces p f) x ↔ orderedLabels (selectedFaces p f) y := by
        have hh (i : Fin n) : x (selectedFaces p f i) = y (selectedFaces p f i) := by
          apply hxy
          intro h
          have h1 := congrArg Prod.fst h
          have h2 := congrArg Prod.snd h
          change p i = a.1 at h1
          change f (p i) = a.2 at h2
          exact hf (by rwa [h1] at h2)
        simp only [orderedLabels, hh]
      simp [orderIndicator, he, hf]
  calc
    _ = |∑ f : Fin n → Fin m,
        (orderIndicator (selectedFaces p f) x - orderIndicator (selectedFaces p f) y)| := by
      rw [Finset.sum_sub_distrib]
      rfl
    _ ≤ ∑ f : Fin n → Fin m,
        |orderIndicator (selectedFaces p f) x - orderIndicator (selectedFaces p f) y| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ f : Fin n → Fin m, if f a.1 = a.2 then (1 : ℝ) else 0 :=
      Finset.sum_le_sum (fun f _ => hterm f)
    _ = _ := by
      rw [← Nat.cast_pow, ← face_fiber_card a.1 a.2, Finset.card_filter]
      simp

theorem randomPatternCount_tail (horder : ContinuousOrderExternal)
    (hbd : BoundedDifferencesExternal) {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (p : Equiv.Perm (Fin n)) {ε : ℝ} (hε : 0 < ε) :
    (independentLabels (Fin n × Fin m)).real
      {x | ε * (m : ℝ)^n / (n.factorial : ℝ) ≤
        |randomPatternCount p x - (m : ℝ)^n / (n.factorial : ℝ)|} ≤
      2 * Real.exp (-2 * ε^2 * m / ((n : ℝ) * (n.factorial : ℝ)^2)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hfacR : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hsum : (∑ _ : Fin n × Fin m, ((m : ℝ)^(n - 1))^2) =
      (n : ℝ) * m * ((m : ℝ)^(n - 1))^2 := by simp [Fintype.card_prod, mul_assoc]
  have hh := hbd (Fin n × Fin m) (randomPatternCount p) (fun _ => (m : ℝ)^(n - 1))
    (randomPatternCount_measurable p) (fun _ => by positivity)
    (randomPatternCount_bounded_difference p)
    (ε * (m : ℝ)^n / (n.factorial : ℝ)) (by positivity) (by rw [hsum]; positivity)
  rw [randomPatternCount_expectation horder, hsum] at hh
  convert hh using 1
  congr 2
  have hpow : (m : ℝ)^n = (m : ℝ)^(n - 1) * m := by
    rw [← pow_succ, Nat.sub_add_cancel hn]
  rw [hpow]
  field_simp

/-- The dependency neighborhood of one outcome has at most this many
members, including the outcome itself. -/
theorem outcome_overlap_bound {n m : ℕ} (f : Fin n → Fin m) :
    ((Finset.univ : Finset (Fin n → Fin m)).filter (fun g => ∃ a, g a = f a)).card ≤
      n * m^(n - 1) := by
  classical
  have he : ((Finset.univ : Finset (Fin n → Fin m)).filter (fun g => ∃ a, g a = f a)) =
      (Finset.univ : Finset (Fin n)).biUnion
        (fun a => Finset.univ.filter (fun g : Fin n → Fin m => g a = f a)) := by
    ext g
    simp
  rw [he]
  apply Finset.card_biUnion_le.trans
  simp [face_fiber_card]

/-- Applying a union bound retains the factorial factor; this formalizes
the limitation of the direct concentration argument, not a lower bound on
what a sharper analysis of random dice could achieve. -/
theorem random_all_patterns_tail (horder : ContinuousOrderExternal)
    (hbd : BoundedDifferencesExternal) {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    {ε : ℝ} (hε : 0 < ε) :
    (independentLabels (Fin n × Fin m)).real
      {x | ∃ p : Equiv.Perm (Fin n), ε * (m : ℝ)^n / (n.factorial : ℝ) ≤
        |randomPatternCount p x - (m : ℝ)^n / (n.factorial : ℝ)|} ≤
      2 * n.factorial * Real.exp (-2 * ε^2 * m / ((n : ℝ) * (n.factorial : ℝ)^2)) := by
  rw [Set.setOf_exists]
  refine (measureReal_iUnion_fintype_le _).trans ?_
  calc
    _ ≤ ∑ _ : Equiv.Perm (Fin n),
        2 * Real.exp (-2 * ε^2 * m / ((n : ℝ) * (n.factorial : ℝ)^2)) :=
      Finset.sum_le_sum (fun p _ => randomPatternCount_tail horder hbd hn hm p hε)
    _ = _ := by simp [Fintype.card_perm]; ring

end FairDice
