import FairDice.FiniteLp

namespace FairDice

noncomputable def keepIndicator (b : Bool) : ℝ := if b then 1 else 0

@[simp] theorem keepIndicator_sq (b : Bool) : (keepIndicator b)^2 = keepIndicator b := by
  cases b <;> norm_num [keepIndicator]

theorem keepIndicator_nonneg (b : Bool) : 0 ≤ keepIndicator b := by
  cases b <;> norm_num [keepIndicator]

variable {Γ Ω τ : Type*} [Fintype Γ] [Nonempty Γ] [Fintype Ω] [Fintype τ]

/-- Literal retention and inverse-probability rescaling of a finite sum. -/
noncomputable def coloredSum (keep : Γ → τ → Bool) (π c : τ → ℝ)
    (G : τ → Ω → ℝ) (r : Γ) (x : Ω) : ℝ :=
  ∑ a, (c a / π a) * keepIndicator (keep r a) * G a x

/-- Squared coefficients after retention; the indicator is squared in the
actual definition, so the cancellation of one retention probability is proved. -/
noncomputable def coloredEnergy (keep : Γ → τ → Bool) (π c b : τ → ℝ) (r : Γ) : ℝ :=
  ∑ a, ((c a / π a) * keepIndicator (keep r a))^2 * (b a)^2

theorem coloredSum_mean (keep : Γ → τ → Bool) (π c : τ → ℝ)
    (hπ : ∀ a, π a ≠ 0) (hkeep : ∀ a, finiteMean (fun r => keepIndicator (keep r a)) = π a)
    (G : τ → Ω → ℝ) (x : Ω) :
    finiteMean (fun r => coloredSum keep π c G r x) = ∑ a, c a * G a x := by
  unfold coloredSum
  rw [finiteMean_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [finiteMean_mul_const, finiteMean_const_mul, hkeep]
  field_simp [hπ a]

theorem coloredEnergy_nonneg (keep : Γ → τ → Bool) (π c b : τ → ℝ) (r : Γ) :
    0 ≤ coloredEnergy keep π c b r :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))

/-- Averaging the actual squared coefficients gives the paper's single
inverse retention factor, rather than its square. -/
theorem coloredEnergy_mean (keep : Γ → τ → Bool) (π c b : τ → ℝ)
    (hπ : ∀ a, π a ≠ 0) (hkeep : ∀ a, finiteMean (fun r => keepIndicator (keep r a)) = π a) :
    finiteMean (coloredEnergy keep π c b) = ∑ a, (c a)^2 * (b a)^2 / π a := by
  unfold coloredEnergy
  simp only [mul_pow, keepIndicator_sq]
  rw [finiteMean_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [finiteMean_mul_const, finiteMean_const_mul, hkeep]
  field_simp

/-- The averaging and square-root Jensen part of `eq:palindrome-colored`.
The fixed-color norm estimate is a hypothesis: this theorem does not assert
that overlapping palindrome segments are independent. -/
theorem colored_average_bound (keep : Γ → τ → Bool) (π c b : τ → ℝ)
    (hπ : ∀ a, π a ≠ 0) (hkeep : ∀ a, finiteMean (fun r => keepIndicator (keep r a)) = π a)
    (G : τ → Ω → ℝ) (p : ℝ) (hp : 1 ≤ p) (F : ℝ) (hF : 0 ≤ F)
    (hfixed : ∀ r, finiteLp p (coloredSum keep π c G r) ≤ F * Real.sqrt (coloredEnergy keep π c b r)) :
    finiteLp p (fun x => ∑ a, c a * G a x) ≤
      F * Real.sqrt (∑ a, (c a)^2 * (b a)^2 / π a) := by
  rw [← show (fun x => finiteMean (fun r => coloredSum keep π c G r x)) =
    (fun x => ∑ a, c a * G a x) from funext (coloredSum_mean keep π c hπ hkeep G)]
  calc
    _ ≤ finiteMean (fun r => finiteLp p (coloredSum keep π c G r)) := finiteLp_mean hp _
    _ ≤ finiteMean (fun r => F * Real.sqrt (coloredEnergy keep π c b r)) := finiteMean_mono hfixed
    _ = F * finiteMean (fun r => Real.sqrt (coloredEnergy keep π c b r)) := finiteMean_const_mul _ _
    _ ≤ F * Real.sqrt (finiteMean (coloredEnergy keep π c b)) :=
      mul_le_mul_of_nonneg_left (finiteMean_sqrt_le _ (coloredEnergy_nonneg keep π c b)) hF
    _ = _ := by rw [coloredEnergy_mean keep π c b hπ hkeep]

/-- Terms with zero coefficients need no retention-law premise. This
allows indexing the actual expansion by all finite subsets of segments,
including subsets containing several segments in the same block. -/
theorem colored_average_bound_supported (keep : Γ → τ → Bool) (π c b : τ → ℝ)
    (hπ : ∀ a, π a ≠ 0)
    (hkeep : ∀ a, c a≠0 → finiteMean (fun r => keepIndicator (keep r a))=π a)
    (G : τ → Ω → ℝ) (p : ℝ) (hp : 1 ≤ p) (F : ℝ) (hF : 0 ≤ F)
    (hfixed : ∀ r, finiteLp p (coloredSum keep π c G r) ≤
      F*Real.sqrt (coloredEnergy keep π c b r)) :
    finiteLp p (fun x => ∑ a, c a*G a x) ≤
      F*Real.sqrt (∑ a, (c a)^2*(b a)^2/π a) := by
  classical
  let K := fun r a => if c a=0 then true else keep r a
  let Q := fun a => if c a=0 then (1 : ℝ) else π a
  have hQ (a : τ) : Q a≠0 := by
    by_cases ha : c a=0 <;> simp [Q,ha,hπ a]
  have hK (a : τ) : finiteMean (fun r => keepIndicator (K r a))=Q a := by
    by_cases ha : c a=0
    · simp [K,Q,ha,keepIndicator]
    · simpa [K,Q,ha] using hkeep a ha
  have hs (r : Γ) : coloredSum K Q c G r=coloredSum keep π c G r := by
    funext x
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : c a=0 <;> simp [K,Q,ha]
  have he (r : Γ) : coloredEnergy K Q c b r=coloredEnergy keep π c b r := by
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : c a=0 <;> simp [K,Q,ha]
  have hbound := colored_average_bound K Q c b hQ hK G p hp F hF
    (fun r => by rw [hs,he]; exact hfixed r)
  have hr : (∑ a, (c a)^2*(b a)^2/Q a)=(∑ a, (c a)^2*(b a)^2/π a) := by
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : c a=0 <;> simp [Q,ha]
  rwa [hr] at hbound

end FairDice
