import FairDice.IteratedCorrections
import FairDice.CorrectedFamily

namespace FairDice

open MeasureTheory Set Polynomial

/-- The local data needed by the ordered-integral argument. The sign also
allows the reflected system, whose left moments are negative evaluations. -/
structure LocalBumpSystem (m K : ℕ) where
  node : Fin K → ℝ
  left : Fin K → ℝ
  right : Fin K → ℝ
  node_bounds : ∀ q, 0 ≤ left q ∧ left q < node q ∧ node q < right q ∧ right q ≤ 1
  disjoint : ∀ q r, q≠r → Disjoint (Ioo (left q) (right q)) (Ioo (left r) (right r))
  bump : Fin K → ℝ → ℝ
  support : ∀ q, Function.support (bump q) ⊆ Ioo (left q) (right q)
  integrableLocal : ∀ q, LocallyIntegrable (bump q) volume
  sign : ℝ
  full : ∀ (q : Fin K) (p : ℝ[X]), p.natDegree < m → (∫ x in (0 : ℝ)..1, bump q x*p.eval x)=0
  cut : ∀ (q : Fin K) (p : ℝ[X]), p.natDegree < m →
    (∫ x in (0 : ℝ)..node q, bump q x*p.eval x)=sign*p.eval (node q)

noncomputable def CorrectedFamily.bumpSystem {m K : ℕ} (C : CorrectedFamily m K) :
    LocalBumpSystem m K := {
  node := fun q => C.node q
  left := C.containerLeft
  right := C.containerRight
  node_bounds := C.container_bounds
  disjoint := C.container_disjoint
  bump := fun q => (C.intervals q).bump (C.node q)
  support := C.bump_support
  integrableLocal := fun q => by
    have hi := (C.intervals q).bump_polynomial_integrable (C.node q) 1
    simp only [eval_one,mul_one] at hi
    exact hi.locallyIntegrable
  sign := 1
  full := fun q p hp => (C.intervals q).full_moments (C.node q) (C.admissible q) p hp
  cut := fun q p hp => by
    simpa using (C.intervals q).left_moments (C.node q) (C.admissible q) p hp }

noncomputable def LocalBumpSystem.weighted {m K : ℕ} (S : LocalBumpSystem m K)
    (q : Fin K) (a : ℕ) (x : ℝ) : ℝ := S.bump q x*x^a/(a.factorial : ℝ)

noncomputable def LocalBumpSystem.response {m K : ℕ} (S : LocalBumpSystem m K)
    (q : Fin K) (a b : ℕ) : ℝ → ℝ := correctionIterate (b+1) (S.weighted q a)

theorem LocalBumpSystem.weighted_local {m K : ℕ} (S : LocalBumpSystem m K)
    (q : Fin K) (a : ℕ) : LocallyIntegrable (S.weighted q a) volume := by
  have h := (local_mul_continuous (S.integrableLocal q) (continuous_id.pow a)).smul
    (a.factorial : ℝ)⁻¹
  convert h using 1
  funext x
  simp only [weighted,Pi.smul_apply,smul_eq_mul,div_eq_mul_inv,Pi.pow_apply,id_eq]
  ring

theorem LocalBumpSystem.weighted_moment {m K : ℕ} (S : LocalBumpSystem m K)
    (q : Fin K) (a k : ℕ) (t : ℝ) :
    (∫ x in (0 : ℝ)..t, S.weighted q a x*x^k) =
      (∫ x in (0 : ℝ)..t, S.bump q x*x^(a+k))/(a.factorial : ℝ) := by
  have he (x : ℝ) : S.weighted q a x*x^k=(S.bump q x*x^(a+k))/(a.factorial : ℝ) := by
    unfold weighted; rw [pow_add]; ring
  simp_rw [he]
  exact intervalIntegral.integral_div _ _

/-- All response profiles remain in their original disjoint intervals. -/
theorem LocalBumpSystem.response_support {m K : ℕ} (S : LocalBumpSystem m K)
    (q : Fin K) (a b : ℕ) (hdeg : a+b < m) :
    Function.support (S.response q a b) ⊆ Ioo (S.left q) (S.right q) := by
  have hbounds := S.node_bounds q
  have hs : Function.support (S.weighted q a) ⊆ Ioo (S.left q) (S.right q) := by
    intro x hx
    apply S.support q
    intro hb
    apply hx
    simp [weighted,hb]
  have hmom (k : ℕ) (hk : k < m-a) : (∫ x in (0 : ℝ)..1, S.weighted q a x*x^k)=0 := by
    rw [S.weighted_moment]
    have hh := S.full q (X^(a+k)) (by simp; omega)
    simp only [eval_pow,eval_X] at hh
    rw [hh,zero_div]
  exact (correctionIterate_support_moments (S.weighted_local q a) hbounds.1 hbounds.2.2.2
    (hbounds.2.1.trans hbounds.2.2.1) hs (m-a) hmom (b+1) (by omega)).1

theorem LocalBumpSystem.response_local {m K : ℕ} (S : LocalBumpSystem m K)
    (q : Fin K) (a b : ℕ) : LocallyIntegrable (S.response q a b) volume :=
  correctionIterate_local (S.weighted_local q a) (b+1)

theorem LocalBumpSystem.response_continuous {m K : ℕ} (S : LocalBumpSystem m K)
    (q : Fin K) (a b : ℕ) : Continuous (S.response q a b) :=
  correctionPrimitive_continuous (correctionIterate_local (S.weighted_local q a) b)

theorem LocalBumpSystem.response_primitive {m K : ℕ} (S : LocalBumpSystem m K)
    (q : Fin K) (a b : ℕ) : correctionPrimitive (S.response q a b)=S.response q a (b+1) := rfl

/-- Only the immediate neighbor response survives at its own cut. -/
theorem LocalBumpSystem.response_at_node {m K : ℕ} (S : LocalBumpSystem m K)
    (q : Fin K) (a b : ℕ) (hdeg : a+b < m) :
    S.response q a b (S.node q)=
      if b=0 then S.sign*(S.node q)^a/(a.factorial : ℝ) else 0 := by
  have hmom (k : ℕ) (hk : k < m-a) :
      (∫ x in (0 : ℝ)..S.node q, S.weighted q a x*x^k)=
        (S.sign*(S.node q)^a/(a.factorial : ℝ))*(S.node q)^k := by
    rw [S.weighted_moment]
    have hh := S.cut q (X^(a+k)) (by simp; omega)
    simp only [eval_pow,eval_X] at hh
    rw [hh,pow_add]
    ring
  exact (correctionIterate_cut_moments (S.weighted_local q a) (S.node q)
    (S.sign*(S.node q)^a/(a.factorial : ℝ)) (m-a) hmom b (by omega)).1

theorem LocalBumpSystem.response_other_node {m K : ℕ} (S : LocalBumpSystem m K)
    (q r : Fin K) (hqr : q≠r) (a b : ℕ) (hdeg : a+b < m) :
    S.response q a b (S.node r)=0 := by
  by_contra h
  have hx := S.response_support q a b hdeg h
  exact Set.disjoint_left.mp (S.disjoint q r hqr) hx
    ⟨(S.node_bounds r).2.1,(S.node_bounds r).2.2.1⟩

/-- A response and a bump from a different interval never interact. This
pointwise identity eliminates every multi-bump term during integration. -/
theorem LocalBumpSystem.response_mul_bump {m K : ℕ} (S : LocalBumpSystem m K)
    (q r : Fin K) (hqr : q≠r) (a b : ℕ) (hdeg : a+b < m) (x : ℝ) :
    S.response q a b x*S.bump r x=0 := by
  by_cases hq : S.response q a b x=0
  · simp [hq]
  · have hzero : S.bump r x=0 := by
      by_contra hr
      exact Set.disjoint_left.mp (S.disjoint q r hqr)
        (S.response_support q a b hdeg hq) (S.support r hr)
    simp [hzero]

end FairDice
