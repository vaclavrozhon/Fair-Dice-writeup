import FairDice.LocalBumpSystem

namespace FairDice

open MeasureTheory Set Polynomial

theorem LocalBumpSystem.bump_integrable {m K : ℕ} (S : LocalBumpSystem m K) (q : Fin K) :
    Integrable (S.bump q) volume :=
  (integrableOn_iff_integrable_of_support_subset
    ((S.support q).trans Ioo_subset_Icc_self)).mp
      ((S.integrableLocal q).integrableOn_isCompact isCompact_Icc)

noncomputable def reflectPolynomial (p : ℝ[X]) : ℝ[X] := p.comp (1-X)

theorem reflectPolynomial_eval (p : ℝ[X]) (x : ℝ) :
    (reflectPolynomial p).eval x=p.eval (1-x) := by simp [reflectPolynomial]

theorem reflectPolynomial_degree (p : ℝ[X]) :
    (reflectPolynomial p).natDegree ≤ p.natDegree := by
  apply natDegree_comp_le.trans
  have hx : (1-X : ℝ[X]).natDegree ≤ 1 :=
    (natDegree_sub_le (1 : ℝ[X]) X).trans (by simp)
  nlinarith

theorem reflected_bump_integral {m K : ℕ} (S : LocalBumpSystem m K)
    (q : Fin K) (p : ℝ[X]) (t : ℝ) :
    (∫ x in (0 : ℝ)..t, S.bump q (1-x)*p.eval x) =
      ∫ x in (1-t)..1, S.bump q x*(reflectPolynomial p).eval x := by
  have he (x : ℝ) : S.bump q (1-x)*p.eval x=
      (fun y => S.bump q y*(reflectPolynomial p).eval y) (1-x) := by
    dsimp only
    rw [reflectPolynomial_eval,show 1-(1-x)=x by ring]
  calc
    _ = ∫ x in (0 : ℝ)..t, (fun y => S.bump q y*(reflectPolynomial p).eval y) (1-x) :=
      intervalIntegral.integral_congr (fun x _ => he x)
    _ = _ := by
      simpa only [sub_zero] using intervalIntegral.integral_comp_sub_left
        (a := (0 : ℝ)) (b := t) (fun y => S.bump q y*(reflectPolynomial p).eval y) 1

/-- Reflection supplies the right-hand ordered-integral calculation from
the same verified left-hand argument. -/
noncomputable def LocalBumpSystem.reflect {m K : ℕ} (S : LocalBumpSystem m K) :
    LocalBumpSystem m K := {
  node := fun q => 1-S.node q
  left := fun q => 1-S.right q
  right := fun q => 1-S.left q
  node_bounds := fun q => by
    have h := S.node_bounds q
    exact ⟨by linarith,by linarith,by linarith,by linarith⟩
  disjoint := fun q r hqr => by
    apply Set.disjoint_left.mpr
    intro x hx hy
    have hqx : 1-x ∈ Ioo (S.left q) (S.right q) :=
      ⟨by linarith [hx.2],by linarith [hx.1]⟩
    have hrx : 1-x ∈ Ioo (S.left r) (S.right r) :=
      ⟨by linarith [hy.2],by linarith [hy.1]⟩
    exact Set.disjoint_left.mp (S.disjoint q r hqr) hqx hrx
  bump := fun q x => S.bump q (1-x)
  support := fun q x hx => by
    have h := S.support q hx
    exact ⟨by linarith [h.2],by linarith [h.1]⟩
  integrableLocal := fun q =>
    ((volume.measurePreserving_sub_left 1).integrable_comp_of_integrable (S.bump_integrable q)).locallyIntegrable
  sign := -S.sign
  full := fun q p hp => by
    rw [reflected_bump_integral]
    norm_num
    exact S.full q (reflectPolynomial p) ((reflectPolynomial_degree p).trans_lt hp)
  cut := fun q p hp => by
    rw [reflected_bump_integral]
    have ht : 1-(1-S.node q)=S.node q := by ring
    rw [ht]
    have hdeg := (reflectPolynomial_degree p).trans_lt hp
    have hi := local_mul_continuous (S.integrableLocal q) (reflectPolynomial p).continuous
    have hh := intervalIntegral.integral_add_adjacent_intervals
      (local_interval_integrable hi 0 (S.node q)) (local_interval_integrable hi (S.node q) 1)
    rw [S.full q _ hdeg,S.cut q _ hdeg,reflectPolynomial_eval] at hh
    linarith }

end FairDice
