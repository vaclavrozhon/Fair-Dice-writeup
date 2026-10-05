import FairDice.DensityCorrection

namespace FairDice

open Set MeasureTheory Polynomial

private theorem finite_positive_radius {ι : Type*} [Fintype ι] (a : ι → ℝ)
    (ha : ∀ i, 0 < a i) : ∃ ε : ℝ, 0 < ε ∧ ∀ i, ε < a i := by
  classical
  have hh (S : Finset ι) : ∃ ε : ℝ, 0 < ε ∧ ∀ i ∈ S, ε < a i := by
    induction S using Finset.induction_on with
    | empty => exact ⟨1, by norm_num, by simp⟩
    | @insert i S hi ih =>
      obtain ⟨ε,hε,hεa⟩ := ih
      refine ⟨min ε (a i)/2, div_pos (lt_min hε (ha i)) (by norm_num), ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with hji | hj
      · subst j
        have := min_le_right ε (a i); linarith [lt_min hε (ha i)]
      · have := min_le_left ε (a i); linarith [hεa j hj, lt_min hε (ha i)]
  obtain ⟨ε,hε,he⟩ := hh Finset.univ
  exact ⟨ε,hε,fun i => he i (Finset.mem_univ i)⟩

/-- Finitely many distinct interior nodes admit disjoint open intervals
whose closures remain inside the unit interval. -/
theorem disjoint_node_intervals {K : ℕ} (u : Fin K → ℝ) (hu : Function.Injective u)
    (hunit : ∀ q, 0 < u q ∧ u q < 1) :
    ∃ L R : Fin K → ℝ,
      (∀ q, 0 ≤ L q ∧ L q < u q ∧ u q < R q ∧ R q ≤ 1) ∧
      ∀ q r, q ≠ r → Disjoint (Ioo (L q) (R q)) (Ioo (L r) (R r)) := by
  classical
  let a : (Fin K ⊕ Fin K) ⊕ (Fin K × Fin K) → ℝ := fun v => match v with
    | .inl (.inl q) => u q
    | .inl (.inr q) => 1-u q
    | .inr (q,r) => if q=r then 1 else |u q-u r|/2
  have ha (v) : 0 < a v := by
    rcases v with (q | q) | ⟨q,r⟩
    · exact (hunit q).1
    · exact sub_pos.mpr (hunit q).2
    · dsimp [a]
      split_ifs with hqr
      · norm_num
      · exact div_pos (abs_pos.mpr (sub_ne_zero.mpr (hu.ne hqr))) (by norm_num)
  obtain ⟨ε,hε,he⟩ := finite_positive_radius a ha
  have hq (q : Fin K) : ε < u q ∧ ε < 1-u q := ⟨he (.inl (.inl q)),he (.inl (.inr q))⟩
  refine ⟨fun q => u q-ε,fun q => u q+ε,fun q => ?_,fun q r hqr => ?_⟩
  · have hh := hq q
    exact ⟨by linarith,by linarith,by linarith,by linarith⟩
  · apply Set.disjoint_left.mpr
    intro x hxq hxr
    have hh := he (.inr (q,r))
    simp only [a,if_neg hqr] at hh
    have h2 : |u q-u r| < 2*ε := by
      rw [abs_lt]
      constructor <;> linarith [hxq.1,hxq.2,hxr.1,hxr.2]
    linarith

/-- The `m^2` size condition supplies disjoint selections of `m` node
indices for each of the `m` ordinary dice. -/
theorem disjoint_node_selections {m K : ℕ} (hsize : m^2 ≤ K) :
    ∃ e : Fin m → (Fin m ↪ Fin K), ∀ i j, i ≠ j → ∀ q r, e i q ≠ e j r := by
  obtain ⟨E⟩ := Function.Embedding.nonempty_of_card_le (α := Fin m × Fin m) (β := Fin K)
    (by simpa [pow_two] using hsize)
  let e := fun i : Fin m => (⟨fun j => E (i,j), fun q r h =>
    congrArg Prod.snd (E.injective h)⟩ : Fin m ↪ Fin K)
  exact ⟨e,fun i j hij q r h => hij (congrArg Prod.fst (E.injective h))⟩

/-- All data actually constructed before the order-response argument:
rational nodes, disjoint correction sets and supports, positive normalized
rational-valued densities, and their common repaired moment functional. -/
structure CorrectedFamily (m K : ℕ) where
  node : Fin K → ℚ
  node_injective : Function.Injective node
  node_interior : ∀ q, 0 < node q ∧ node q < 1
  selection : Fin m → (Fin m ↪ Fin K)
  selection_disjoint : ∀ i j, i ≠ j → ∀ q r, selection i q ≠ selection j r
  intervals : Fin K → CorrectionIntervals m
  admissible : ∀ q, (intervals q).admissible (node q)
  containerLeft : Fin K → ℝ
  containerRight : Fin K → ℝ
  container_bounds : ∀ q, 0 ≤ containerLeft q ∧ containerLeft q < node q ∧
    (node q : ℝ) < containerRight q ∧ containerRight q ≤ 1
  container_disjoint : ∀ q r, q≠r →
    Disjoint (Ioo (containerLeft q) (containerRight q))
      (Ioo (containerLeft r) (containerRight r))
  bump_support : ∀ q, Function.support ((intervals q).bump (node q)) ⊆
    Ioo (containerLeft q) (containerRight q)
  supports_disjoint : ∀ q r, q ≠ r →
    Disjoint (Function.support ((intervals q).bump (node q)))
      (Function.support ((intervals r).bump (node r)))
  positive : ∀ j x, (1/2 : ℝ) ≤ correctedDensity (selection j) intervals (fun q => (node q : ℝ)) x
  normalized : ∀ j, (∫ x in (0 : ℝ)..1,
    correctedDensity (selection j) intervals (fun q => (node q : ℝ)) x) = 1
  rational : ∀ j x, ∃ c : ℚ,
    correctedDensity (selection j) intervals (fun q => (node q : ℝ)) x = c
  common_functional : ∀ i j p, p.natDegree < m →
    densityMomentFunctional (selection i) (fun q => (node q : ℝ)) p =
      densityMomentFunctional (selection j) (fun q => (node q : ℝ)) p
  repaired_moments : ∀ j p, p.natDegree ≤ m →
    densityMomentFunctional (selection j) (fun q => (node q : ℝ)) p.derivative =
      realPolynomialIntegral p - (∑ q, p.eval (node q : ℝ))/K

/-- The article's positive rational continuous-family construction, starting
from a regular exact quadrature. The regular rule itself and the full-order
response are not assumed as conclusions of this theorem. -/
theorem corrected_family_exists {m K : ℕ} (hm : 0 < m) (hK : 0 < K) (hsize : m^2 ≤ K)
    (Q : EqualWeightRealRule K m) (hu : Function.Injective Q.node)
    (hunit : ∀ q, 0 < Q.node q ∧ Q.node q < 1) : Nonempty (CorrectedFamily m K) := by
  classical
  obtain ⟨L,R,hLR,hdis⟩ := disjoint_node_intervals Q.node hu hunit
  have hex (q : Fin K) := centered_bump_exists m (L q) (Q.node q) (R q)
    (hLR q).1 (hLR q).2.1 (hLR q).2.2.1 (hLR q).2.2.2
  choose I V hVo huV hVa hVs C hC hCb using hex
  obtain ⟨e,he⟩ := disjoint_node_selections hsize
  let U : Set (Fin K → ℝ) := {t | ∀ q, t q ∈ V q ∩ Ioo (L q) (R q)}
  have hUo : IsOpen U := by
    have hh := isOpen_iInter_of_finite (fun q : Fin K =>
      ((hVo q).inter (isOpen_Ioo (a := L q) (b := R q))).preimage (continuous_apply q))
    have heq : U = ⋂ q : Fin K, (fun t : Fin K → ℝ => t q) ⁻¹' (V q ∩ Ioo (L q) (R q)) := by
      ext t
      simp only [U, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
    rw [heq]
    exact hh
  have huU : Q.node ∈ U := fun q => ⟨huV q,(hLR q).2.1,(hLR q).2.2.1⟩
  obtain ⟨t,ht,hpos⟩ := positive_rational_density_approximation hK Q hu e I U hUo huU
  have hT : ∀ q, (t q : ℝ) ∈ V q := fun q => (ht q).1
  have htI (q : Fin K) : L q < (t q : ℝ) ∧ (t q : ℝ) < R q := (ht q).2
  have htR : Function.Injective (fun q => (t q : ℝ)) := by
    intro q r h
    by_contra hqr
    change (t q : ℝ) = (t r : ℝ) at h
    exact Set.disjoint_left.mp (hdis q r hqr) (htI q) (h.symm ▸ htI r)
  have htQ : Function.Injective t := fun q r h => htR (congrArg (fun a : ℚ => (a : ℝ)) h)
  refine ⟨{ node := t
            node_injective := htQ
            node_interior := ?_
            selection := e
            selection_disjoint := he
            intervals := I
            admissible := fun q => hVa q _ (hT q)
            containerLeft := L
            containerRight := R
            container_bounds := fun q =>
              ⟨(hLR q).1,(htI q).1,(htI q).2,(hLR q).2.2.2⟩
            container_disjoint := hdis
            bump_support := fun q => hVs q _ (hT q)
            supports_disjoint := ?_
            positive := hpos
            normalized := ?_
            rational := ?_
            common_functional := ?_
            repaired_moments := ?_ }⟩
  · intro q
    have hh := htI q
    have hreal : (0 : ℝ) < t q ∧ (t q : ℝ) < 1 :=
      ⟨(hLR q).1.trans_lt hh.1,hh.2.trans_le (hLR q).2.2.2⟩
    exact_mod_cast hreal
  · intro q r hqr
    exact (hdis q r hqr).mono (hVs q _ (hT q)) (hVs r _ (hT r))
  · intro j
    exact correctedDensity_integral hm (e j) I _ (fun q => hVa q _ (hT q))
  · intro j x
    exact correctedDensity_rational hK (e j) I t htQ x
  · intro i j p hp
    exact densityMomentFunctional_eq hK (e i) (e j) _ htR p hp
  · intro j p hp
    exact densityMomentFunctional_derivative hK (e j) _ htR p hp

end FairDice
