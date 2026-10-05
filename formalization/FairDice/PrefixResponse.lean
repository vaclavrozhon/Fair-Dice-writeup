import FairDice.PrefixOrder

open scoped Classical

namespace FairDice

open MeasureTheory

variable {ι : Type*} {m K : ℕ}

theorem LocalBumpSystem.response_any_node (S : LocalBumpSystem m K)
    (q r : Fin K) (a b : ℕ) (hdeg : a+b < m) :
    S.response q a b (S.node r)=
      if q=r ∧ b=0 then S.sign*(S.node r)^a/(a.factorial : ℝ) else 0 := by
  by_cases hqr : q=r
  · subst q
    rw [S.response_at_node r a b hdeg]
    simp
  · rw [S.response_other_node q r hqr a b hdeg]
    simp [hqr]

theorem shiftedResponseSum_at_node_zero (S : LocalBumpSystem m K) (e : ι → Fin m ↪ Fin K)
    (δ : ι → Fin m → ℝ) (js : List ι) (h : ℕ) (hh : 0 < h)
    (hlen : js.length+h ≤ m) (q : Fin K) :
    shiftedResponseSum S e δ js h (S.node q)=0 := by
  unfold shiftedResponseSum
  apply List.sum_eq_zero
  intro z hz
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hz
  have hd := (responseTerms_data js v hv).2
  apply Finset.sum_eq_zero
  intro r _
  rw [S.response_any_node (e v.1 r) q v.2.1 (v.2.2+h) (by omega),if_neg (by omega),mul_zero]

noncomputable def nodalDensityCoefficient (e : ι → Fin m ↪ Fin K) (δ : ι → Fin m → ℝ)
    (i : ι) (q : Fin K) : ℝ := ∑ r, if e i r=q then δ i r else 0

/-- Conditional ordered-prefix probability at a distinguished node.
The only correction is from the immediate predecessor in the ordering. -/
theorem densityPrefix_at_node [DecidableEq ι]
    (S : LocalBumpSystem m K) (e : ι → Fin m ↪ Fin K) (δ : ι → Fin m → ℝ)
    (he : ∀ i j, i≠j → ∀ r s, e i r≠e j s)
    (i : ι) (js : List ι) (hjs : (i::js).Nodup) (hlen : js.length+1 ≤ m) (q : Fin K) :
    densityPrefix (profileDensity S e δ) (i::js) (S.node q)=
      uniformPrefix (js.length+1) (S.node q)+
        nodalDensityCoefficient e δ i q*(S.sign*uniformPrefix js.length (S.node q)) := by
  rw [densityPrefix_expansion S e δ he _ hjs (by simpa using hlen),shiftedResponseSum_cons]
  rw [shiftedResponseSum_at_node_zero S e δ js 1 (by norm_num) hlen,add_zero]
  simp only [List.length_cons]
  congr 1
  unfold nodalDensityCoefficient uniformPrefix
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r _
  rw [S.response_any_node (e i r) q js.length 0 (by omega)]
  by_cases hr : e i r=q
  · simp [hr]; ring_nf; simp
  · simp [hr]

/-- The disjoint node selections also eliminate the possible product of
the predecessor and successor corrections at the same distinguished node. -/
theorem nodalDensityCoefficient_mul [DecidableEq ι]
    (e : ι → Fin m ↪ Fin K) (δ : ι → Fin m → ℝ)
    (he : ∀ i j, i≠j → ∀ r s, e i r≠e j s)
    (i j : ι) (hij : i≠j) (q : Fin K) :
    nodalDensityCoefficient e δ i q*nodalDensityCoefficient e δ j q=0 := by
  unfold nodalDensityCoefficient
  rw [Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro r _
  rw [Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro s _
  by_cases hr : e i r=q
  · have hs : e j s≠q := fun hs => he i j hij r s (hr.trans hs.symm)
    simp [hs]
  · simp [hr]

end FairDice
