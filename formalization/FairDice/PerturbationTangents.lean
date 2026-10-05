import FairDice.MomentPerturbation

namespace FairDice

@[simp] theorem pivotLift_pivot {m K : ℕ} (e : Fin m ↪ Fin K) (v : Fin m → ℝ) (j : Fin m) :
    pivotLift e v (e j) = v j := by
  rw [pivotLift_apply]
  simp [e.injective.eq_iff]

theorem pivotLift_free {m K : ℕ} (e : Fin m ↪ Fin K) (v : Fin m → ℝ)
    (q : Fin K) (hq : q ∉ Set.range e) : pivotLift e v q = 0 := by
  rw [pivotLift_apply]
  have he (j : Fin m) : e j ≠ q := fun h => hq ⟨j,h⟩
  simp [he]

noncomputable def correctionTangent {m K : ℕ} (e : Fin m ↪ Fin K) (u : Fin K → ℝ) :
    (Fin K → ℝ) →L[ℝ] (Fin m → ℝ) :=
  -((rawMomentDifferential (m := m) u).comp (pivotLift e)).inverse |>.comp (rawMomentDifferential u)

noncomputable def nodeTangent {m K : ℕ} (e : Fin m ↪ Fin K) (u : Fin K → ℝ) :
    (Fin K → ℝ) →L[ℝ] (Fin K → ℝ) :=
  ContinuousLinearMap.id ℝ _ + (pivotLift e).comp (correctionTangent e u)

noncomputable def MomentPerturbation.nodes {m K : ℕ} {e : Fin m ↪ Fin K} {u : Fin K → ℝ}
    (P : MomentPerturbation e u) (t : Fin K → ℝ) : Fin K → ℝ :=
  u+t+pivotLift e (P.response t)

@[simp] theorem MomentPerturbation.nodes_zero {m K : ℕ} {e : Fin m ↪ Fin K} {u : Fin K → ℝ}
    (P : MomentPerturbation e u) : P.nodes 0 = u := by simp [nodes,P.base]

theorem MomentPerturbation.nodes_hasFDerivAt {m K : ℕ} {e : Fin m ↪ Fin K} {u : Fin K → ℝ}
    (P : MomentPerturbation e u) : HasFDerivAt P.nodes (nodeTangent e u) 0 := by
  have hh := ((hasFDerivAt_const u (0 : Fin K → ℝ)).add (hasFDerivAt_id (0 : Fin K → ℝ))).add
    ((pivotLift e).hasFDerivAt.comp (0 : Fin K → ℝ) P.derivative)
  convert hh using 1 <;> first | rfl | simp [nodeTangent,correctionTangent]

@[simp] theorem rawMomentDifferential_single {m K : ℕ} (u : Fin K → ℝ) (q : Fin K) (r : Fin m) :
    rawMomentDifferential (m := m) u (Pi.single q 1) r = ((r.val+1 : ℝ)/K)*u q^r.val := by
  simp [rawMomentDifferential, Pi.single_apply, eq_comm, div_eq_mul_inv]
  ring

/-- The inverse derivative sends a free direction at a repeated pivot
value to minus the corresponding unit vector, exactly as the informal proof. -/
theorem correctionTangent_matching {m K : ℕ} (hK : 0 < K) (e : Fin m ↪ Fin K)
    (u : Fin K → ℝ) (hu : Function.Injective (fun j => u (e j)))
    (q : Fin K) (j : Fin m) (hq : u q = u (e j)) :
    correctionTangent e u (Pi.single q 1) = -Pi.single j 1 := by
  apply matching_pivot_response hK (fun j => u (e j)) hu j
  rw [← pivot_differential_eq e u]
  have hi := pivot_differential_isInvertible hK e u hu
  change ((rawMomentDifferential u).comp (pivotLift e))
    (-((rawMomentDifferential u).comp (pivotLift e)).inverse (rawMomentDifferential u (Pi.single q 1))) = _
  rw [map_neg, hi.self_apply_inverse]
  funext r
  simp [rawMomentDifferential_single,hq]

@[simp] theorem nodeTangent_free {m K : ℕ} (e : Fin m ↪ Fin K) (u v : Fin K → ℝ)
    (q : Fin K) (hq : q ∉ Set.range e) : nodeTangent e u v q = v q := by
  simp [nodeTangent,pivotLift_free e _ q hq]

/-- Every collision between initially coincident distinct coordinates has
a nonzero tangent. Both-pivot coincidences are excluded by distinct pivots. -/
theorem coinciding_nodes_tangent_nonzero {m K : ℕ} (hK : 0 < K) (e : Fin m ↪ Fin K)
    (u : Fin K → ℝ) (hu : Function.Injective (fun j => u (e j)))
    (q r : Fin K) (hqr : q ≠ r) (hval : u q = u r) :
    ∃ v : Fin K → ℝ, nodeTangent e u v q - nodeTangent e u v r ≠ 0 := by
  classical
  have hfree (q r : Fin K) (hq : q ∉ Set.range e) (hqr : q ≠ r) (hval : u q = u r) :
      nodeTangent e u (Pi.single q 1) q - nodeTangent e u (Pi.single q 1) r ≠ 0 := by
    rw [nodeTangent_free e u _ q hq]
    by_cases hr : r ∈ Set.range e
    · obtain ⟨j,rfl⟩ := hr
      have hh := correctionTangent_matching hK e u hu q j hval
      simp [nodeTangent,hh,hqr]
    · rw [nodeTangent_free e u _ r hr]
      simp [Ne.symm hqr]
  by_cases hq : q ∈ Set.range e
  · obtain ⟨j,hj⟩ := hq
    have hr : r ∉ Set.range e := by
      rintro ⟨i,hi⟩
      have hji : j=i := hu (by simpa [hj,hi] using hval)
      exact hqr (hj.symm.trans (hji ▸ hi))
    refine ⟨Pi.single r 1, ?_⟩
    have hh := hfree r q hr (Ne.symm hqr) hval.symm
    exact fun h => hh (by linarith)
  · exact ⟨Pi.single q 1,hfree q r hq hqr hval⟩

end FairDice
