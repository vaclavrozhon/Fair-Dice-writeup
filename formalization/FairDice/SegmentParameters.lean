import FairDice.ActualLattice

open scoped Classical

namespace FairDice

/-- Selected lengths, indexed by the same finite size choices as the colors. -/
abbrev AdmissibleLengths (ell n : ℕ) :=
  {k : Fin ell → Fin (n-2) // (∑ j, ((k j).val+3)) ≤ n}

noncomputable instance (ell n : ℕ) : Fintype (AdmissibleLengths ell n) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

def selectedLengths {ell n : ℕ} (k : AdmissibleLengths ell n) (j : Fin ell) : ℕ :=
  (k.val j).val+3

def selectedLengthSum {ell n : ℕ} (k : AdmissibleLengths ell n) : ℕ :=
  ∑ j, selectedLengths k j

abbrev SegmentParameters (ell m n : ℕ) :=
  Σ k : AdmissibleLengths ell n, BlockSelection ell m ×
    {a : Fin (ell+1) → ℕ // a ∈ Finset.piAntidiag Finset.univ (n-selectedLengthSum k)}

/-- The concrete monomial described by a block set, lengths and gap totals. -/
noncomputable def parameterSegments {ell m n : ℕ} (u : SegmentParameters ell m n) :
    Finset (BlockSegment (Fin m) n) := by
  let k := selectedLengths u.1
  let a := u.2.2.val
  let P := blockGapPartition (u.2.1.val.orderEmbOfFin u.2.1.property)
  have ha : ∑ r, a r=n-selectedLengthSum u.1 := (Finset.mem_piAntidiag.mp u.2.2.property).1
  have hn : (∑ j, k j)+(∑ r, a r)=n := by
    rw [ha]; exact Nat.add_sub_of_le u.1.property
  exact Finset.univ.image (fun j => (⟨P.selected j,
    segmentOfStart n (selectedGapStart k a j) (k j)
      (by rw [← hn]; exact selectedGapStart_fits k a j)
      (by dsimp [k,selectedLengths]; omega)⟩ : BlockSegment (Fin m) n))

/-- Every nonzero concrete coefficient has an admissible gap description.
The witness is extracted from an actual cut, so no extra support assumption
is imposed on the word expansion. -/
theorem palindrome_coefficient_parameter {n m ell : ℕ} (σ : Equiv.Perm (Fin n))
    (K : Finset (BlockSegment (Fin m) n))
    (hK : palindromeSegmentCoefficient σ ell K≠0) :
    ∃ u : SegmentParameters ell m n, parameterSegments u=K := by
  classical
  obtain ⟨I,hI,hc⟩ := Finset.exists_ne_zero_of_sum_ne_zero hK
  obtain ⟨j,_,hc⟩ := Finset.exists_ne_zero_of_sum_ne_zero hc
  have hell : I.card=ell := (Finset.mem_filter.mp hI).2
  unfold palindromeCutCoefficient at hc
  split_ifs at hc with hlong he
  · let P := blockGapPartition (I.orderEmbOfFin hell)
    let v := cutOccupancy σ j
    let a := fun r => ∑ i, v (P.labels.symm (.inr ⟨r,i⟩))
    have htotal : (∑ r, v (P.selected r))+∑ r, a r=n := by
      rw [← P.total_sum]; exact cutOccupancy_sum σ j
    have hk3 (r : Fin ell) : 3 ≤ v (P.selected r) :=
      hlong _ (I.orderEmbOfFin_mem hell r)
    have hkfit (r : Fin ell) : v (P.selected r) ≤ n := by
      have hh := Finset.single_le_sum (fun r _ => Nat.zero_le (v (P.selected r)))
        (Finset.mem_univ r)
      omega
    let k0 : Fin ell → Fin (n-2) := fun r => ⟨v (P.selected r)-3,by
      have := hk3 r; have := hkfit r; omega⟩
    have hk0 (r) : (k0 r).val+3=v (P.selected r) := by
      dsimp [k0]; have := hk3 r; omega
    have hks : (∑ r, ((k0 r).val+3)) ≤ n := by
      simp_rw [hk0]; omega
    let k : AdmissibleLengths ell n := ⟨k0,hks⟩
    have hk (r) : selectedLengths k r=v (P.selected r) := hk0 r
    have ha : ∑ r, a r=n-selectedLengthSum k := by
      change ∑ r, a r=n-∑ r, selectedLengths k r
      simp_rw [hk]; omega
    let u : SegmentParameters ell m n :=
      ⟨k,⟨⟨I,hell⟩,⟨a,Finset.mem_piAntidiag.mpr ⟨ha,by simp⟩⟩⟩⟩
    refine ⟨u,?_⟩
    rw [← he]
    ext w
    change w ∈ Finset.univ.image _ ↔ w ∈ cutGraphAt σ I j hlong
    rw [cutGraphAt,cutGraph_mem_iff]
    constructor
    · intro hw
      obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp hw
      refine ⟨I.orderEmbOfFin_mem hell r,?_,?_⟩
      · rw [segmentOfStart_start,cutStart_occupancy]
        exact (P.prefix_of_event (selectedLengths k) a v
          ⟨fun r => by rw [P.selected_label]; exact (hk r).symm,fun _ => rfl⟩ r).symm
      · rw [segmentOfStart_length]
        exact hk r
    · rintro ⟨hw,hs,hl⟩
      have hmemb : w.1 ∈ Finset.univ.image (I.orderEmbOfFin hell) := by
        rwa [Finset.image_orderEmbOfFin_univ]
      obtain ⟨r,_,hr⟩ := Finset.mem_image.mp hmemb
      apply Finset.mem_image.mpr
      refine ⟨r,Finset.mem_univ r,?_⟩
      apply Sigma.ext hr
      apply heq_of_eq
      apply segment_eq_of_start_length
      · rw [segmentOfStart_start,hs,← hr,cutStart_occupancy]
        exact (P.prefix_of_event (selectedLengths k) a v
          ⟨fun r => by rw [P.selected_label]; exact (hk r).symm,fun _ => rfl⟩ r).symm
      · rw [segmentOfStart_length,hl,← hr]
        exact hk r
  all_goals exact False.elim (hc rfl)

/-- A nonnegative sum is bounded by any finite parametrization covering
its nonzero support; repeated parametrizations only increase the bound. -/
theorem finite_sum_le_of_support_covered {U V : Type*} [Fintype U] [Fintype V]
    (f : U → V) (g : V → ℝ) (hg : ∀ v, 0 ≤ g v)
    (h : ∀ v, g v≠0 → ∃ u, f u=v) :
    (∑ v, g v) ≤ ∑ u, g (f u) := by
  classical
  let S := {v : V // g v≠0}
  letI : Fintype S := Fintype.ofFinite S
  let e : S ↪ U := {
    toFun := fun v => (h v.val v.property).choose
    inj' := by
      intro v w he
      apply Subtype.ext
      exact (h v.val v.property).choose_spec.symm.trans
        ((congrArg f he).trans (h w.val w.property).choose_spec) }
  have he := finite_sum_embedding_le e (fun u => g (f u)) (fun u => hg (f u))
  have hleft : (∑ v : S, g (f (e v)))=∑ v : S, g v.val := by
    apply Finset.sum_congr rfl
    intro v _
    change g (f (h v.val v.property).choose)=g v.val
    rw [(h v.val v.property).choose_spec]
  rw [hleft] at he
  have hs : (∑ v : S, g v.val)=∑ v, g v := by
    rw [← Finset.sum_subtype (F := inferInstance)
      (Finset.univ.filter (fun v => g v≠0)) (fun v => by simp) g,Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro v _
    by_cases hv : g v=0 <;> simp [hv]
  rwa [hs] at he

noncomputable def segmentCoefficientEnergy {n m : ℕ} (σ : Equiv.Perm (Fin n))
    (ell : ℕ) (K : Finset (BlockSegment (Fin m) n)) : ℝ :=
  (palindromeSegmentCoefficient σ ell K)^2 *
    ∏ v ∈ K, (segmentErrorBound v)^2/segmentRetentionWeight v.2

theorem segmentCoefficientEnergy_nonneg {n m : ℕ} (σ : Equiv.Perm (Fin n))
    (ell : ℕ) (K : Finset (BlockSegment (Fin m) n)) :
    0 ≤ segmentCoefficientEnergy σ ell K := by
  apply mul_nonneg (sq_nonneg _)
  exact Finset.prod_nonneg (fun v _ => div_nonneg (sq_nonneg _) (segmentRetentionWeight_pos v.2).le)

/-- The full energy is now bounded by a finite sum over admissible length
vectors, actual block selections and gap letter counts. -/
theorem palindrome_energy_parameter_bound {n m : ℕ} (σ : Equiv.Perm (Fin n))
    (ell : ℕ) :
    (∑ K : Finset (BlockSegment (Fin m) n), segmentCoefficientEnergy σ ell K) ≤
      ∑ u : SegmentParameters ell m n, segmentCoefficientEnergy σ ell (parameterSegments u) := by
  apply finite_sum_le_of_support_covered _ _ (segmentCoefficientEnergy_nonneg σ ell)
  intro K hK
  apply palindrome_coefficient_parameter σ K
  intro hc
  apply hK
  simp [segmentCoefficientEnergy,hc]

end FairDice
