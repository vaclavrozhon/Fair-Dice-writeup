import FairDice.CutSegments

namespace FairDice

abbrev CutIndex {n : ℕ} (σ : Equiv.Perm (Fin n)) (m : ℕ) :=
  Fin (patternCuts ((List.finRange n).map σ) m).length

def cutAt {n m : ℕ} (σ : Equiv.Perm (Fin n)) (j : CutIndex σ m) : List (List (Fin n)) :=
  (patternCuts ((List.finRange n).map σ) m).get j

theorem cutAt_mem {n m : ℕ} (σ : Equiv.Perm (Fin n)) (j : CutIndex σ m) :
    cutAt σ j ∈ patternCuts ((List.finRange n).map σ) m := List.get_mem _ j

theorem cutAt_length {n m : ℕ} (σ : Equiv.Perm (Fin n)) (j : CutIndex σ m) :
    (cutAt σ j).length=m := (patternCuts_length_flatten _ _ _ (cutAt_mem σ j)).1

theorem cutAt_flatten {n m : ℕ} (σ : Equiv.Perm (Fin n)) (j : CutIndex σ m) :
    (cutAt σ j).flatten=(List.finRange n).map σ :=
  (patternCuts_length_flatten _ _ _ (cutAt_mem σ j)).2

noncomputable def cutGraphAt {n m : ℕ} (σ : Equiv.Perm (Fin n))
    (I : Finset (Fin m)) (j : CutIndex σ m)
    (h : ∀ i ∈ I, 3 ≤ ((cutAt σ j)[i.val]?.getD []).length) :
    Finset (BlockSegment (Fin m) n) :=
  cutGraph (cutAt σ j) (cutAt_length σ j) (by rw [cutAt_flatten]; simp) I h

@[simp] theorem cutGraphAt_card {n m : ℕ} (σ : Equiv.Perm (Fin n))
    (I : Finset (Fin m)) (j : CutIndex σ m)
    (h : ∀ i ∈ I, 3 ≤ ((cutAt σ j)[i.val]?.getD []).length) :
    (cutGraphAt σ I j h).card=I.card := cutGraph_card _ _ _ _ _

/-- Contribution of one literal cut to the coefficient of a segment monomial.
Indexing cuts by their positions preserves all multiplicities. -/
noncomputable def palindromeCutCoefficient {n m : ℕ} (σ : Equiv.Perm (Fin n))
    (I : Finset (Fin m)) (j : CutIndex σ m) (K : Finset (BlockSegment (Fin m) n)) : ℝ := by
  classical
  exact if h : ∀ i ∈ I, 3 ≤ ((cutAt σ j)[i.val]?.getD []).length then
    if cutGraphAt σ I j h=K then palindromeCutWeight n m (cutAt σ j) else 0
  else 0

theorem palindromeCutCoefficient_card {n m : ℕ} (σ : Equiv.Perm (Fin n))
    (I : Finset (Fin m)) (j : CutIndex σ m) (K : Finset (BlockSegment (Fin m) n))
    (hcard : K.card≠I.card) : palindromeCutCoefficient σ I j K=0 := by
  classical
  unfold palindromeCutCoefficient
  split_ifs with h he
  · exact False.elim (hcard (he ▸ cutGraphAt_card σ I j h))
  all_goals rfl

theorem palindromeCutCoefficient_blocks {n m : ℕ} (σ : Equiv.Perm (Fin n))
    (I : Finset (Fin m)) (j : CutIndex σ m) (K : Finset (BlockSegment (Fin m) n))
    (hK : palindromeCutCoefficient σ I j K≠0) :
    Set.InjOn (fun v : BlockSegment (Fin m) n => v.1) K := by
  classical
  unfold palindromeCutCoefficient at hK
  split_ifs at hK with h he
  · subst K
    exact cutGraph_blocks _ _ _ _ _
  all_goals exact False.elim (hK rfl)

theorem palindromeCutCoefficient_sum {n m : ℕ} (σ : Equiv.Perm (Fin n))
    (I : Finset (Fin m)) (j : CutIndex σ m) (ρ : Fin m → Equiv.Perm (Fin n)) :
    (∑ K : Finset (BlockSegment (Fin m) n), palindromeCutCoefficient σ I j K *
      ∏ v ∈ K, segmentError σ v ρ) =
        palindromeCutWeight n m (cutAt σ j) * ∏ i ∈ I, palindromeCutDelta ρ (cutAt σ j) i := by
  classical
  by_cases h : ∀ i ∈ I, 3 ≤ ((cutAt σ j)[i.val]?.getD []).length
  · simp only [palindromeCutCoefficient, dif_pos h, ite_mul, zero_mul]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ, ite_true]
    congr 1
    exact cutGraph_error_product σ _ (cutAt_length σ j) (cutAt_flatten σ j) I h ρ
  · rw [cut_product_eq_zero_of_short σ _ (cutAt_mem σ j) I h ρ]
    simp [palindromeCutCoefficient,h]

/-- The actual nonnegative coefficient of each degree-`ell` monomial,
obtained by grouping the finite cut expansion by its selected segments. -/
noncomputable def palindromeSegmentCoefficient {n m : ℕ} (σ : Equiv.Perm (Fin n))
    (ell : ℕ) (K : Finset (BlockSegment (Fin m) n)) : ℝ :=
  ∑ I ∈ (Finset.univ : Finset (Finset (Fin m))).filter (fun I => I.card=ell),
    ∑ j : CutIndex σ m, palindromeCutCoefficient σ I j K

theorem palindromeSegmentCoefficient_card {n m : ℕ} (σ : Equiv.Perm (Fin n))
    (ell : ℕ) (K : Finset (BlockSegment (Fin m) n)) (hK : K.card≠ell) :
    palindromeSegmentCoefficient σ ell K=0 := by
  apply Finset.sum_eq_zero
  intro I hI
  apply Finset.sum_eq_zero
  intro j _
  apply palindromeCutCoefficient_card
  rwa [(Finset.mem_filter.mp hI).2]

theorem palindromeSegmentCoefficient_blocks {n m : ℕ} (σ : Equiv.Perm (Fin n))
    (ell : ℕ) (K : Finset (BlockSegment (Fin m) n))
    (hK : palindromeSegmentCoefficient σ ell K≠0) :
    Set.InjOn (fun v : BlockSegment (Fin m) n => v.1) K := by
  classical
  by_contra h
  apply hK
  apply Finset.sum_eq_zero
  intro I _
  apply Finset.sum_eq_zero
  intro j _
  by_contra hc
  exact h (palindromeCutCoefficient_blocks σ I j K hc)

theorem palindromeCutWeight_nonneg (n m : ℕ) (ps : List (List (Fin n))) :
    0 ≤ palindromeCutWeight n m ps := by
  apply div_nonneg (Nat.cast_nonneg _)
  apply mul_nonneg (pow_nonneg (Nat.cast_nonneg _) _)
  apply List.prod_nonneg
  intro x hx
  obtain ⟨q,_,rfl⟩ := List.mem_map.mp hx
  exact Nat.cast_nonneg _

theorem palindromeSegmentCoefficient_nonneg {n m : ℕ} (σ : Equiv.Perm (Fin n))
    (ell : ℕ) (K : Finset (BlockSegment (Fin m) n)) :
    0 ≤ palindromeSegmentCoefficient σ ell K := by
  apply Finset.sum_nonneg
  intro I _
  apply Finset.sum_nonneg
  intro j _
  unfold palindromeCutCoefficient
  split_ifs
  · exact palindromeCutWeight_nonneg _ _ _
  all_goals exact le_rfl

/-- Exact identification of the homogeneous part of the actual word with
the polynomial to which the coloring theorem applies. -/
theorem palindrome_segment_part_expansion {n m : ℕ} (σ : Equiv.Perm (Fin n))
    (ell : ℕ) (ρ : Fin m → Equiv.Perm (Fin n)) :
    (∑ K : Finset (BlockSegment (Fin m) n), palindromeSegmentCoefficient σ ell K *
      ∏ v ∈ K, segmentError σ v ρ) =
        ∑ I ∈ (Finset.univ : Finset (Finset (Fin m))).filter (fun I => I.card=ell),
          palindromeBlockPart σ I ρ := by
  classical
  unfold palindromeSegmentCoefficient
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro I _
  rw [Finset.sum_comm]
  simp_rw [palindromeCutCoefficient_sum]
  unfold palindromeBlockPart
  let cuts := patternCuts ((List.finRange n).map σ) m
  have he := congrArg (fun xs : List (List (List (Fin n))) =>
    (xs.map (fun ps => palindromeCutWeight n m ps * ∏ i ∈ I, palindromeCutDelta ρ ps i)).sum)
      (List.ofFn_get cuts)
  simpa only [List.map_ofFn,List.sum_ofFn,cutAt,cuts,Function.comp_apply] using he

/-- The coloring estimate now applies directly to a homogeneous part of
the concrete random palindrome word, with its actual cut coefficients. -/
theorem palindrome_homogeneous_colored {n m : ℕ} (H : BonamiExternal)
    (σ : Equiv.Perm (Fin n)) (p : ℝ) (hp : 2 ≤ p) (ell : ℕ) :
    finiteLp p (fun ρ : Fin m → Equiv.Perm (Fin n) =>
      ∑ I ∈ (Finset.univ : Finset (Finset (Fin m))).filter (fun I => I.card=ell),
        palindromeBlockPart σ I ρ) ≤
      (2*Real.sqrt (p-1))^ell * Real.sqrt
        (∑ K : Finset (BlockSegment (Fin m) n), (palindromeSegmentCoefficient σ ell K)^2 *
          ∏ v ∈ K, (segmentErrorBound v)^2/segmentRetentionWeight v.2) := by
  have h := palindrome_colored (B := Fin m) H σ p hp ell (palindromeSegmentCoefficient σ ell)
    (palindromeSegmentCoefficient_card σ ell) (palindromeSegmentCoefficient_blocks σ ell)
  have he := funext (palindrome_segment_part_expansion (m := m) σ ell)
  rw [he] at h
  exact h

/-- Group the actual error by its nonzero homogeneous degrees. -/
theorem palindrome_error_by_degree {n m : ℕ} (hm : 0 < m)
    (σ : Equiv.Perm (Fin n)) (ρ : Fin m → Equiv.Perm (Fin n)) :
    palindromeRelativeError ρ σ =
      ∑ ell ∈ Finset.Icc 1 m,
        ∑ I ∈ (Finset.univ : Finset (Finset (Fin m))).filter (fun I => I.card=ell),
          palindromeBlockPart σ I ρ := by
  classical
  rw [palindrome_error_nonempty_parts hm]
  have hmaps (I : Finset (Fin m))
      (hI : I ∈ (Finset.univ : Finset (Finset (Fin m))).erase ∅) :
      I.card ∈ Finset.Icc 1 m := by
    apply Finset.mem_Icc.mpr
    constructor
    · have hn := Finset.mem_erase.mp hI
      have hpos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hn.1)
      omega
    · simpa using Finset.card_le_univ I
  rw [← Finset.sum_fiberwise_of_maps_to hmaps (fun I => palindromeBlockPart σ I ρ)]
  apply Finset.sum_congr rfl
  intro ell hell
  congr 1
  ext I
  simp only [Finset.mem_filter,Finset.mem_erase,Finset.mem_univ,and_true,true_and]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_,h⟩
    intro he
    subst I
    simp only [Finset.card_empty] at h
    have := (Finset.mem_Icc.mp hell).1
    omega

/-- A bound for the norm of the whole concrete word error in terms of the
computed segment coefficients; every probabilistic reduction is now proved.
The remaining task for the moment theorem is bounding this finite energy. -/
theorem palindrome_error_colored_bound {n m : ℕ} (H : BonamiExternal) (hm : 0 < m)
    (σ : Equiv.Perm (Fin n)) (p : ℝ) (hp : 2 ≤ p) :
    finiteLp p (fun ρ : Fin m → Equiv.Perm (Fin n) => palindromeRelativeError ρ σ) ≤
      ∑ ell ∈ Finset.Icc 1 m, (2*Real.sqrt (p-1))^ell * Real.sqrt
        (∑ K : Finset (BlockSegment (Fin m) n), (palindromeSegmentCoefficient σ ell K)^2 *
          ∏ v ∈ K, (segmentErrorBound v)^2/segmentRetentionWeight v.2) := by
  simp_rw [palindrome_error_by_degree hm σ]
  exact (finiteLp_sum (by linarith : 1 ≤ p) _ _).trans
    (Finset.sum_le_sum (fun ell _ => palindrome_homogeneous_colored H σ p hp ell))

end FairDice
