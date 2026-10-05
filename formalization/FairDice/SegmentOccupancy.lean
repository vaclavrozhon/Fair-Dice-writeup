import FairDice.CoefficientOccupancy

namespace FairDice

/-- Start and length determine the actual finite segment. -/
theorem segment_eq_of_start_length {n : ℕ} {u v : ConsecutiveSegment n}
    (ha : segmentStart u=segmentStart v) (hk : segmentLength u=segmentLength v) : u=v := by
  apply segment_eq ha
  apply Fin.ext
  change u.val.2.val+3=v.val.2.val+3 at hk
  change u.val.2.val=v.val.2.val
  omega

/-- Membership in the graph of a concrete cut is exactly the specified
block, segment start and segment length. -/
theorem cutGraph_mem_iff {n m : ℕ} (ps : List (List (Fin n)))
    (hlen : ps.length=m) (hflat : ps.flatten.length=n)
    (I : Finset (Fin m)) (hI : ∀ i ∈ I, 3 ≤ (ps[i.val]?.getD []).length)
    (v : BlockSegment (Fin m) n) :
    v ∈ cutGraph ps hlen hflat I hI ↔
      v.1 ∈ I ∧ segmentStart v.2=cutStart ps v.1.val ∧
        segmentLength v.2=(ps[v.1.val]?.getD []).length := by
  classical
  unfold cutGraph
  constructor
  · intro hv
    obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hv
    refine ⟨i.property,rfl,?_⟩
    have hi : i.val.val<ps.length := by rw [hlen]; exact i.val.isLt
    have hk : 3 ≤ ps[i.val.val].length := by
      simpa [List.getElem?_eq_getElem hi] using hI i.val i.property
    change segmentLength (cutSegment ps i.val.val hi hflat hk)=
      (ps[i.val.val]?.getD []).length
    rw [cutSegment_length,List.getElem?_eq_getElem (show i.val.val<ps.length by rw [hlen]; exact i.val.isLt)]
    rfl
  · rintro ⟨hv,ha,hk⟩
    apply Finset.mem_map.mpr
    refine ⟨⟨v.1,hv⟩,Finset.mem_univ _,?_⟩
    cases v with
    | mk b t =>
      apply congrArg (fun u => (⟨b,u⟩ : BlockSegment (Fin m) n))
      apply segment_eq_of_start_length
      · exact ha.symm
      · rw [cutSegment_length]
        rw [List.getElem?_eq_getElem (show b.val<ps.length by rw [hlen]; exact b.isLt)] at hk
        exact hk.symm

/-- Prefixes of an occupancy vector use precisely the block positions
strictly before the given block. -/
theorem cutStart_occupancy {n m : ℕ} (σ : Equiv.Perm (Fin n))
    (j : CutIndex σ m) (b : Fin m) :
    cutStart (cutAt σ j) b.val =
      ∑ i ∈ (Finset.univ : Finset (Fin m)).filter (fun i => i<b), cutOccupancy σ j i := by
  classical
  rw [cutStart_range]
  apply Finset.sum_bij (fun i hi => (⟨i,by have := Finset.mem_range.mp hi; omega⟩ : Fin m))
  · intro i hi
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Fin.lt_def]
    exact Finset.mem_range.mp hi
  · intro i hi i' hi' he
    exact congrArg Fin.val he
  · intro i hi
    refine ⟨i.val,?_,Fin.ext rfl⟩
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Fin.lt_def] at hi
    exact Finset.mem_range.mpr hi
  · intro i hi
    rfl

end FairDice
