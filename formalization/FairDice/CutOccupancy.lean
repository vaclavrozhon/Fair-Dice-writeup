import FairDice.CutCoefficients
import FairDice.SelectedOccupancy

namespace FairDice

variable {α : Type*}

/-- Literal enumeration of ordered cuts contains no duplicate cut. -/
theorem patternCuts_nodup (p : List α) (m : ℕ) : (patternCuts p m).Nodup := by
  induction m generalizing p with
  | zero => by_cases h : p=[] <;> simp [patternCuts,h]
  | succ m ih =>
    apply List.nodup_flatMap.mpr
    refine ⟨fun k _ => (ih (p.drop k)).map (fun x y h => by injection h),?_⟩
    apply (List.nodup_range (n := p.length+1)).pairwise_of_forall_ne
    intro a ha b hb hab
    apply List.disjoint_left.mpr
    intro ps hpa hpb
    obtain ⟨xs,_,he⟩ := List.mem_map.mp hpa
    obtain ⟨ys,_,hf⟩ := List.mem_map.mp hpb
    have hp : p.take a=p.take b := (List.cons.inj (he.trans hf.symm)).1
    have hl := congrArg List.length hp
    have ha' : a≤p.length := by have := List.mem_range.mp ha; omega
    have hb' : b≤p.length := by have := List.mem_range.mp hb; omega
    simp only [List.length_take, Nat.min_eq_left ha', Nat.min_eq_left hb'] at hl
    exact hab hl

/-- A cut of a fixed word is uniquely determined by its occupancy lengths. -/
theorem cut_eq_of_lengths (ps qs : List (List α)) (hflat : ps.flatten=qs.flatten)
    (hlen : ps.map List.length=qs.map List.length) : ps=qs := by
  induction ps generalizing qs with
  | nil => cases qs <;> simp_all
  | cons p ps ih =>
    cases qs with
    | nil => simp at hlen
    | cons q qs =>
      have hhead : p.length=q.length := (List.cons.inj hlen).1
      have hp : p=q := by
        have h := congrArg (List.take p.length) hflat
        simpa [List.flatten_cons,hhead] using h
      subst q
      have hrest : ps.flatten=qs.flatten := by
        simpa [List.flatten_cons] using hflat
      rw [ih qs hrest (List.cons.inj hlen).2]

/-- The actual occupancy vector of an enumerated cut. -/
def cutOccupancy {n m : ℕ} (σ : Equiv.Perm (Fin n)) (j : CutIndex σ m) : Fin m → ℕ :=
  fun i => ((cutAt σ j)[i.val]?.getD []).length

theorem cutAt_ofFn {n m : ℕ} (σ : Equiv.Perm (Fin n)) (j : CutIndex σ m) :
    cutAt σ j=List.ofFn (fun i : Fin m => (cutAt σ j)[i.val]?.getD []) := by
  let f := fun i : Fin m => (cutAt σ j).get (Fin.cast (cutAt_length σ j).symm i)
  have hh : cutAt σ j=List.ofFn f := by
    rw [← List.ofFn_get (cutAt σ j)]
    exact List.ofFn_congr (cutAt_length σ j) _
  rw [hh]
  apply congrArg List.ofFn
  funext i
  simp [f]

theorem cutOccupancy_sum {n m : ℕ} (σ : Equiv.Perm (Fin n)) (j : CutIndex σ m) :
    ∑ i, cutOccupancy σ j i=n := by
  have he := congrArg List.length (cutAt_flatten σ j)
  rw [List.length_flatten] at he
  have hm : ((cutAt σ j).map List.length).sum=∑ i, cutOccupancy σ j i := by
    conv_lhs => rw [cutAt_ofFn σ j]
    simp [List.map_ofFn,List.sum_ofFn,cutOccupancy,Function.comp_def]
  rw [hm] at he
  simpa using he

theorem cutOccupancy_injective {n m : ℕ} (σ : Equiv.Perm (Fin n)) :
    Function.Injective (cutOccupancy (m := m) σ) := by
  intro i j h
  have hlen : (cutAt σ i).map List.length=(cutAt σ j).map List.length := by
    rw [cutAt_ofFn σ i,cutAt_ofFn σ j,List.map_ofFn,List.map_ofFn]
    exact congrArg List.ofFn h
  have hc := cut_eq_of_lengths _ _ ((cutAt_flatten σ i).trans (cutAt_flatten σ j).symm) hlen
  exact (patternCuts_nodup _ m).injective_get hc

/-- Every occupancy vector summing to the word length describes one cut. -/
theorem patternCuts_of_occupancy (p : List α) (m : ℕ) (k : Fin m → ℕ)
    (hs : ∑ i, k i=p.length) :
    ∃ ps ∈ patternCuts p m, ∀ i : Fin m, (ps[i.val]?.getD []).length=k i := by
  induction m generalizing p with
  | zero =>
    have hp : p=[] := List.length_eq_zero_iff.mp (by simpa using hs.symm)
    subst p
    exact ⟨[],by simp [patternCuts],fun i => Fin.elim0 i⟩
  | succ m ih =>
    have hsum : k 0+∑ i : Fin m, k i.succ=p.length := by rwa [Fin.sum_univ_succ] at hs
    have hk0 : k 0≤p.length := by omega
    have htail : (∑ i : Fin m, k i.succ)=(p.drop (k 0)).length := by
      simp only [List.length_drop]
      omega
    obtain ⟨qs,hqs,hk⟩ := ih (p.drop (k 0)) (fun i => k i.succ) htail
    refine ⟨p.take (k 0)::qs,?_,?_⟩
    · apply List.mem_flatMap.mpr
      exact ⟨k 0,List.mem_range.mpr (by omega),List.mem_map.mpr ⟨qs,hqs,rfl⟩⟩
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [List.length_take, Nat.min_eq_left hk0]
      · simpa using hk j

/-- Every vector in the uniform multinomial occupancy model corresponds to
an actual cut of the target permutation. -/
theorem cutOccupancy_surjective {n m : ℕ} (σ : Equiv.Perm (Fin n))
    (k : Fin m → ℕ) (hk : ∑ i, k i=n) : ∃ j : CutIndex σ m, cutOccupancy σ j=k := by
  obtain ⟨ps,hps,hkps⟩ := patternCuts_of_occupancy ((List.finRange n).map σ) m k (by simpa using hk)
  obtain ⟨j,hj⟩ := List.mem_iff_get.mp hps
  refine ⟨j,?_⟩
  funext i
  change (((patternCuts ((List.finRange n).map σ) m).get j)[i.val]?.getD []).length=k i
  rw [hj]
  exact hkps i

/-- The concrete cut enumeration and weak compositions are the same
finite space, with their actual occupancy map as the bijection. -/
noncomputable def cutOccupancyEquiv {n m : ℕ} (σ : Equiv.Perm (Fin n)) :
    CutIndex σ m ≃ {k : Fin m → ℕ // k ∈ Finset.piAntidiag Finset.univ n} :=
  Equiv.ofBijective (fun j => ⟨cutOccupancy σ j,by
    exact Finset.mem_piAntidiag.mpr ⟨cutOccupancy_sum σ j,by simp⟩⟩) ⟨
      fun i j h => cutOccupancy_injective σ (congrArg Subtype.val h),
      fun k => by
        obtain ⟨j,hj⟩ := cutOccupancy_surjective σ k.val (Finset.mem_piAntidiag.mp k.property).1
        exact ⟨j,Subtype.ext hj⟩⟩

/-- Equality of the concrete cut weight with the actual uniform occupancy
mass; it is derived from the literal cut lengths. -/
theorem palindromeCutWeight_occupancy {n m : ℕ} (σ : Equiv.Perm (Fin n))
    (j : CutIndex σ m) :
    palindromeCutWeight n m (cutAt σ j)=
      multinomialMass n (fun _ : Fin m => (1 : ℝ)/m) (cutOccupancy σ j) := by
  rw [multinomialMass_factorial n _ _ (cutOccupancy_sum σ j)]
  have hp : ((cutAt σ j).map (fun p => (p.length.factorial : ℝ))).prod=
      ∏ i, ((cutOccupancy σ j i).factorial : ℝ) := by
    conv_lhs => rw [cutAt_ofFn σ j]
    simp [List.map_ofFn,List.prod_ofFn,cutOccupancy,Function.comp_def]
  unfold palindromeCutWeight
  rw [hp]
  simp only [one_div]
  rw [Finset.prod_pow_eq_pow_sum,cutOccupancy_sum]
  ring

/-- Summation over literal cuts can be replaced by summation over uniform
multinomial occupancies using the proved concrete bijection. -/
theorem sum_cutOccupancy {n m : ℕ} (σ : Equiv.Perm (Fin n))
    (f : (Fin m → ℕ) → ℝ) :
    (∑ j : CutIndex σ m, f (cutOccupancy σ j)) =
      ∑ k ∈ Finset.piAntidiag (Finset.univ : Finset (Fin m)) n, f k := by
  classical
  have he := Fintype.sum_equiv (cutOccupancyEquiv (m := m) σ)
    (fun j => f (cutOccupancy σ j)) (fun k => f k.val) (fun _ => rfl)
  rw [he]
  exact Finset.sum_coe_sort _ f

/-- Prefix lengths are the literal starting positions of occupancy cells. -/
theorem cutStart_range (ps : List (List α)) (i : ℕ) :
    cutStart ps i=∑ r ∈ Finset.range i, (ps[r]?.getD []).length := by
  induction ps generalizing i with
  | nil => simp [cutStart]
  | cons p ps ih =>
    cases i with
    | zero => simp [cutStart]
    | succ i =>
      rw [Finset.sum_range_succ']
      simpa [cutStart, ih, Nat.add_comm] using congrArg (fun v => p.length+v) (ih i)

/-- Membership in the actual cut enumeration is exactly the ordered
partition condition, including empty parts. -/
theorem patternCuts_mem_iff (p : List α) (m : ℕ) (ps : List (List α)) :
    ps ∈ patternCuts p m ↔ ps.length=m ∧ ps.flatten=p := by
  refine ⟨patternCuts_length_flatten p m ps,?_⟩
  rintro ⟨hlen,hflat⟩
  let k : Fin m → ℕ := fun i => (ps[i.val]?.getD []).length
  have hsum : ∑ i, k i=p.length := by
    have he := congrArg (fun xs : List (List α) => (xs.map List.length).sum) (List.ofFn_get ps)
    rw [List.map_ofFn,List.sum_ofFn] at he
    simp only [Function.comp_apply] at he
    have hf := congrArg List.length hflat
    rw [List.length_flatten] at hf
    have hchange : (∑ i : Fin ps.length, (ps.get i).length)=∑ i : Fin m, k i := by
      subst m
      apply Finset.sum_congr rfl
      intro i _
      simp [k]
    rw [hchange] at he
    exact he.trans hf
  obtain ⟨qs,hqs,hk⟩ := patternCuts_of_occupancy p m k hsum
  have hqslen := (patternCuts_length_flatten p m qs hqs).1
  have hlengths : ps.map List.length=qs.map List.length := by
    apply List.ext_getElem (by simp [hlen,hqslen])
    intro r hr hqr
    have hrps : r<ps.length := by simpa using hr
    have hrqs : r<qs.length := by simpa using hqr
    have hrm : r < m := by rwa [hlen] at hrps
    have h := hk ⟨r,hrm⟩
    simpa [k,List.getElem?_eq_getElem hrps,List.getElem?_eq_getElem hrqs] using h.symm
  have he := cut_eq_of_lengths ps qs
    (hflat.trans (patternCuts_length_flatten p m qs hqs).2.symm) hlengths
  rwa [he]

end FairDice
