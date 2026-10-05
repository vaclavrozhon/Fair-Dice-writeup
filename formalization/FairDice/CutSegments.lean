import FairDice.ColoredSegments
import FairDice.BlockHomogeneous

namespace FairDice

/-- Starting position of a part of a concrete ordered cut. -/
def cutStart {α : Type*} (ps : List (List α)) (i : ℕ) : ℕ :=
  ((ps.take i).flatten).length

/-- A selected cut really is the consecutive interval used by the coloring
argument, including empty parts and repeated cut positions. -/
theorem cut_part_slice {α : Type*} (ps : List (List α)) (i : ℕ) (hi : i<ps.length) :
    (ps.flatten.drop (cutStart ps i)).take ps[i].length = ps[i] := by
  have he : ps=(ps.take i)++(ps[i]::ps.drop (i+1)) := by
    rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]
  have hf : ps.flatten=(ps.take i).flatten++(ps[i]++(ps.drop (i+1)).flatten) := by
    conv_lhs => rw [he]
    rw [List.flatten_append, List.flatten_cons]
  rw [hf]
  simp [cutStart]

theorem cut_part_fits {α : Type*} (ps : List (List α)) (i : ℕ) (hi : i<ps.length) :
    cutStart ps i+ps[i].length ≤ ps.flatten.length := by
  have he : ps=(ps.take i)++(ps[i]::ps.drop (i+1)) := by
    rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]
  have hf : ps.flatten=(ps.take i).flatten++(ps[i]++(ps.drop (i+1)).flatten) := by
    conv_lhs => rw [he]
    rw [List.flatten_append, List.flatten_cons]
  rw [hf]
  simp [cutStart]

/-- Reindex a valid cut part of length at least three by the actual finite
segment type. No existence or distributional hypothesis is used. -/
def cutSegment {n : ℕ} (ps : List (List (Fin n))) (i : ℕ) (hi : i<ps.length)
    (hflat : ps.flatten.length=n) (hk : 3 ≤ ps[i].length) : ConsecutiveSegment n := by
  have hf := cut_part_fits ps i hi
  rw [hflat] at hf
  refine ⟨(⟨cutStart ps i,by omega⟩,⟨ps[i].length-3,by omega⟩),?_⟩
  dsimp
  omega

@[simp] theorem cutSegment_start {n : ℕ} (ps : List (List (Fin n))) (i : ℕ)
    (hi : i<ps.length) (hf : ps.flatten.length=n) (hk : 3 ≤ ps[i].length) :
    segmentStart (cutSegment ps i hi hf hk)=cutStart ps i := rfl

@[simp] theorem cutSegment_length {n : ℕ} (ps : List (List (Fin n))) (i : ℕ)
    (hi : i<ps.length) (hf : ps.flatten.length=n) (hk : 3 ≤ ps[i].length) :
    segmentLength (cutSegment ps i hi hf hk)=ps[i].length := by
  change ps[i].length-3+3=ps[i].length
  omega

/-- The subtype representation of a segment agrees with taking the literal
slice of the target permutation word. -/
theorem segmentPattern_slice {n : ℕ} (σ : Equiv.Perm (Fin n))
    (a k : ℕ) (h : a+k ≤ n) :
    (segmentPattern σ a k h).map Subtype.val=
      (((List.finRange n).map σ).drop a).take k := by
  apply List.ext_getElem
  · simp [segmentPattern]
    omega
  · intro i hi hj
    simp [segmentPattern, List.getElem_take, List.getElem_drop, consecutiveEmbedding]

/-- Identification of the cut error with the exact colored segment error. -/
theorem cutSegment_pattern {n : ℕ} (σ : Equiv.Perm (Fin n))
    (ps : List (List (Fin n))) (hps : ps.flatten=(List.finRange n).map σ)
    (i : ℕ) (hi : i<ps.length) (hk : 3 ≤ ps[i].length) :
    let hf : ps.flatten.length=n := by rw [hps]; simp
    let t := cutSegment ps i hi hf hk
    (segmentPattern σ (segmentStart t) (segmentLength t) (segment_fits t)).map Subtype.val=ps[i] := by
  dsimp only
  rw [segmentPattern_slice, cutSegment_start, cutSegment_length, ← hps]
  exact cut_part_slice ps i hi

/-- The graph of the selected blocks and their literal cut segments. -/
noncomputable def cutGraph {n m : ℕ} (ps : List (List (Fin n)))
    (hlen : ps.length=m) (hflat : ps.flatten.length=n)
    (I : Finset (Fin m)) (hI : ∀ i ∈ I, 3 ≤ (ps[i.val]?.getD []).length) :
    Finset (BlockSegment (Fin m) n) := by
  classical
  let e : I ↪ BlockSegment (Fin m) n := {
    toFun := fun i => ⟨i.val, cutSegment ps i.val.val (by rw [hlen]; exact i.val.isLt)
      hflat (by simpa [List.getElem?_eq_getElem (show i.val.val<ps.length by
        rw [hlen]; exact i.val.isLt)] using hI i.val i.property)⟩
    inj' := by intro i j h; exact Subtype.ext (congrArg Sigma.fst h) }
  exact Finset.univ.map e

@[simp] theorem cutGraph_card {n m : ℕ} (ps : List (List (Fin n)))
    (hlen : ps.length=m) (hflat : ps.flatten.length=n)
    (I : Finset (Fin m)) (hI : ∀ i ∈ I, 3 ≤ (ps[i.val]?.getD []).length) :
    (cutGraph ps hlen hflat I hI).card=I.card := by
  simp [cutGraph]

theorem cutGraph_blocks {n m : ℕ} (ps : List (List (Fin n)))
    (hlen : ps.length=m) (hflat : ps.flatten.length=n)
    (I : Finset (Fin m)) (hI : ∀ i ∈ I, 3 ≤ (ps[i.val]?.getD []).length) :
    Set.InjOn (fun v : BlockSegment (Fin m) n => v.1) (cutGraph ps hlen hflat I hI) := by
  classical
  intro v hv w hw he
  obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hv
  obtain ⟨j,_,rfl⟩ := Finset.mem_map.mp hw
  have hij : i=j := Subtype.ext he
  subst j
  rfl

theorem cutGraph_error_product {n m : ℕ} (σ : Equiv.Perm (Fin n))
    (ps : List (List (Fin n))) (hlen : ps.length=m)
    (hps : ps.flatten=(List.finRange n).map σ)
    (I : Finset (Fin m)) (hI : ∀ i ∈ I, 3 ≤ (ps[i.val]?.getD []).length)
    (ρ : Fin m → Equiv.Perm (Fin n)) :
    let hf : ps.flatten.length=n := by rw [hps]; simp
    (∏ v ∈ cutGraph ps hlen hf I hI, segmentError σ v ρ) =
      ∏ i ∈ I, palindromeCutDelta ρ ps i := by
  classical
  dsimp only
  rw [cutGraph, Finset.prod_map, ← Finset.prod_attach I]
  apply Finset.prod_congr rfl
  intro i _
  dsimp only [Function.Embedding.coeFn_mk, segmentError]
  rw [cutSegment_pattern σ ps hps]
  simp only [palindromeCutDelta, List.getElem?_eq_getElem (show i.val.val<ps.length by
    rw [hlen]; exact i.val.isLt), Option.getD_some]

/-- Every cut term containing a part of size at most two vanishes, because
palindrome blocks are exactly fair on such parts. -/
theorem cut_product_eq_zero_of_short {n m : ℕ} (σ : Equiv.Perm (Fin n))
    (ps : List (List (Fin n))) (hps : ps ∈ patternCuts ((List.finRange n).map σ) m)
    (I : Finset (Fin m))
    (hI : ¬ ∀ i ∈ I, 3 ≤ (ps[i.val]?.getD []).length)
    (ρ : Fin m → Equiv.Perm (Fin n)) :
    (∏ i ∈ I, palindromeCutDelta ρ ps i)=0 := by
  classical
  push Not at hI
  obtain ⟨i,hi,hshort⟩ := hI
  apply Finset.prod_eq_zero hi
  obtain ⟨hlen,hflat⟩ := patternCuts_length_flatten _ _ _ hps
  have hil : i.val<ps.length := by rw [hlen]; exact i.isLt
  have hp : (ps[i.val]?.getD []).Nodup := by
    rw [List.getElem?_eq_getElem hil]
    exact (List.nodup_flatten.mp (hflat ▸ (List.nodup_finRange n).map σ.injective)).1
      _ (List.getElem_mem hil)
  apply palindromeDelta_short _ _ ((List.nodup_finRange n).map (ρ i).injective) hp
  · intro a ha
    obtain ⟨b,rfl⟩ := (ρ i).surjective a
    exact List.mem_map.mpr ⟨b,List.mem_finRange b,rfl⟩
  · omega

end FairDice
