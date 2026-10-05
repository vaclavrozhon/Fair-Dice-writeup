import FairDice.SegmentErrors

namespace FairDice

/-- Two different starts in one residue class modulo their segment length
are separated by at least that length. -/
theorem same_residue_separated (k a b : ℕ) (hk : 0 < k) (hab : a≠b)
    (hmod : a%k=b%k) : a+k ≤ b ∨ b+k ≤ a := by
  have haa := Nat.mod_add_div a k
  have hbb := Nat.mod_add_div b k
  have hdir (a b : ℕ) (hab : a<b) (hmod : a%k=b%k) : a+k ≤ b := by
    have haa := Nat.mod_add_div a k
    have hbb := Nat.mod_add_div b k
    have hd : a/k<b/k := by
      by_contra h
      have hm := Nat.mul_le_mul_left k (le_of_not_gt h)
      nlinarith
    have hm := Nat.mul_le_mul_left k (Nat.succ_le_of_lt hd)
    nlinarith
  rcases lt_or_gt_of_ne hab with h | h
  · exact Or.inl (hdir a b h hmod)
  · exact Or.inr (hdir b a h hmod.symm)

def consecutiveEmbedding {n : ℕ} (a k : ℕ) (h : a+k ≤ n) : Fin k ↪ Fin n :=
  ⟨fun j => ⟨a+j.val,by omega⟩,fun i j hij => Fin.ext (by
    have hh := congrArg Fin.val hij
    dsimp at hh
    omega)⟩

def segmentAlphabet {n : ℕ} (σ : Equiv.Perm (Fin n)) (a k : ℕ) (h : a+k ≤ n) : Finset (Fin n) :=
  Finset.univ.image (fun j => σ (consecutiveEmbedding a k h j))

/-- The actual ordered pattern of a consecutive segment, with its alphabet
represented as a subtype for the proved independence law. -/
def segmentPattern {n : ℕ} (σ : Equiv.Perm (Fin n)) (a k : ℕ) (h : a+k ≤ n) :
    List (segmentAlphabet σ a k h) :=
  List.ofFn (fun j : Fin k => ⟨σ (consecutiveEmbedding a k h j),
    Finset.mem_image.mpr ⟨j,Finset.mem_univ j,rfl⟩⟩)

@[simp] theorem segmentPattern_length {n : ℕ} (σ : Equiv.Perm (Fin n)) (a k : ℕ) (h : a+k ≤ n) :
    (segmentPattern σ a k h).length=k := by simp [segmentPattern]

theorem segmentPattern_nodup {n : ℕ} (σ : Equiv.Perm (Fin n)) (a k : ℕ) (h : a+k ≤ n) :
    (segmentPattern σ a k h).Nodup := by
  apply List.nodup_ofFn.mpr
  intro i j hij
  exact (consecutiveEmbedding a k h).injective (σ.injective (congrArg Subtype.val hij))

/-- Segments of one length and residue class have disjoint actual letters,
for every target permutation. This supplies the structural premise used
by the fixed-color chaos theorem. -/
theorem residue_segment_alphabets_disjoint {n : ℕ} (σ : Equiv.Perm (Fin n))
    (k a b : ℕ) (hk : 0 < k) (ha : a+k ≤ n) (hb : b+k ≤ n)
    (hab : a≠b) (hmod : a%k=b%k) :
    Disjoint (segmentAlphabet σ a k ha) (segmentAlphabet σ b k hb) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨i,_,hix⟩ := Finset.mem_image.mp hx
  obtain ⟨j,_,hjx⟩ := Finset.mem_image.mp hy
  have he := σ.injective (hix.trans hjx.symm)
  have hev := congrArg Fin.val he
  change a+i.val=b+j.val at hev
  rcases same_residue_separated k a b hk hab hmod with h | h <;> omega

end FairDice
