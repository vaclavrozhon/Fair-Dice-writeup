import FairDice.FaceMoments
import FairDice.HilbertRank

namespace FairDice

variable {α : Type*} [DecidableEq α] [Fintype α]

omit [Fintype α] in
theorem tailProduct_append (s t p q : List α) :
    tailProduct s t (p ++ q) = tailProduct s t p * tailProduct s t q := by
  simp [tailProduct, List.map_append, List.prod_append]

omit [DecidableEq α] [Fintype α] in
theorem sum_list_get (L : List (List α)) (f : List α → ℚ) :
    (∑ i : Fin L.length, f (L.get i)) = (L.map f).sum := by
  rw [← List.sum_ofFn]
  congr 1
  exact List.ofFn_getElem_eq_map L f

/-- Each face supplies one factor in a matrix factorization of the uniform
moment matrix. Full rank therefore requires at least `r+1` faces. -/
theorem individual_rank_bound {s : List α} (hs : PermutationFair s) (a : α)
    (p q : List α) (r : ℕ) (hnodup : (a :: (p ++ q)).Nodup)
    (hp : p.length = r) (hq : q.length = r) : r + 1 ≤ s.count a := by
  classical
  let L := faceSuffixes a s
  let U : Matrix (Fin (r + 1)) (Fin L.length) ℚ :=
    fun i k => tailProduct s (L.get k) (p.take i.val)
  let V : Matrix (Fin L.length) (Fin (r + 1)) ℚ :=
    fun k j => tailProduct s (L.get k) (q.take j.val) / s.count a
  have hca : (s.count a : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (List.count_pos_iff.mpr (hs.1 a)))
  have heq : U * V = hilbertMatrix (r + 1) := by
    ext i j
    have hi : i.val ≤ r := by omega
    have hj : j.val ≤ r := by omega
    have hsub : (p.take i.val ++ q.take j.val).Sublist (p ++ q) :=
      (List.take_sublist _ _).append (List.take_sublist _ _)
    have hnd := ((hsub).cons_cons a).nodup hnodup
    have hmoment := faceSuffixes_moment hs a (p.take i.val ++ q.take j.val) hnd
    simp only [Matrix.mul_apply, U, V, ← mul_div_assoc, ← tailProduct_append,
      ← Finset.sum_div]
    rw [sum_list_get L (fun t => tailProduct s t (p.take i.val ++ q.take j.val))]
    change ((L.map (fun t => tailProduct s t (p.take i.val ++ q.take j.val))).sum) /
      (s.count a : ℚ) = _
    rw [hmoment]
    simp only [List.length_append, List.length_take, hp, hq, min_eq_left hi, min_eq_left hj,
      hilbertMatrix, Nat.cast_add]
    field_simp
  have hrank : r + 1 ≤ L.length := by
    calc
      _ = (hilbertMatrix (r + 1)).rank := (hilbertMatrix_rank _).symm
      _ = (U * V).rank := congrArg Matrix.rank heq.symm
      _ ≤ U.rank := Matrix.rank_mul_le_left _ _
      _ ≤ Fintype.card (Fin L.length) := Matrix.rank_le_card_width _
      _ = _ := Fintype.card_fin _
  simpa [L, length_faceSuffixes] using hrank

/-- Theorem 4.4. The integer expression `(n+1)/2` is `ceil(n/2)`. -/
theorem each_die_linear {s : List α} (hs : PermutationFair s) (a : α) :
    (Fintype.card α + 1) / 2 ≤ s.count a := by
  classical
  let l := (Finset.univ.erase a).toList
  let r := (Fintype.card α - 1) / 2
  have hl : l.length = Fintype.card α - 1 := by simp [l]
  have hr : r ≤ l.length := by dsimp [r]; omega
  have hnd : (a :: l).Nodup := by simp [l, Finset.nodup_toList]
  have hsub : (l.take r ++ (l.drop r).take r).Sublist l := by
    have h := (List.take_sublist r (l.drop r)).append_left (l.take r)
    simpa using h
  have hp : (l.take r).length = r := by simp [List.length_take, min_eq_left hr]
  have hq : ((l.drop r).take r).length = r := by
    rw [List.length_take, List.length_drop]
    apply min_eq_left
    dsimp [r]
    omega
  have hb := individual_rank_bound hs a (l.take r) ((l.drop r).take r) r
    (hsub.cons_cons a |>.nodup hnd) hp hq
  have hn : 0 < Fintype.card α := Fintype.card_pos_iff.mpr ⟨a⟩
  dsimp [r] at hb
  omega

end FairDice
