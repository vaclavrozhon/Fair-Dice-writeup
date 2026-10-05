import FairDice.CenteredBumps

namespace FairDice

open Set

/-- Any rational interval contains arbitrarily many strictly ordered
positive-length intervals with rational endpoints. -/
theorem rational_ordered_intervals (m : ℕ) (x y : ℚ) (hxy : x < y) :
    ∃ a b : Fin m → ℚ,
      (∀ j, x < a j ∧ a j < b j ∧ b j < y) ∧
      ∀ i j, i < j → b i < a j := by
  let D : ℚ := (y-x)/(2*m+1)
  have hden : (0 : ℚ) < 2*m+1 := by positivity
  have hD : 0 < D := div_pos (sub_pos.mpr hxy) hden
  have hDeq : (2*m+1 : ℚ)*D = y-x := by dsimp [D]; field_simp
  refine ⟨fun j => x + (2*(j.val : ℚ)+1)*D,
    fun j => x + (2*(j.val : ℚ)+2)*D, ?_, ?_⟩
  · intro j
    have hj : (j.val : ℚ) < m := by exact_mod_cast j.isLt
    have hj' : (j.val : ℚ)+1 ≤ m := by exact_mod_cast Nat.succ_le_of_lt j.isLt
    have hj0 : (0 : ℚ) ≤ j.val := Nat.cast_nonneg _
    constructor
    · nlinarith
    · constructor <;> nlinarith
  · intro i j hij
    have hh : (i.val : ℚ)+1 ≤ j.val := by exact_mod_cast (show i.val+1 ≤ j.val by omega)
    nlinarith

/-- Existence of the fixed rational support intervals and an admissible
open neighborhood for an arbitrary interior real node. -/
theorem centered_intervals_exist (m : ℕ) (L u R : ℝ)
    (hL0 : 0 ≤ L) (hLu : L < u) (huR : u < R) (hR1 : R ≤ 1) :
    ∃ I : CorrectionIntervals m, ∃ V : Set ℝ, IsOpen V ∧ u ∈ V ∧
      (∀ t ∈ V, I.admissible t) ∧
      (∀ j, L < I.leftA j ∧ L < I.rightA j) ∧
      (∀ j, I.leftB j < R ∧ I.rightB j < R) := by
  obtain ⟨x, hxL, hxu⟩ := exists_rat_btwn hLu
  obtain ⟨y, hxy, hyu⟩ := exists_rat_btwn hxu
  obtain ⟨z, huz, hzR⟩ := exists_rat_btwn huR
  obtain ⟨w, hzw, hwR⟩ := exists_rat_btwn hzR
  have hxyQ : x < y := by exact_mod_cast hxy
  have hzwQ : z < w := by exact_mod_cast hzw
  obtain ⟨a, b, hab, hord⟩ := rational_ordered_intervals m x y hxyQ
  obtain ⟨c, d, hcd, hord'⟩ := rational_ordered_intervals m z w hzwQ
  let I : CorrectionIntervals m := {
    la := a, lb := b, ra := c, rb := d,
    left_pos := fun j => (hab j).2.1,
    right_pos := fun j => (hcd j).2.1,
    left_order := hord, right_order := hord',
    left_unit := fun j => ⟨by
      have hh : (0 : ℝ) ≤ a j := by exact (hL0.trans hxL.le).trans (by exact_mod_cast (hab j).1.le)
      exact_mod_cast hh,
      by
        have hh : (b j : ℝ) ≤ 1 :=
          (by exact_mod_cast (hab j).2.2.le : (b j : ℝ) ≤ y).trans (hyu.le.trans (huR.le.trans hR1))
        exact_mod_cast hh⟩,
    right_unit := fun j => ⟨by
      have hh : (0 : ℝ) ≤ c j :=
        (hL0.trans (hLu.le.trans huz.le)).trans (by exact_mod_cast (hcd j).1.le)
      exact_mod_cast hh,
      by
        have hh : (d j : ℝ) ≤ 1 :=
          (by exact_mod_cast (hcd j).2.2.le : (d j : ℝ) ≤ w).trans (hwR.le.trans hR1)
        exact_mod_cast hh⟩ }
  refine ⟨I, Ioo (y : ℝ) z, isOpen_Ioo, ⟨hyu, huz⟩, ?_, ?_, ?_⟩
  · intro t ht
    refine ⟨(hL0.trans hxL.le).trans (hxy.le.trans ht.1.le),
      ht.2.le.trans (hzw.le.trans (hwR.le.trans hR1)), ?_, ?_⟩
    · intro j
      exact (by exact_mod_cast (hab j).2.2 : (b j : ℝ) < y).trans ht.1
    · intro j
      exact ht.2.le.trans (by exact_mod_cast (hcd j).1.le)
  · intro j
    constructor
    · exact hxL.trans (by exact_mod_cast (hab j).1)
    · exact (hLu.trans huz).trans (by exact_mod_cast (hcd j).1)
  · intro j
    constructor
    · exact (by exact_mod_cast (hab j).2.2 : (b j : ℝ) < y).trans (hyu.trans huR)
    · exact (by exact_mod_cast (hcd j).2.2 : (d j : ℝ) < w).trans hwR

/-- Lemma `individual-centered-bumps` for one node: actual step functions,
their two truncated moment identities, support, rational values,
continuous coefficients and uniform local bounds. Apply this independently
to the disjoint neighborhoods of the finitely many starting nodes. -/
theorem centered_bump_exists (m : ℕ) (L u R : ℝ)
    (hL0 : 0 ≤ L) (hLu : L < u) (huR : u < R) (hR1 : R ≤ 1) :
    ∃ I : CorrectionIntervals m, ∃ V : Set ℝ, IsOpen V ∧ u ∈ V ∧
      (∀ t ∈ V, I.admissible t) ∧
      (∀ t ∈ V, Function.support (I.bump t) ⊆ Ioo L R) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ t ∈ V, ∀ x : ℝ, |I.bump t x| ≤ C := by
  obtain ⟨I, V, hVo, huV, hVa, hL, hR⟩ := centered_intervals_exist m L u R hL0 hLu huR hR1
  obtain ⟨W, hWo, huW, C, hC, hb⟩ := I.locally_bounded u
  exact ⟨I, V ∩ W, hVo.inter hWo, ⟨huV, huW⟩,
    fun t ht => hVa t ht.1, fun t _ => I.support_subset t L R hL hR,
    C, hC, fun t ht => hb t ht.2⟩

end FairDice
