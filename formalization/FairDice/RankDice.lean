import Mathlib

namespace FairDice

open Polynomial

/-- Equal-sided dice with distinct integer labels on all faces. -/
structure RankedDice (α : Type*) (m : ℕ) where
  label : α → Fin m → ℕ
  injective : Function.Injective (fun p : α × Fin m => label p.1 p.2)

variable {α : Type*} [DecidableEq α] [Fintype α] {m : ℕ}

/-- Coefficient `k` counts outcomes in which exactly `k` other dice precede
the distinguished die. Products represent independent face choices. -/
noncomputable def rankGenerating (D : RankedDice α m) (a : α) : ℚ[X] :=
  ∑ t : Fin m, ∏ b : {b : α // b ≠ a}, ∑ u : Fin m,
    if D.label b.val u < D.label a t then X else 1

def PlaceFair (D : RankedDice α m) : Prop :=
  ∀ a b : α, rankGenerating D a = rankGenerating D b

/-- Literal finite-outcome semantics of the generating polynomial. The
sample space has one uniform face for each die, with the distinguished face
written separately from all other faces. -/
theorem rankGenerating_coeff (D : RankedDice α m) (a : α) (k : ℕ) :
    (rankGenerating D a).coeff k =
      ∑ t : Fin m, (((Finset.univ : Finset ({b : α // b ≠ a} → Fin m)).filter
        (fun f => ((Finset.univ : Finset {b : α // b ≠ a}).filter
          (fun b => D.label b.val (f b) < D.label a t)).card = k)).card : ℚ) := by
  classical
  simp only [rankGenerating, Fintype.prod_sum, finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.card_filter, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro f _
  have he : (∏ b : {b : α // b ≠ a},
      if D.label b.val (f b) < D.label a t then (X : ℚ[X]) else 1) =
        X^((Finset.univ : Finset {b : α // b ≠ a}).filter
          (fun b => D.label b.val (f b) < D.label a t)).card := by
    simp [Finset.prod_ite]
  rw [he]
  simp [coeff_X_pow, eq_comm]

theorem rankGenerating_normalization (D : RankedDice α m) (a : α) :
    (rankGenerating D a).eval 1 = (m : ℚ)^(Fintype.card α) := by
  classical
  have hn : 0 < Fintype.card α := Fintype.card_pos_iff.mpr ⟨a⟩
  simp only [rankGenerating, eval_finsetSum, eval_prod, apply_ite, eval_X, eval_one,
    ite_self, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one, Finset.prod_const]
  have hcard : Fintype.card {b : α // b ≠ a} = Fintype.card α - 1 := by
    simp [Fintype.card_subtype_compl]
  rw [hcard, ← pow_succ']
  congr 1
  omega

/-- A block consists of one face of each die, in the order prescribed by the
permutation `e t`. Labels are consecutive positions in the concatenated blocks. -/
def blockDice {n : ℕ} (hn : 0 < n) (e : Fin m → Equiv.Perm (Fin n)) : RankedDice (Fin n) m where
  label a t := n * t.val + (e t a).val
  injective := by
    rintro ⟨a, t⟩ ⟨b, u⟩ h
    have hr : (e t a).val = (e u b).val := by
      have hh := congrArg (fun z => z % n) h
      simpa only [Nat.add_mod, Nat.mul_mod, Nat.mod_self, Nat.mod_mod, Nat.zero_mod, zero_mul, zero_add,
        Nat.mod_eq_of_lt (e t a).isLt, Nat.mod_eq_of_lt (e u b).isLt] using hh
    have htu : t = u := by
      apply Fin.ext
      dsimp at h
      nlinarith
    subst u
    have hab : a = b := (e t).injective (Fin.ext hr)
    subst b
    rfl

theorem blockDice_lt {n : ℕ} (hn : 0 < n) (e : Fin m → Equiv.Perm (Fin n))
    (a b : Fin n) (t u : Fin m) :
    (blockDice hn e).label b u < (blockDice hn e).label a t ↔
      u < t ∨ u = t ∧ e t b < e t a := by
  change n * u.val + (e u b).val < n * t.val + (e t a).val ↔ _
  have hb := (e u b).isLt
  have ha := (e t a).isLt
  constructor
  · intro h
    by_cases hut : u < t
    · exact Or.inl hut
    · have hut' : t.val ≤ u.val := by simpa using not_lt.mp hut
      have hmul := Nat.mul_le_mul_left n hut'
      have he : u = t := by
        apply Fin.ext
        by_contra hne
        have hh : t.val + 1 ≤ u.val := by omega
        have hmul' := Nat.mul_le_mul_left n hh
        nlinarith
      exact Or.inr ⟨he, by simpa [he] using h⟩
  · rintro (h | ⟨rfl, h⟩)
    · have hh : u.val + 1 ≤ t.val := h
      have hmul := Nat.mul_le_mul_left n hh
      nlinarith
    · simpa using h

end FairDice
