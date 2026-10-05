import Mathlib

namespace FairDice

open Polynomial

variable {G : Type*} [DecidableEq G] [Fintype G]

/-- Equal sums of like powers in all color classes, including the zeroth
moment (equal class sizes). -/
def MomentBalanced {m : ℕ} (c : Fin m → G) (d : ℕ) : Prop :=
  ∀ q ≤ d, ∀ a b : G,
    (∑ t ∈ Finset.univ.filter (fun t => c t = a), (t.val : ℚ)^q) =
      ∑ t ∈ Finset.univ.filter (fun t => c t = b), (t.val : ℚ)^q

variable {R : Type*} [CommRing R] [Algebra ℚ R]

omit [Fintype G] in
theorem momentBalanced_cast {m d : ℕ} {c : Fin m → G}
    (hc : MomentBalanced c d) (q : ℕ) (hq : q ≤ d) (a b : G) :
    (∑ t ∈ Finset.univ.filter (fun t => c t = a), (t.val : R)^q) =
      ∑ t ∈ Finset.univ.filter (fun t => c t = b), (t.val : R)^q := by
  simpa only [map_sum, map_pow, map_natCast] using congrArg (algebraMap ℚ R) (hc q hq a b)

omit [Fintype G] in
theorem momentBalanced_polynomial {m d : ℕ} {c : Fin m → G}
    (hc : MomentBalanced c d) (p : R[X]) (hp : p.natDegree ≤ d) (a b : G) :
    (∑ t ∈ Finset.univ.filter (fun t => c t = a), p.eval (t.val : R)) =
      ∑ t ∈ Finset.univ.filter (fun t => c t = b), p.eval (t.val : R) := by
  simp_rw [Polynomial.eval_eq_sum_range' (p := p) (n := d + 1) (by omega)]
  rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ.filter (fun t => c t = b))]
  apply Finset.sum_congr rfl
  intro q hq
  rw [← Finset.mul_sum, ← Finset.mul_sum,
    momentBalanced_cast hc q (by simpa using Finset.mem_range.mp hq) a b]

variable [AddCommGroup G]

omit [Algebra ℚ R] in
theorem sum_by_shifted_color {m : ℕ} (c : Fin m → G) (a : G) (f : G → Fin m → R) :
    (∑ t : Fin m, f (a + c t) t) =
      ∑ r : G, ∑ t ∈ Finset.univ.filter (fun t => c t = r - a), f r t := by
  classical
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  have he (r : G) : c t = r - a ↔ a + c t = r := by
    rw [eq_sub_iff_add_eq, add_comm]
  simp_rw [he]
  simp

/-- The algebraic core of the place-fair reduction: all position polynomials
may have the same extra leading term beyond the balanced moment degree. -/
theorem momentBalanced_shifted_polynomials {m d : ℕ} {c : Fin m → G}
    (hc : MomentBalanced c d) (P : G → R[X]) (B : R[X])
    (hP : ∀ r, (P r - B).natDegree ≤ d) (a b : G) :
    (∑ t : Fin m, (P (a + c t)).eval (t.val : R)) =
      ∑ t : Fin m, (P (b + c t)).eval (t.val : R) := by
  have hsplit (x : G) :
      (∑ t : Fin m, (P (x + c t)).eval (t.val : R)) =
        (∑ t : Fin m, B.eval (t.val : R)) +
          ∑ r : G, ∑ t ∈ Finset.univ.filter (fun t => c t = r - x),
            (P r - B).eval (t.val : R) := by
    rw [← sum_by_shifted_color c x (fun r t => (P r - B).eval (t.val : R))]
    simp [eval_sub, Finset.sum_sub_distrib]
  rw [hsplit a, hsplit b]
  congr 1
  apply Finset.sum_congr rfl
  intro r _
  exact momentBalanced_polynomial hc (P r - B) (hP r) _ _

end FairDice
