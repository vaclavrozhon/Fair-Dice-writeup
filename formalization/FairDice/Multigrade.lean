import FairDice.PlaceConstruction

namespace FairDice

open Polynomial

def digitColor (n : ℕ) (hn : 0 < n) (t : Fin (n^(n - 1))) : Fin n :=
  ⟨(n.digits t.val).sum % n, Nat.mod_lt _ hn⟩

/-- The classical Prouhet digit-sum identity cited as Lemma 5.2. Leading
zero digits do not change the color, so `Nat.digits` gives the same map. -/
def ProuhetExternal : Prop :=
  ∀ n : ℕ, ∀ hn : 2 ≤ n, MomentBalanced (digitColor n (by omega)) (n - 2)

/-- Choudhry, Theorem 6: consecutive integers `1,...,2*n^(n-2)` split into
equally sized classes with matching positive moments. The zeroth moment
records the equal class sizes. -/
def ChoudhryExternal : Prop :=
  ∀ n : ℕ, 3 ≤ n → ∃ c : Fin (2 * n^(n - 2)) → Fin n,
    ∀ q ≤ n - 2, ∀ a b : Fin n,
      (∑ t ∈ Finset.univ.filter (fun t => c t = a), (t.val + 1 : ℚ)^q) =
        ∑ t ∈ Finset.univ.filter (fun t => c t = b), (t.val + 1 : ℚ)^q

/-- Translating a consecutive multigrade partition preserves every moment
up to its degree. This is proved here, not included in the external input. -/
theorem translate_moments {n m d : ℕ} (c : Fin m → Fin n)
    (hc : ∀ q ≤ d, ∀ a b : Fin n,
      (∑ t ∈ Finset.univ.filter (fun t => c t = a), (t.val + 1 : ℚ)^q) =
        ∑ t ∈ Finset.univ.filter (fun t => c t = b), (t.val + 1 : ℚ)^q) :
    MomentBalanced c d := by
  intro q hq a b
  let p : ℚ[X] := (X - 1)^q
  have hp : p.natDegree ≤ d := by
    have hlin : (X - 1 : ℚ[X]).natDegree ≤ 1 := by compute_degree!
    exact (natDegree_pow_le.trans (Nat.mul_le_mul_left q hlin)).trans (by omega)
  have he : (∑ t ∈ Finset.univ.filter (fun t => c t = a), p.eval (t.val + 1 : ℚ)) =
      ∑ t ∈ Finset.univ.filter (fun t => c t = b), p.eval (t.val + 1 : ℚ) := by
    simp_rw [eval_eq_sum_range' (p := p) (n := d + 1) (by omega)]
    rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ.filter (fun t => c t = b))]
    apply Finset.sum_congr rfl
    intro k hk
    rw [← Finset.mul_sum, ← Finset.mul_sum, hc k (by simpa using Finset.mem_range.mp hk) a b]
  simpa [p] using he

theorem prouhet_place_construction (hext : ProuhetExternal) (n : ℕ) (hn : 2 ≤ n) :
    ∃ D : RankedDice (Fin n) (n^(n - 1)), PlaceFair D := by
  exact moment_coloring_construction hn (pow_pos (by omega) _)
    (digitColor n (by omega)) (hext n hn)

/-- The improved full-set place-fair upper bound: `2*n^(n-2)` faces per die.
The only external premise is Choudhry's consecutive partition theorem. -/
theorem improved_place_construction (hext : ChoudhryExternal) (n : ℕ) (hn : 2 ≤ n) :
    ∃ D : RankedDice (Fin n) (2 * n^(n - 2)), PlaceFair D := by
  by_cases hn2 : n = 2
  · subst n
    have hc : MomentBalanced (id : Fin 2 → Fin 2) 0 := by
      intro q hq a b
      have hq0 : q = 0 := by omega
      have hf (x : Fin 2) : Finset.univ.filter (fun t : Fin 2 => t = x) = {x} := by ext; simp
      simp [hq0, hf]
    simpa using moment_coloring_construction (n := 2) (m := 2) (by omega) (by omega) id hc
  · obtain ⟨c, hc⟩ := hext n (by omega)
    exact moment_coloring_construction hn (Nat.mul_pos (by omega) (pow_pos (by omega) _))
      c (translate_moments c hc)

theorem one_die_place_construction : ∃ D : RankedDice (Fin 1) 1, PlaceFair D := by
  refine ⟨blockDice (by omega) (fun _ => Equiv.refl _), ?_⟩
  intro a b
  have hab : a = b := Fin.ext (by omega)
  rw [hab]

end FairDice
