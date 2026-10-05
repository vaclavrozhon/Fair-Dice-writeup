import FairDice.RankDice
import FairDice.PlacePolynomials

namespace FairDice

open Polynomial

theorem sum_rank_indicator {m : ℕ} (S : Finset (Fin m)) :
    (∑ u : Fin m, if u ∈ S then (X : ℚ[X]) else 1) =
      C ((m - S.card : ℕ) : ℚ) + C (S.card : ℚ) * X := by
  classical
  have hf : (Finset.univ.filter (fun u : Fin m => u ∈ S)) = S := by ext; simp
  have hg : (Finset.univ.filter (fun u : Fin m => u ∉ S)) = Sᶜ := by ext; simp
  rw [Finset.sum_ite]
  simp [hf, hg, nsmul_eq_mul, add_comm, Finset.card_compl]

theorem block_face_factor {n m : ℕ} (hn : 0 < n) (e : Fin m → Equiv.Perm (Fin n))
    (a b : Fin n) (t : Fin m) :
    (∑ u : Fin m, if (blockDice hn e).label b u < (blockDice hn e).label a t then
      (X : ℚ[X]) else 1) =
    if e t b < e t a then C ((m : ℚ) - t.val - 1) + C ((t.val : ℚ) + 1) * X
    else C ((m : ℚ) - t.val) + C (t.val : ℚ) * X := by
  by_cases hba : e t b < e t a
  · have hcond (u : Fin m) : (blockDice hn e).label b u < (blockDice hn e).label a t ↔
        u ∈ Finset.Iic t := by
      rw [blockDice_lt]
      simp only [hba, and_true, Finset.mem_Iic]
      omega
    simp_rw [hcond]
    rw [sum_rank_indicator, if_pos hba, Fin.card_Iic]
    simp only [Nat.cast_sub (show t.val + 1 ≤ m by omega), Nat.cast_add, Nat.cast_one,
      map_sub, map_add, map_one]
    ring
  · have hcond (u : Fin m) : (blockDice hn e).label b u < (blockDice hn e).label a t ↔
        u ∈ Finset.Iio t := by rw [blockDice_lt]; simp [hba]
    simp_rw [hcond]
    rw [sum_rank_indicator, if_neg hba, Fin.card_Iio]
    simp [Nat.cast_sub (show t.val ≤ m by omega)]

theorem prod_off_diagonal {n : ℕ} (a : Fin n) (f : Fin n → ℚ[X]) :
    (∏ b : {b : Fin n // b ≠ a}, f b.val) =
      ∏ b : Fin n, if b = a then 1 else f b := by
  classical
  rw [Finset.prod_ite]
  simp only [Finset.prod_const_one, one_mul]
  exact (Finset.prod_subtype _ (fun b => by simp) f).symm

theorem prod_rank_split {n : ℕ} (r : Fin n) (A B : ℚ[X]) :
    (∏ i : Fin n, if i = r then 1 else if i < r then A else B) =
      A^r.val * B^(n - 1 - r.val) := by
  classical
  have he (i : Fin n) : (if i = r then 1 else if i < r then A else B) =
      (if i < r then A else 1) * (if r < i then B else 1) := by
    rcases lt_trichotomy i r with h | h | h <;> simp [h, ne_of_lt, ne_of_gt, not_lt_of_ge, le_of_lt]
  have hlt : Finset.univ.filter (fun i : Fin n => i < r) = Finset.Iio r := by ext; simp
  have hgt : Finset.univ.filter (fun i : Fin n => r < i) = Finset.Ioi r := by ext; simp
  simp_rw [he]
  rw [Finset.prod_mul_distrib]
  simp only [Finset.prod_ite, Finset.prod_const, one_pow, mul_one,
    hlt, hgt, Fin.card_Iio, Fin.card_Ioi]

theorem block_face_product {n m : ℕ} (hn : 0 < n) (e : Fin m → Equiv.Perm (Fin n))
    (a : Fin n) (t : Fin m) :
    (∏ b : {b : Fin n // b ≠ a}, ∑ u : Fin m,
      if (blockDice hn e).label b.val u < (blockDice hn e).label a t then (X : ℚ[X]) else 1) =
      (placePosition n m (e t a).val).eval (t.val : ℚ[X]) := by
  rw [placePosition_eval]
  simp_rw [block_face_factor]
  let A : ℚ[X] := C ((m : ℚ) - t.val - 1) + C ((t.val : ℚ) + 1) * X
  let B : ℚ[X] := C ((m : ℚ) - t.val) + C (t.val : ℚ) * X
  rw [prod_off_diagonal a (fun b => if e t b < e t a then A else B)]
  calc
    _ = ∏ r : Fin n, if r = e t a then 1 else if r < e t a then A else B := by
      apply Fintype.prod_equiv (e t)
      intro b
      simp only [(e t).injective.eq_iff]
    _ = _ := prod_rank_split _ A B

theorem rankGenerating_block {n m : ℕ} (hn : 0 < n) (e : Fin m → Equiv.Perm (Fin n))
    (a : Fin n) : rankGenerating (blockDice hn e) a =
      ∑ t : Fin m, (placePosition n m (e t a).val).eval (t.val : ℚ[X]) := by
  apply Finset.sum_congr rfl
  intro t _
  exact block_face_product hn e a t

/-- Theorem 5.3, realized by actual distinct integer face labels. The face
type is `Fin m`, so the construction has exactly `m` faces on each die. -/
theorem moment_coloring_construction {n m : ℕ} (hn : 2 ≤ n) (_hm : 0 < m)
    (c : Fin m → Fin n) (hc : MomentBalanced c (n - 2)) :
    ∃ D : RankedDice (Fin n) m, PlaceFair D := by
  letI : NeZero n := ⟨by omega⟩
  let D := blockDice (show 0 < n by omega) (fun t => Equiv.addRight (c t))
  refine ⟨D, ?_⟩
  intro a b
  rw [rankGenerating_block, rankGenerating_block]
  exact placePosition_balanced hn c hc a b

end FairDice
