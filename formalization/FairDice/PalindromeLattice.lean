import FairDice.LatticeWeights
import FairDice.PoissonCollision

namespace FairDice

private theorem lattice_prefactor_bound (ell : ℕ) (hell : 1 ≤ ell) (x : ℝ) (hx : 0 ≤ x) :
    (3 * 2^(ell+1) * Real.sqrt (ell+1 : ℝ)) * (ell+1 : ℝ) * (3*x)^ell ≤ (108*x)^ell := by
  have hcub (k : ℕ) : (k+1)^3 ≤ 9^k := by
    induction k with
    | zero => norm_num
    | succ k ih =>
      have hb := Nat.pow_le_pow_left (show k+2 ≤ 2*(k+1) by omega) 3
      have h : (k+2)^3 ≤ 9*(k+1)^3 := by
        rw [mul_pow] at hb
        norm_num at hb
        exact hb.trans (Nat.mul_le_mul_right _ (by norm_num : 8 ≤ 9))
      calc
        (k+1+1)^3 ≤ 9*(k+1)^3 := by simpa [Nat.add_assoc] using h
        _ ≤ 9*9^k := Nat.mul_le_mul_left 9 ih
        _ = 9^(k+1) := by rw [pow_succ]; ring
  have hcubR : (ell+1 : ℝ)^3 ≤ (9 : ℝ)^ell := by exact_mod_cast hcub ell
  have hs := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ ell+1)
  have hpoly : ((ell+1 : ℝ)*Real.sqrt (ell+1 : ℝ))^2 ≤ ((3 : ℝ)^ell)^2 := by
    have hp : ((3 : ℝ)^ell)^2 = (9 : ℝ)^ell := by
      rw [← pow_mul, Nat.mul_comm ell 2, pow_mul]
      norm_num
    rw [mul_pow, hs, hp]
    nlinarith
  have hsqr : (ell+1 : ℝ)*Real.sqrt (ell+1 : ℝ) ≤ (3 : ℝ)^ell := by
    nlinarith [Real.sqrt_nonneg (ell+1 : ℝ), pow_nonneg (by norm_num : (0 : ℝ) ≤ 3) ell]
  have h6 : (6 : ℝ) ≤ 6^ell := by
    exact_mod_cast (Nat.pow_le_pow_right (by norm_num : 1 ≤ 6) hell)
  calc
    _ = 6 * ((ell+1 : ℝ)*Real.sqrt (ell+1 : ℝ)) * (6*x)^ell := by
      rw [pow_succ]
      rw [show (6*x)^ell = (2 : ℝ)^ell*(3*x)^ell by rw [← mul_pow]; congr 1; ring]
      ring
    _ ≤ 6 * (3 : ℝ)^ell * (6*x)^ell := by
      gcongr
    _ = 6 * (18*x)^ell := by
      rw [show (18*x)^ell = (3 : ℝ)^ell*(6*x)^ell by rw [← mul_pow]; congr 1; ring]
      ring
    _ ≤ (6 : ℝ)^ell * (18*x)^ell :=
      mul_le_mul_of_nonneg_right h6 (pow_nonneg (by positivity) _)
    _ = (108*x)^ell := by rw [← mul_pow]; congr 1; ring

/-- Lemma `lem:palindrome-lattice`: the full summation argument. Its only
external input is the two scalar classical Poisson mass estimates. -/
theorem palindrome_lattice_bound (H : PoissonEstimates) (ell d M : ℕ)
    (hell : 1 ≤ ell) (hM : d+1 ≤ M) :
    (∑ g ∈ Finset.piAntidiag (Finset.univ : Finset (Fin (ell+1))) M,
      multinomialCollision d (fun j => (g j : ℝ)/M)) ≤
        (108*M/Real.sqrt (d+1 : ℝ))^ell := by
  classical
  let w : ℕ → ℝ := fun k => 1 / Real.sqrt (1+(d : ℝ)*k/M)
  let B : ℝ := 3 * 2^(ell+1) * Real.sqrt (ell+1 : ℝ)
  have hMpos : 0 < M := by omega
  have hMr : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hw (k : ℕ) : 0 ≤ w k := by dsimp [w]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hF (g : Fin (ell+1) → ℕ)
      (hg : g ∈ Finset.piAntidiag Finset.univ M) :
      ∃ j : Fin (ell+1), multinomialCollision d (fun i => (g i : ℝ)/M) ≤
        B * ∏ i : {i : Fin (ell+1) // i ≠ j}, w (g i.val) := by
    have hsum : ∑ i, g i = M := (Finset.mem_piAntidiag.mp hg).1
    obtain ⟨j, hj⟩ := composition_large_coordinate M g hsum
    have hu0 (i : Fin (ell+1)) : (0 : ℝ) ≤ (g i : ℝ)/M := by positivity
    have hu : (∑ i, (g i : ℝ)/M) = 1 := by
      rw [← Finset.sum_div]
      have hcast : (∑ i, (g i : ℝ)) = M := by exact_mod_cast hsum
      rw [hcast, div_self (ne_of_gt hMr)]
    have hh := poisson_collision_bound H d (fun i => (g i : ℝ)/M) hu0 hu
    simp only [Fintype.card_fin] at hh hj
    have hwprod : (∏ i : Fin (ell+1), 1 / Real.sqrt (1+(d : ℝ)*((g i : ℝ)/M))) =
        w (g j) * ∏ i : {i : Fin (ell+1) // i ≠ j}, w (g i.val) := by
      have he : (fun i : Fin (ell+1) => 1 / Real.sqrt (1+(d : ℝ)*((g i : ℝ)/M))) =
          fun i => w (g i) := by funext i; dsimp [w]; congr 2; ring
      rw [he]
      exact Fintype.prod_eq_mul_prod_subtype_ne _ j
    rw [hwprod] at hh
    have hsup := suppress_large_coordinate d M (ell+1) (g j) hMpos (by omega) hj
    have hp : 0 ≤ ∏ i : {i : Fin (ell+1) // i ≠ j}, w (g i.val) :=
      Finset.prod_nonneg (fun i _ => hw _)
    refine ⟨j, hh.trans ?_⟩
    have he := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsup (show (0 : ℝ) ≤ 3*2^(ell+1) by positivity)) hp
    push_cast at he
    convert he using 1 <;> dsimp [B, w] <;> ring
  have hh := composition_sum_le M w hw (fun g : Fin (ell+1) → ℕ =>
    multinomialCollision d (fun i => (g i : ℝ)/M)) B hB hF
  have hcard (j : Fin (ell+1)) : Fintype.card {i : Fin (ell+1) // i ≠ j} = ell := by
    simp [Fintype.card_subtype_compl]
  simp_rw [hcard] at hh
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
  push_cast at hh
  have hsum := lattice_weight_sum d M hM
  have hpow : (∑ k : Fin (M+1), w k.val)^ell ≤ (3*M/Real.sqrt (d+1 : ℝ))^ell := by
    exact pow_le_pow_left₀ (Finset.sum_nonneg (fun k _ => hw _)) hsum ell
  have hpref := lattice_prefactor_bound ell hell (M/Real.sqrt (d+1 : ℝ)) (by positivity)
  calc
    _ ≤ B * ((ell+1 : ℝ)*(∑ k : Fin (M+1), w k.val)^ell) := hh
    _ ≤ B * ((ell+1 : ℝ)*(3*M/Real.sqrt (d+1 : ℝ))^ell) := by gcongr
    _ ≤ (108*M/Real.sqrt (d+1 : ℝ))^ell := by
      simpa [B, mul_div_assoc, mul_assoc] using hpref

end FairDice
