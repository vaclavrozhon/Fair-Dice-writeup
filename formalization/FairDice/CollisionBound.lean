import FairDice.Approximation

namespace FairDice

theorem prod_one_sub_lower {ι : Type*} (S : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ S, 0 ≤ x i ∧ x i ≤ 1) :
    1 - ∑ i ∈ S, x i ≤ ∏ i ∈ S, (1 - x i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    have hi' := hx i (Finset.mem_insert_self i S)
    have hS : ∀ j ∈ S, 0 ≤ x j ∧ x j ≤ 1 := fun j hj => hx j (Finset.mem_insert_of_mem hj)
    have hmul := mul_le_mul_of_nonneg_left (ih hS) (sub_nonneg.mpr hi'.2)
    have hsum : 0 ≤ ∑ j ∈ S, x j := Finset.sum_nonneg (fun j hj => (hS j hj).1)
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    nlinarith [mul_nonneg hi'.1 hsum]

theorem falling_probability_product {n m : ℕ} (hnm : n ≤ m) (hm : 0 < m) :
    (m.descFactorial n : ℝ) / (m : ℝ)^n =
      ∏ k ∈ Finset.range n, (1 - (k : ℝ) / m) := by
  rw [Nat.descFactorial_eq_prod_range, Nat.cast_prod]
  have hconst : (m : ℝ)^n = ∏ _k ∈ Finset.range n, (m : ℝ) := by simp
  rw [hconst, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro k hk
  have hk' := Finset.mem_range.mp hk
  rw [Nat.cast_sub (by omega : k ≤ m)]
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  field_simp

theorem falling_collision_bound {n m : ℕ} (hm : 0 < m) :
    1 - (m.descFactorial n : ℝ) / (m : ℝ)^n ≤ (n : ℝ) * (n - 1 : ℝ) / (2 * m) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  by_cases hnm : n ≤ m
  · have hb := prod_one_sub_lower (Finset.range n) (fun k => (k : ℝ) / m) (by
      intro k hk
      have hk' := Finset.mem_range.mp hk
      refine ⟨by positivity, ?_⟩
      apply (div_le_one hmR).mpr
      exact_mod_cast (show k ≤ m by omega))
    rw [falling_probability_product hnm hm]
    rw [← Finset.sum_div, sum_range_cast] at hb
    have he : (n : ℝ) * (n - 1 : ℝ) / 2 / m = (n : ℝ) * (n - 1 : ℝ) / (2 * m) := by ring
    rw [he] at hb
    linarith
  · have hmle : (m : ℝ) + 1 ≤ n := by exact_mod_cast (show m + 1 ≤ n by omega)
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hzero : m.descFactorial n = 0 := Nat.descFactorial_eq_zero_iff_lt.mpr (by omega)
    rw [hzero]
    norm_num
    apply (le_div_iff₀ (by positivity : 0 < (2 : ℝ) * m)).mpr
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ n - 2 by linarith) (show (0 : ℝ) ≤ n - 1 by linarith)]

/-- The collision-coupling bound, proved directly from the common mass
present in every permutation. This also covers `m < n`. -/
theorem periodic_total_variation_collision (hext : PPartitionExternal)
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    permutationL1Error n m / 2 ≤ 1 - (m.descFactorial n : ℝ) / (m : ℝ)^n := by
  let L := (List.finRange n).permutations'
  let A : ℝ := (m.choose n : ℝ) / (m : ℝ)^n
  let U : ℝ := 1 / (n.factorial : ℝ)
  let P := fun p => (patternProbability (periodicWord n m) p : ℝ)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have hAU : A ≤ U := by
    apply (div_le_div_iff₀ (by positivity) hfac).mpr
    have hh := Nat.descFactorial_le_pow m n
    rw [Nat.descFactorial_eq_factorial_mul_choose] at hh
    exact_mod_cast (by nlinarith : m.choose n * n.factorial ≤ 1 * m^n)
  have hAP (p : List (Fin n)) (hp : p ∈ L) : A ≤ P p := by
    have hperm := List.mem_permutations'.mp hp
    have hpnd := hperm.nodup_iff.mpr (List.nodup_finRange n)
    have hplen : p.length = n := by simpa using hperm.length_eq
    have hd : descents p < n := by
      have hne : p ≠ [] := by intro h; simp [h] at hplen; omega
      simpa [hplen] using descents_lt_length p hne
    dsimp [A, P]
    rw [periodic_probability_formula hext hn p hpnd hplen]
    push_cast
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast Nat.choose_le_choose n (show m ≤ m + n - 1 - descents p by omega)
  have hterm (p : List (Fin n)) (hp : p ∈ L) : |P p - U| ≤ P p + U - 2 * A := by
    apply abs_le.mpr
    constructor <;> linarith [hAP p hp]
  have hb := List.sum_le_sum hterm
  have hlen : L.length = n.factorial := by
    dsimp [L]
    rw [← (List.permutations_perm_permutations' _).length_eq, List.length_permutations]
    simp
  have hPsum : (L.map P).sum = 1 := by
    have hh := permutation_probability_sum (periodicWord n m) (List.finRange n)
      (List.nodup_finRange n) (fun a _ => by rw [periodicWord_multiplicity]; exact hm)
    have hreal := congrArg (fun q : ℚ => (q : ℝ)) hh
    simpa only [Rat.cast_list_sum, List.map_map, Function.comp_def, Rat.cast_one, L, P] using hreal
  have hsub (f g : List (Fin n) → ℝ) : (L.map (fun p => f p - g p)).sum =
      (L.map f).sum - (L.map g).sum := by
    induction L with
    | nil => simp
    | cons p L ih => simp only [List.map_cons, List.sum_cons, ih]; ring
  simp only [hsub, List.sum_map_add, hPsum, List.map_const', List.sum_replicate,
    hlen, nsmul_eq_mul] at hb
  have hU : (n.factorial : ℝ) * U = 1 := by dsimp [U]; field_simp
  have hA : (n.factorial : ℝ) * A = (m.descFactorial n : ℝ) / (m : ℝ)^n := by
    dsimp [A]
    rw [Nat.descFactorial_eq_factorial_mul_choose]
    push_cast
    ring
  change (L.map (fun p => |P p - U|)).sum / 2 ≤ _
  nlinarith

theorem periodic_total_variation_quadratic (hext : PPartitionExternal)
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    permutationL1Error n m / 2 ≤ (n : ℝ) * (n - 1 : ℝ) / (2 * m) :=
  (periodic_total_variation_collision hext hn hm).trans (falling_collision_bound hm)

end FairDice
