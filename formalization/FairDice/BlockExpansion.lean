import FairDice.Concatenation
import FairDice.PalindromeBlocks

namespace FairDice

variable {α : Type*} [DecidableEq α]

/-- All ways to cut a prescribed pattern into `m` consecutive segments,
including empty segments. Each cut is counted once. -/
def patternCuts (p : List α) : ℕ → List (List (List α))
  | 0 => if p = [] then [[]] else []
  | m+1 => (List.range (p.length+1)).flatMap (fun k =>
      (patternCuts (p.drop k) m).map (fun ps => p.take k :: ps))

omit [DecidableEq α] in
theorem patternCuts_length_flatten (p : List α) (m : ℕ)
    (ps : List (List α)) (hps : ps ∈ patternCuts p m) :
    ps.length = m ∧ ps.flatten = p := by
  induction m generalizing p ps with
  | zero =>
    by_cases hp : p = []
    · simp [patternCuts, hp] at hps
      subst ps
      simp [hp]
    · simp [patternCuts, hp] at hps
  | succ m ih =>
    obtain ⟨k, hk, hps⟩ := List.mem_flatMap.mp hps
    obtain ⟨qs, hqs, rfl⟩ := List.mem_map.mp hps
    obtain ⟨hlen, hflat⟩ := ih _ _ hqs
    simp [hlen, hflat]

/-- Iterating the two-block counting identity gives the occupancy
expansion for an actual finite word, before normalization. -/
theorem count_blocks (p : List α) (ss : List (List α)) :
    count p ss.flatten =
      ((patternCuts p ss.length).map (fun ps => (List.zipWith count ps ss).prod)).sum := by
  induction ss generalizing p with
  | nil => cases p <;> simp [patternCuts]
  | cons s ss ih =>
    rw [List.flatten_cons, count_append]
    simp only [List.length_cons, patternCuts, List.map_flatMap,
      List.map_map, Function.comp_def, List.zipWith_cons_cons,
      List.prod_cons]
    simp only [List.flatMap_def, List.sum_flatten, List.map_map, Function.comp_def]
    rw [← List.sum_toFinset _ List.nodup_range]
    simp only [List.toFinset_range]
    apply Finset.sum_congr rfl
    intro k hk
    rw [List.sum_map_mul_left, ← ih]

/-- The product of normalized block contributions has a common denominator
`2` to the total segment length. -/
theorem palindrome_product_identity (ss ps : List (List α)) (hlen : ps.length = ss.length) :
    (List.zipWith (fun p s => 1 + palindromeDelta s p) ps ss).prod =
      ((ps.map (fun p => (p.length.factorial : ℝ))).prod *
        (List.zipWith (fun p s => (count p (s ++ s.reverse) : ℝ)) ps ss).prod) /
          2^(ps.map List.length).sum := by
  induction ps generalizing ss with
  | nil => cases ss <;> simp_all
  | cons p ps ih =>
    cases ss with
    | nil => simp at hlen
    | cons s ss =>
      have hl : ps.length = ss.length := by simpa using hlen
      simp only [List.zipWith_cons_cons, List.prod_cons, List.map_cons, List.sum_cons]
      rw [ih ss hl]
      simp only [palindromeDelta, pow_add]
      ring

private theorem sum_map_div_list {β : Type*} (xs : List β) (f : β → ℝ) (a : ℝ) :
    (xs.map (fun x => f x / a)).sum = (xs.map f).sum / a := by
  simp [div_eq_mul_inv, List.sum_map_mul_right]

/-- Exact expansion `eq:palindrome-expansion`. The coefficients are the
multinomial occupancy masses `n!/(m^n ∏ k_i!)`, evaluated on consecutive cuts.
This theorem requires no probabilistic inequality. -/
theorem palindrome_occupancy_expansion (p : List α) (ss : List (List α)) :
    (p.length.factorial : ℝ) *
      (count p (ss.map (fun s => s ++ s.reverse)).flatten : ℝ) /
        (2 * (ss.length : ℝ))^p.length =
    ((patternCuts p ss.length).map (fun ps =>
      ((p.length.factorial : ℝ) /
        ((ss.length : ℝ)^p.length * (ps.map (fun p => (p.length.factorial : ℝ))).prod)) *
          (List.zipWith (fun p s => 1 + palindromeDelta s p) ps ss).prod)).sum := by
  rw [count_blocks]
  simp only [List.length_map, Nat.cast_list_sum, List.map_map, Function.comp_def]
  rw [← List.sum_map_mul_left, ← sum_map_div_list]
  apply congrArg List.sum
  apply List.map_congr_left
  intro ps hps
  obtain ⟨hlen, hflat⟩ := patternCuts_length_flatten p ss.length ps hps
  have htotal : (ps.map List.length).sum = p.length := by
    rw [← List.length_flatten, hflat]
  have hfac : (ps.map (fun p => (p.length.factorial : ℝ))).prod ≠ 0 := by
    apply ne_of_gt
    apply List.prod_pos
    intro x hx
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
    exact_mod_cast Nat.factorial_pos q.length
  rw [palindrome_product_identity ss ps hlen, htotal]
  have hz :
      (List.zipWith count ps (ss.map (fun s => s ++ s.reverse))).prod =
        (List.zipWith (fun p s => count p (s ++ s.reverse)) ps ss).prod := by
    congr 1
    exact List.zipWith_map_right
  rw [hz]
  have hcast : ((List.zipWith (fun p s => count p (s ++ s.reverse)) ps ss).prod : ℝ) =
      (List.zipWith (fun p s => (count p (s ++ s.reverse) : ℝ)) ps ss).prod := by
    rw [Nat.cast_list_prod]
    congr 1
    exact List.map_zipWith
  rw [hcast, mul_pow]
  field_simp

noncomputable def cutReciprocal (ps : List (List α)) : ℝ :=
  1 / (ps.map (fun p => (p.length.factorial : ℝ))).prod

omit [DecidableEq α] in
theorem cutReciprocal_cons (p : List α) (ps : List (List α)) :
    cutReciprocal (p :: ps) = (1 / (p.length.factorial : ℝ)) * cutReciprocal ps := by
  simp [cutReciprocal, div_eq_mul_inv, mul_comm]

omit [DecidableEq α] in
/-- The normalization of the cut weights is the multinomial theorem. -/
theorem cutReciprocal_sum (p : List α) (m : ℕ) :
    ((patternCuts p m).map cutReciprocal).sum = (m : ℝ)^p.length / p.length.factorial := by
  induction m generalizing p with
  | zero => cases p <;> simp [patternCuts, cutReciprocal]
  | succ m ih =>
    simp only [patternCuts, List.map_flatMap, List.map_map, Function.comp_def,
      cutReciprocal_cons]
    simp only [List.flatMap_def, List.sum_flatten, List.map_map, Function.comp_def]
    simp_rw [List.sum_map_mul_left, ih, List.length_drop]
    rw [← List.sum_toFinset _ List.nodup_range]
    simp only [List.toFinset_range, Nat.cast_add, Nat.cast_one]
    have hbin := add_pow (1 : ℝ) (m : ℝ) p.length
    simp only [one_pow, one_mul] at hbin
    rw [add_comm 1 (m : ℝ)] at hbin
    rw [hbin, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k hk
    have hkn : k ≤ p.length := by have := Finset.mem_range.mp hk; omega
    rw [List.length_take, Nat.min_eq_left hkn, Nat.cast_choose ℝ hkn]
    have hfac : (p.length.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (Nat.factorial_pos _)
    field_simp

/-- The exact coefficients in the palindrome cut expansion sum to one
when at least one block is present. -/
theorem palindrome_occupancy_weights_sum (p : List α) (m : ℕ) (hm : 0 < m) :
    ((patternCuts p m).map (fun ps => (p.length.factorial : ℝ) /
      ((m : ℝ)^p.length * (ps.map (fun p => (p.length.factorial : ℝ))).prod))).sum = 1 := by
  have he (ps : List (List α)) : (p.length.factorial : ℝ) /
      ((m : ℝ)^p.length * (ps.map (fun p => (p.length.factorial : ℝ))).prod) =
        ((p.length.factorial : ℝ)/(m : ℝ)^p.length) * cutReciprocal ps := by
    unfold cutReciprocal
    ring
  simp_rw [he]
  rw [List.sum_map_mul_left, cutReciprocal_sum]
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hm
  have hf : (p.length.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (Nat.factorial_pos _)
  field_simp

end FairDice
