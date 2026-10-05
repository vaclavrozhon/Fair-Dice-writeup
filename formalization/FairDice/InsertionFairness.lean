import FairDice.Insertion

namespace FairDice

variable {α : Type*} [DecidableEq α]

local instance instBEqOptionInsertionFairness : BEq (Option α) := instBEqOfDecidableEq

theorem repeatWord_multiplicity (s : List α) (N : ℕ) (a : α) :
    (repeatWord s N).count a = N * s.count a := by
  simp [repeatWord, List.count_flatten, List.map_replicate, List.sum_replicate]

theorem insertGaps_old_multiplicity (s : List α) (N : ℕ) (k : Fin (N + 1) → ℕ) (a : α) :
    (insertGaps s N k).count (some a) = N * s.count a := by
  have h := count_some [a] (insertGaps s N k)
  rw [insertGaps_old_letters] at h
  simpa [repeatWord_multiplicity] using h

theorem insertGaps_new_multiplicity (s : List α) (N : ℕ) (k : Fin (N + 1) → ℕ) :
    (insertGaps s N k).count none = ∑ i, k i := by
  simpa [markedCount] using markedCount_insertGaps s [] [] N k

omit [DecidableEq α] in
theorem list_eq_map_some {l : List (Option α)} (h : none ∉ l) :
    ∃ p : List α, l = p.map some := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons a l ih =>
    obtain ⟨p, hp⟩ := ih (fun hl => h (by simp [hl]))
    cases a with
    | none => exact False.elim (h (by simp))
    | some a => exact ⟨a :: p, by simp [hp]⟩

variable [Fintype α]

theorem repeatWord_partial_count {s : List α} (hs : PermutationFair s)
    (F : ℕ) (hF : ∀ a, s.count a = F) (p : List α) (hp : p.Nodup) (N : ℕ) :
    (count p (repeatWord s N) : ℚ) = ((N : ℚ) * F)^p.length / p.length.factorial := by
  cases N with
  | zero => cases p <;> simp
  | succ N =>
    have hrep := permutationFair_repeat hs N
    have hc := partial_count_product hrep p hp
    change p.length.factorial * count p (repeatWord s (N + 1)) =
      (p.map (fun a => (repeatWord s (N + 1)).count a)).prod at hc
    simp only [repeatWord_multiplicity, hF, List.map_const', List.prod_replicate] at hc
    have hc' : (p.length.factorial : ℚ) * count p (repeatWord s (N + 1)) =
        (((N + 1 : ℕ) : ℚ) * F)^p.length := by exact_mod_cast hc
    apply (eq_div_iff (by exact_mod_cast Nat.ne_of_gt (Nat.factorial_pos p.length))).mpr
    nlinarith

theorem full_pattern_split (l : List (Option α)) (hl : l.Nodup)
    (hlen : l.length = Fintype.card (Option α)) :
    ∃ p q : List α, l = p.map some ++ none :: q.map some ∧
      (p ++ q).Nodup ∧ p.length + q.length = Fintype.card α := by
  have hm := mem_full_pattern l hl hlen none
  obtain ⟨u, v, rfl⟩ := List.mem_iff_append.mp hm
  have hn := List.nodup_append.mp hl
  have hnv : none ∉ v := (List.nodup_cons.mp hn.2.1).1
  have hnu : none ∉ u := by
    intro hnu
    exact hn.2.2 none hnu none (by simp) rfl
  obtain ⟨p, rfl⟩ := list_eq_map_some hnu
  obtain ⟨q, rfl⟩ := list_eq_map_some hnv
  refine ⟨p, q, rfl, ?_, ?_⟩
  · have hsub : (p.map some ++ q.map some).Sublist (p.map some ++ none :: q.map some) :=
      (List.sublist_cons_self none (q.map some)).append_left (p.map some)
    have hnod := hl.sublist hsub
    rw [← List.map_append] at hnod
    exact List.Nodup.of_map some hnod
  · simp only [List.length_append, List.length_cons, List.length_map, Fintype.card_option] at hlen
    omega

/-- Insertion criterion in unnormalized moment form. The subsequent Bernstein
identity translates this directly to Lemma 3.1. -/
theorem insertion_fair_of_moments {s : List α} (hs : PermutationFair s)
    (F : ℕ) (hF : ∀ a, s.count a = F) (N : ℕ) (hN : 0 < N)
    (k : Fin (N + 1) → ℕ) (hk : 0 < ∑ i, k i) (C : ℚ)
    (hm : ∀ j ≤ Fintype.card α,
      ∑ i : Fin (N + 1), (k i : ℚ) * (i.val : ℚ)^j * (N - i.val : ℚ)^(Fintype.card α - j) /
        ((j.factorial : ℚ) * (Fintype.card α - j).factorial) = C) :
    PermutationFair (insertGaps s N k) := by
  constructor
  · intro a
    apply List.count_pos_iff.mp
    cases a with
    | none => simpa [insertGaps_new_multiplicity] using hk
    | some a =>
      rw [insertGaps_old_multiplicity]
      exact Nat.mul_pos hN (List.count_pos_iff.mpr (hs.1 a))
  · have hcount (l : List (Option α)) (hl : l.Nodup)
        (hlen : l.length = Fintype.card (Option α)) :
        (count l (insertGaps s N k) : ℚ) = (F : ℚ)^(Fintype.card α) * C := by
      obtain ⟨p, q, rfl, hpq, hlenpq⟩ := full_pattern_split l hl hlen
      have hp := (List.nodup_append.mp hpq).1
      have hq := (List.nodup_append.mp hpq).2.1
      have hqLen : q.length = Fintype.card α - p.length := by omega
      change (markedCount p q (insertGaps s N k) : ℚ) = _
      rw [markedCount_insertGaps, Nat.cast_sum]
      simp only [Nat.cast_mul, repeatWord_partial_count hs F hF p hp,
        repeatWord_partial_count hs F hF q hq]
      rw [← hm p.length (by omega), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      have hiN : i.val ≤ N := by omega
      rw [Nat.cast_sub hiN]
      have hpow : (F : ℚ)^p.length * (F : ℚ)^q.length = (F : ℚ)^(Fintype.card α) := by
        rw [← pow_add, hlenpq]
      rw [← hpow, ← hqLen]
      simp only [mul_pow]
      ring
    intro p q hp hq hpl hql
    exact_mod_cast (hcount p hp hpl).trans (hcount q hq hql).symm

theorem repeatWord_partial_count_general {s : List α} (hs : PermutationFair s)
    (p : List α) (hp : p.Nodup) (N : ℕ) :
    (count p (repeatWord s N) : ℚ) = (N : ℚ)^p.length *
      ((p.map (fun a => s.count a)).prod : ℚ) / p.length.factorial := by
  cases N with
  | zero => cases p <;> simp
  | succ N =>
    have hrep := permutationFair_repeat hs N
    have hc := partial_count_product hrep p hp
    change p.length.factorial * count p (repeatWord s (N + 1)) =
      (p.map (fun a => (repeatWord s (N + 1)).count a)).prod at hc
    simp only [repeatWord_multiplicity, List.prod_map_mul, List.map_const', List.prod_replicate] at hc
    have hc' : (p.length.factorial : ℚ) * count p (repeatWord s (N + 1)) =
        (((N + 1 : ℕ) : ℚ)^p.length) * ((p.map (fun a => s.count a)).prod : ℚ) := by
      exact_mod_cast hc
    apply (eq_div_iff (by exact_mod_cast Nat.ne_of_gt (Nat.factorial_pos p.length))).mpr
    nlinarith

theorem full_pattern_face_product {s p : List α} (hp : p.Nodup)
    (hlen : p.length = Fintype.card α) :
    (p.map (fun a => s.count a)).prod = ∏ a : α, s.count a := by
  classical
  have hperm := full_patterns_perm p (Finset.univ : Finset α).toList hp
    (Finset.nodup_toList _) hlen (by simp)
  simpa only [Finset.prod_map_toList] using (hperm.map (fun a => s.count a)).prod_eq

/-- The same insertion criterion works for arbitrary unequal-sided old dice.
This is the combinatorial input to the rational-design proposition. -/
theorem insertion_fair_general {s : List α} (hs : PermutationFair s)
    (N : ℕ) (hN : 0 < N) (k : Fin (N + 1) → ℕ) (hk : 0 < ∑ i, k i) (C : ℚ)
    (hm : ∀ j ≤ Fintype.card α,
      ∑ i : Fin (N + 1), (k i : ℚ) * (i.val : ℚ)^j * (N - i.val : ℚ)^(Fintype.card α - j) /
        ((j.factorial : ℚ) * (Fintype.card α - j).factorial) = C) :
    PermutationFair (insertGaps s N k) := by
  constructor
  · intro a
    apply List.count_pos_iff.mp
    cases a with
    | none => simpa [insertGaps_new_multiplicity] using hk
    | some a =>
      rw [insertGaps_old_multiplicity]
      exact Nat.mul_pos hN (List.count_pos_iff.mpr (hs.1 a))
  · have hcount (l : List (Option α)) (hl : l.Nodup)
        (hlen : l.length = Fintype.card (Option α)) :
        (count l (insertGaps s N k) : ℚ) = ((∏ a : α, s.count a : ℕ) : ℚ) * C := by
      obtain ⟨p, q, rfl, hpq, hlenpq⟩ := full_pattern_split l hl hlen
      have hp := (List.nodup_append.mp hpq).1
      have hq := (List.nodup_append.mp hpq).2.1
      have hqLen : q.length = Fintype.card α - p.length := by omega
      change (markedCount p q (insertGaps s N k) : ℚ) = _
      rw [markedCount_insertGaps, Nat.cast_sum]
      simp only [Nat.cast_mul, repeatWord_partial_count_general hs p hp,
        repeatWord_partial_count_general hs q hq]
      have hprod : ((p.map (fun a => s.count a)).prod : ℚ) *
          ((q.map (fun a => s.count a)).prod : ℚ) = (∏ a : α, s.count a : ℕ) := by
        have heq := full_pattern_face_product (s := s) hpq (by simpa using hlenpq)
        simpa only [List.map_append, List.prod_append, Nat.cast_mul] using
          congrArg (fun t : ℕ => (t : ℚ)) heq
      rw [← hm p.length (by omega), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      have hiN : i.val ≤ N := by omega
      rw [Nat.cast_sub hiN, ← hprod, ← hqLen]
      ring
    intro p q hp hq hpl hql
    exact_mod_cast (hcount p hp hpl).trans (hcount q hq hql).symm

end FairDice
