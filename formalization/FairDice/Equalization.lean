import FairDice.Blowup

namespace FairDice

/-- A binomial-term proof of the weak product bound needed for equalization. -/
theorem length_mul_prod_le_sum_pow (l : List ℕ) : l.length * l.prod ≤ l.sum ^ l.length := by
  cases l with
  | nil => simp
  | cons a l =>
    have hp : l.prod ≤ l.sum^l.length :=
      List.prod_le_pow_card l l.sum (fun x hx => List.single_le_sum (fun _ _ => Nat.zero_le _) x hx)
    have hb : (l.length + 1) * a * l.sum^l.length ≤ (a + l.sum)^(l.length + 1) := by
      rw [add_pow]
      have h := Finset.single_le_sum (f := fun i =>
        a^i * l.sum^(l.length + 1 - i) * (l.length + 1).choose i)
        (fun _ _ => Nat.zero_le _) (show 1 ∈ Finset.range (l.length + 1 + 1) by simp)
      simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h
    simp only [List.length_cons, List.prod_cons, List.sum_cons]
    exact (show (l.length + 1) * (a * l.prod) ≤
      (l.length + 1) * a * l.sum^l.length by
        simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left ((l.length + 1) * a) hp).trans hb

variable {α : Type*} [DecidableEq α] [Fintype α]

theorem sum_multiplicities (s : List α) : ∑ a : α, s.count a = s.length := by
  classical
  induction s with
  | nil => simp
  | cons b s ih =>
    have hc (a : α) : (b :: s).count a = s.count a + if a = b then 1 else 0 := by
      simpa only [count_singleton, count_nil] using count_cons_cons a b [] s
    simp only [hc, Finset.sum_add_distrib]
    simp [ih]

theorem card_mul_face_product_le_length_pow (s : List α) :
    Fintype.card α * (∏ a : α, s.count a) ≤ s.length ^ Fintype.card α := by
  classical
  have h := length_mul_prod_le_sum_pow
    ((Finset.univ : Finset α).toList.map fun a => s.count a)
  simpa only [List.length_map, Finset.length_toList, Finset.card_univ,
    Finset.prod_map_toList, Finset.sum_map_toList, sum_multiplicities] using h

/-- Corollary 2.3: arbitrary fair dice can be equalized with total length at
most the original total length raised to the number of dice. -/
theorem equalize {s : List α} (hs : PermutationFair s) :
    ∃ t : List α, PermutationFair t ∧
      (∀ a, t.count a = ∏ b : α, s.count b) ∧ t.length ≤ s.length ^ Fintype.card α := by
  classical
  let w : α → ℕ := fun a => ∏ b ∈ (Finset.univ : Finset α).erase a, s.count b
  have hw : ∀ a, 0 < w a := by
    intro a
    exact Finset.prod_pos (fun b _ => List.count_pos_iff.mpr (hs.1 b))
  have hc : ∀ a, (blowup w s).count a = ∏ b : α, s.count b := by
    intro a
    rw [multiplicity_blowup]
    exact Finset.prod_erase_mul _ _ (Finset.mem_univ a)
  refine ⟨blowup w s, permutationFair_blowup hs w hw, hc, ?_⟩
  rw [← sum_multiplicities (blowup w s)]
  simp only [hc, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact card_mul_face_product_le_length_pow s

end FairDice
