import FairDice.GoFirst
import FairDice.Restriction

namespace FairDice

variable {α : Type*} [DecidableEq α] [Fintype α]

local instance instBEqSubtypeHereditary (A : Finset α) : BEq A := instBEqOfDecidableEq

def HereditaryGoFirstFair (s : List α) : Prop :=
  ∀ A : Finset α, A.Nonempty → GoFirstFair (restrict A s)

theorem goFirst_card_dvd [Nonempty α] {s : List α} (hs : GoFirstFair s) :
    Fintype.card α ∣ outcomeCount s := by
  obtain ⟨a⟩ := ‹Nonempty α›
  refine ⟨winCount a s, ?_⟩
  rw [← sum_winCount]
  have hc : ∀ b : α, winCount b s = winCount a s := fun b => hs.2 b a
  simp [hc]

omit [Fintype α] in
theorem hereditary_subset_card_dvd {s : List α} (hs : HereditaryGoFirstFair s)
    (A : Finset α) (hA : A.Nonempty) : A.card ∣ ∏ a ∈ A, s.count a := by
  classical
  letI : Nonempty A := ⟨⟨hA.choose, hA.choose_spec⟩⟩
  have h := goFirst_card_dvd (hs A hA)
  have hc (a : A) : (restrict A s).count a = s.count a.val := by
    simpa using count_restrict A [a] s
  simp only [Fintype.card_coe, outcomeCount, hc] at h
  have hprod : (∏ a : A, s.count a.val) = ∏ a ∈ A, s.count a := by
    exact Finset.prod_coe_sort A (fun a : α => s.count a)
  rwa [hprod] at h

/-- The prime-subset argument applies to hereditary go-first fairness even
though it does not force factorial divisibility. -/
theorem hereditary_few_not_dvd {s : List α} (hs : HereditaryGoFirstFair s)
    (p : ℕ) (hp : p.Prime) :
    ((Finset.univ : Finset α).filter (fun a => ¬p ∣ s.count a)).card < p := by
  classical
  by_contra h
  obtain ⟨A, hA, hcard⟩ := Finset.exists_subset_card_eq (Nat.le_of_not_gt h)
  have hp0 := hp.pos
  have hd := hereditary_subset_card_dvd hs A (Finset.card_pos.mp (by omega))
  rw [hcard] at hd
  obtain ⟨a, ha, hpa⟩ := (hp.prime.dvd_finsetProd_iff _).mp hd
  exact (Finset.mem_filter.mp (hA ha)).2 hpa

omit [Fintype α] in
theorem hereditary_positive {s : List α} (hs : HereditaryGoFirstFair s) (a : α) :
    0 < s.count a := by
  have hh := hs {a} (Finset.singleton_nonempty a)
  have hc := count_restrict {a} [⟨a, Finset.mem_singleton_self a⟩] s
  simp only [List.map_cons, List.map_nil, count_singleton] at hc
  have hpos := List.count_pos_iff.mpr (hh.1 ⟨a, Finset.mem_singleton_self a⟩)
  rwa [hc] at hpos

/-- Equation (5.3), the full finite product before using the cited primorial
asymptotics. -/
theorem hereditary_prime_product {s : List α} (hs : HereditaryGoFirstFair s) :
    (∏ p ∈ (Finset.range (Fintype.card α + 1)).filter Nat.Prime,
      p^(Fintype.card α + 1 - p)) ≤ outcomeCount s := by
  classical
  let P := (Finset.range (Fintype.card α + 1)).filter Nat.Prime
  have hcard (p : ℕ) (hp : p ∈ P) : Fintype.card α + 1 - p ≤
      ((Finset.univ : Finset α).filter (fun a => p ∣ s.count a)).card := by
    have hsmall := hereditary_few_not_dvd hs p (Finset.mem_filter.mp hp).2
    have hpart := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset α)) (fun a => p ∣ s.count a)
    simp only [Finset.card_univ] at hpart
    omega
  calc
    _ ≤ ∏ p ∈ P, p^((Finset.univ : Finset α).filter (fun a => p ∣ s.count a)).card := by
      apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
      intro p hp
      exact Nat.pow_le_pow_right (Finset.mem_filter.mp hp).2.pos (hcard p hp)
    _ = ∏ p ∈ P, ∏ a : α, if p ∣ s.count a then p else 1 := by
      apply Finset.prod_congr rfl
      intro p _
      simp [Finset.prod_ite]
    _ = ∏ a : α, ∏ p ∈ P, if p ∣ s.count a then p else 1 := Finset.prod_comm
    _ ≤ outcomeCount s := by
      apply Finset.prod_le_prod (fun _ _ => Nat.zero_le _)
      intro a _
      have hd : (∏ p ∈ P.filter (fun p => p ∣ s.count a), p) ∣ s.count a := by
        apply Finset.prod_primes_dvd
        · intro p hp
          exact (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.prime
        · intro p hp
          exact (Finset.mem_filter.mp hp).2
      simpa only [Finset.prod_filter] using Nat.le_of_dvd (hereditary_positive hs a) hd

end FairDice
