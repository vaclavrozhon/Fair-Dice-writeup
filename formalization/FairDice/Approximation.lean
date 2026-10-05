import FairDice.ShuffleBounds
import FairDice.Insertion

namespace FairDice

def periodicWord (n m : ℕ) : List (Fin n) := repeatWord (List.finRange n) m

def descents {n : ℕ} : List (Fin n) → ℕ
  | [] => 0
  | [_] => 0
  | a :: b :: p => (if b < a then 1 else 0) + descents (b :: p)

theorem descents_lt_length {n : ℕ} (p : List (Fin n)) (hp : p ≠ []) :
    descents p < p.length := by
  induction p using descents.induct with
  | case1 => contradiction
  | case2 a => simp [descents]
  | case3 a b p ih =>
    have h := ih (by simp)
    simp only [List.length_cons] at h
    simp only [descents, List.length_cons]
    split <;> omega

/-- Stanley's cited P-partition enumeration, specialized to the natural
labeling of a chain. It is an explicit external input, not a Lean axiom.
The subsequence count on the left counts increasing choices of word positions. -/
def PPartitionExternal : Prop :=
  ∀ n m : ℕ, 0 < n → ∀ p : List (Fin n), p.Nodup → p.length = n →
    count p (periodicWord n m) = (m + n - 1 - descents p).choose n

theorem periodicWord_multiplicity (n m : ℕ) (a : Fin n) :
    (periodicWord n m).count a = m := by
  simp [periodicWord, repeatWord, List.count_flatten, List.map_replicate,
    List.count_eq_one_of_mem (List.nodup_finRange n) (List.mem_finRange a)]

theorem periodicWord_length (n m : ℕ) : (periodicWord n m).length = n * m := by
  simp [periodicWord, repeatWord, List.length_flatten, Nat.mul_comm]

theorem periodic_probability_formula (hext : PPartitionExternal) {n m : ℕ}
    (hn : 0 < n) (p : List (Fin n)) (hp : p.Nodup) (hlen : p.length = n) :
    patternProbability (periodicWord n m) p =
      ((m + n - 1 - descents p).choose n : ℚ) / (m : ℚ)^n := by
  unfold patternProbability
  rw [hext n m hn p hp hlen]
  simp [periodicWord_multiplicity, List.map_const', List.prod_replicate, hlen]

/-- Theorem 5.4, including the explicit number of faces of the constructed
word. The only external premise is the classical exact counting formula. -/
theorem approximate_permutation_fairness (hext : PPartitionExternal)
    {n m : ℕ} (hn : 2 ≤ n) (hm : 0 < m) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hsize : (n : ℝ) * (n - 1 : ℝ) / ε ≤ m)
    (p : List (Fin n)) (hp : p.Nodup) (hlen : p.length = n) :
    |(patternProbability (periodicWord n m) p : ℝ) - 1 / (n.factorial : ℝ)| ≤
      ε / (n.factorial : ℝ) := by
  have hn0 : 0 < n := by omega
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hnm : n ≤ m := by
    have hs := (div_le_iff₀ hε).mp hsize
    have hmul := mul_le_mul_of_nonneg_left hε1 hmR.le
    have : (n : ℝ) ≤ m := by nlinarith
    exact_mod_cast this
  have hd : descents p < n := by
    have hne : p ≠ [] := by intro h; simp [h] at hlen; omega
    simpa only [hlen] using descents_lt_length p hne
  have hb := shuffleRatio_bounds hn hm hd hε hε1 hsize
  have hr : (n.factorial : ℝ) * (patternProbability (periodicWord n m) p : ℝ) =
      shuffleRatio n m (descents p) := by
    rw [periodic_probability_formula hext hn0 p hp hlen]
    push_cast
    rw [← mul_div_assoc]
    exact choose_eq_shuffleRatio hn0 hnm hd
  have hfac : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  rw [abs_le]
  constructor
  · have hbl : (1 - ε) / (n.factorial : ℝ) ≤
        (patternProbability (periodicWord n m) p : ℝ) := by
      apply (div_le_iff₀ hfac).mpr
      nlinarith [hb.1]
    rw [sub_div] at hbl
    linarith
  · apply (sub_le_iff_le_add).mpr
    rw [← add_div]
    apply (le_div_iff₀ hfac).mpr
    nlinarith [hb.2]

/-- Sum of absolute errors over the permutation sample space. -/
noncomputable def permutationL1Error (n m : ℕ) : ℝ :=
  (((List.finRange n).permutations').map (fun p =>
    |(patternProbability (periodicWord n m) p : ℝ) - 1 / (n.factorial : ℝ)|)).sum

theorem approximate_l1 (hext : PPartitionExternal) {n m : ℕ}
    (hn : 2 ≤ n) (hm : 0 < m) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hsize : (n : ℝ) * (n - 1 : ℝ) / ε ≤ m) :
    permutationL1Error n m ≤ ε := by
  have hterm (p : List (Fin n)) (hp : p ∈ (List.finRange n).permutations') :
      |(patternProbability (periodicWord n m) p : ℝ) - 1 / (n.factorial : ℝ)| ≤
        ε / (n.factorial : ℝ) := by
    have hperm := List.mem_permutations'.mp hp
    apply approximate_permutation_fairness hext hn hm hε hε1 hsize p
    · exact hperm.nodup_iff.mpr (List.nodup_finRange n)
    · simpa using hperm.length_eq
  have hb := List.sum_le_sum hterm
  have hlen : (List.finRange n).permutations'.length = n.factorial := by
    rw [← (List.permutations_perm_permutations' _).length_eq, List.length_permutations]
    simp
  have hcancel : (n.factorial : ℝ) * (ε / (n.factorial : ℝ)) = ε := by
    field_simp
  simpa [permutationL1Error, List.map_const', List.sum_replicate, hlen,
    nsmul_eq_mul, hcancel] using hb

theorem approximate_total_variation (hext : PPartitionExternal) {n m : ℕ}
    (hn : 2 ≤ n) (hm : 0 < m) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hsize : (n : ℝ) * (n - 1 : ℝ) / ε ≤ m) :
    permutationL1Error n m / 2 ≤ ε / 2 := by
  exact div_le_div_of_nonneg_right (approximate_l1 hext hn hm hε hε1 hsize) (by norm_num)

end FairDice
