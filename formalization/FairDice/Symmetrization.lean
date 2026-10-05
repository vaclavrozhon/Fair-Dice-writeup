import FairDice.Concatenation

namespace FairDice

variable {α : Type*} [DecidableEq α]

/-- Separate occurrences lying wholly in one block from those crossing the
boundary. -/
theorem count_append_endpoints (p s t : List α) {k : ℕ} (hp : p.length = k + 1) :
    count p (s ++ t) = count p s + count p t +
      ∑ i ∈ Finset.range k, count (p.take (i + 1)) s * count (p.drop (i + 1)) t := by
  rw [count_append, hp, Finset.sum_range_succ']
  rw [Finset.sum_range_succ]
  simp [← hp, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

/-- For blocks fair through `k`, the difference of two `(k+1)`-pattern counts
is the sum of the differences within the individual blocks. This is stated
without subtraction, so all counts remain natural numbers. -/
theorem count_flatten_balance {k : ℕ} {ss : List (List α)}
    (hs : ∀ s ∈ ss, FairUpTo k s) (p q : List α) (hp : p.Nodup) (hq : q.Nodup)
    (hpl : p.length = k + 1) (hql : q.length = k + 1) :
    count p ss.flatten + (ss.map (count q)).sum =
      count q ss.flatten + (ss.map (count p)).sum := by
  induction ss with
  | nil =>
    have hp0 : p ≠ [] := by intro h; simp [h] at hpl
    have hq0 : q ≠ [] := by intro h; simp [h] at hql
    simp [count_empty_word, hp0, hq0]
  | cons s ss ih =>
    have hs₀ := hs s (by simp)
    have hss : ∀ t ∈ ss, FairUpTo k t := fun t ht => hs t (by simp [ht])
    have ht := fairUpTo_flatten hss
    have hcross :
        (∑ i ∈ Finset.range k, count (p.take (i + 1)) s *
          count (p.drop (i + 1)) ss.flatten) =
        ∑ i ∈ Finset.range k, count (q.take (i + 1)) s *
          count (q.drop (i + 1)) ss.flatten := by
      apply Finset.sum_congr rfl
      intro i hi
      have hik : i < k := Finset.mem_range.mp hi
      congr 1
      · apply hs₀ (i + 1) (by omega) _ _ hp.take hq.take
        · simp [hpl, Nat.min_eq_left (show i + 1 ≤ k + 1 by omega)]
        · simp [hql, Nat.min_eq_left (show i + 1 ≤ k + 1 by omega)]
      · apply ht (k - i) (Nat.sub_le _ _) _ _ hp.drop hq.drop
        · simp [hpl]
        · simp [hql]
    simp only [List.flatten_cons, List.map_cons, List.sum_cons]
    rw [count_append_endpoints p s ss.flatten hpl,
      count_append_endpoints q s ss.flatten hql, hcross]
    have := ih hss
    omega

omit [DecidableEq α] in
/-- Any two injective patterns of equal length are related by a permutation
of the alphabet. -/
theorem exists_relabel (p q : List α) (hp : p.Nodup) (hq : q.Nodup)
    (hlen : p.length = q.length) : ∃ e : Equiv.Perm α, p.map e = q := by
  classical
  let f : Fin p.length → α := p.get
  let g : Fin p.length → α := fun i => q.get (Fin.cast hlen i)
  have hf : Function.Injective f := (List.nodup_iff_injective_get.mp hp)
  have hg : Function.Injective g := by
    intro i j hij
    have hij' := (List.nodup_iff_injective_get.mp hq) hij
    simpa using hij'
  obtain ⟨e, he⟩ := Equiv.Perm.exists_extending_pair f g hf hg
  refine ⟨e, ?_⟩
  apply List.ext_get (by simp [hlen])
  intro i hi₁ hi₂
  simpa [f, g] using he ⟨i, by simpa using hi₁⟩

variable [Fintype α]

/-- The sum of counts over all alphabet permutations is independent of the
particular injective pattern of a given length. -/
theorem sum_relabel_counts (s p q : List α) (hp : p.Nodup) (hq : q.Nodup)
    (hlen : p.length = q.length) :
    ∑ e : Equiv.Perm α, count p (s.map e) =
      ∑ e : Equiv.Perm α, count q (s.map e) := by
  classical
  obtain ⟨σ, hσ⟩ := exists_relabel p q hp hq hlen
  subst q
  apply Fintype.sum_equiv (Equiv.mulLeft σ)
  intro e
  change count p (s.map e) = count (p.map σ) (s.map (σ * e))
  rw [show s.map (σ * e) = (s.map e).map σ by simp [List.map_map]]
  exact (count_map σ σ.injective p (s.map e)).symm

/-- Concatenation over all alphabet permutations, in the chosen finite
enumeration order. -/
noncomputable def symmetrize (s : List α) : List α :=
  ((Finset.univ : Finset (Equiv.Perm α)).toList.map
    fun (e : Equiv.Perm α) => s.map e).flatten

/-- Lemma 2.7: one round of symmetrization increases the fairness order. -/
theorem fairUpTo_symmetrize {k : ℕ} {s : List α} (hs : FairUpTo k s) :
    FairUpTo (k + 1) (symmetrize s) := by
  classical
  let es := (Finset.univ : Finset (Equiv.Perm α)).toList
  let ss := es.map fun (e : Equiv.Perm α) => s.map e
  have hss : ∀ t ∈ ss, FairUpTo k t := by
    intro t ht
    obtain ⟨e, _, rfl⟩ := List.mem_map.mp ht
    exact fairUpTo_relabel e hs
  intro j hj
  by_cases hjk : j ≤ k
  · exact fairUpTo_flatten hss j hjk
  · have hj' : j = k + 1 := by omega
    subst j
    intro p q hp hq hpl hql
    have hb := count_flatten_balance hss p q hp hq hpl hql
    have heq : (ss.map (count p)).sum = (ss.map (count q)).sum := by
      simp only [ss, es, List.map_map, Function.comp_def,
        Finset.sum_map_toList]
      exact sum_relabel_counts s p q hp hq (hpl.trans hql.symm)
    change count p ss.flatten = count q ss.flatten
    omega

/-- The exact size increase in Lemma 2.7. -/
theorem length_symmetrize (s : List α) :
    (symmetrize s).length = s.length * (Fintype.card α).factorial := by
  classical
  simp [symmetrize, List.length_flatten, List.map_map, Function.comp_def,
    List.map_const', List.sum_replicate, Fintype.card_perm, Nat.mul_comm]

end FairDice
