import FairDice.ConstantCells
import FairDice.FiniteCells

namespace FairDice

variable {α : Type*} [DecidableEq α]

noncomputable def normalizedCount (N : ℕ) (p s : List α) : ℝ :=
  (count p s : ℝ)/(N : ℝ)^p.length

theorem normalizedCount_append (N : ℕ) (_hN : 0 < N) (p s t : List α) :
    normalizedCount N p (s++t)=
      ∑ k ∈ Finset.range (p.length+1),
        normalizedCount N (p.take k) s*normalizedCount N (p.drop k) t := by
  unfold normalizedCount
  rw [count_append,Nat.cast_sum,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  have hl : (p.take k).length+(p.drop k).length=p.length := by
    rw [← List.length_append,List.take_append_drop]
  rw [Nat.cast_mul,← hl,pow_add]
  ring

theorem normalizedCount_reverse (N : ℕ) (p s : List α) :
    normalizedCount N p s.reverse=normalizedCount N p.reverse s := by
  simp only [normalizedCount,count_reverse,List.length_reverse]

def cellWord (blocks : ℕ → List α) (n : ℕ) : List α := (List.range n).flatMap blocks

omit [DecidableEq α] in
theorem cellWord_succ (blocks : ℕ → List α) (n : ℕ) :
    cellWord blocks (n+1)=cellWord blocks n++blocks n := by
  simp [cellWord,List.range_succ]

/-- Literal counts in the first cells agree with the iterated Lebesgue
integral whenever all within-cell partial orders have the right masses. -/
theorem cellWord_integral (f : α → ℝ → ℝ)
    (hf : ∀ i, MeasureTheory.LocallyIntegrable (f i) MeasureTheory.volume)
    (point : ℕ → ℝ) (blocks : ℕ → List α) (N : ℕ) (hN : 0 < N)
    (n : ℕ) (hcell : ∀ g < n, ∀ p : List α, p.Nodup →
      normalizedCount N p (blocks g).reverse=densityPrefixFrom f (point g) p (point (g+1)))
    (p : List α) (hp : p.Nodup) :
    normalizedCount N p (cellWord blocks n).reverse=densityPrefixFrom f (point 0) p (point n) := by
  induction n generalizing p with
  | zero => cases p <;> simp [cellWord,normalizedCount,densityPrefixFrom]
  | succ n ih =>
    rw [cellWord_succ,List.reverse_append,normalizedCount_append N hN,
      densityPrefixFrom_split f hf p (point 0) (point n) (point (n+1))]
    apply Finset.sum_congr rfl
    intro k _
    rw [hcell n (by omega) (p.take k) hp.take,
      ih (fun g hg => hcell g (by omega)) (p.drop k) hp.drop]
    ring

end FairDice
