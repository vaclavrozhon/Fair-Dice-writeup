import FairDice.RationalGrid
import FairDice.CellCounts

namespace FairDice

open MeasureTheory Set

variable {α : Type*} [DecidableEq α] {K : ℕ}

theorem gridPoint_width {G : ℕ} (_hG : 0 < G) (g : ℕ) :
    gridPoint G (g+1)-gridPoint G g=1/(G : ℝ) := by
  simp only [gridPoint,Nat.cast_add,Nat.cast_one]
  ring

omit [DecidableEq α] in
theorem gridCell_integral (f : α → ℝ → ℝ) (mass : α → ℝ)
    {G : ℕ} (hG : 0 < G) (g : ℕ)
    (hf : ∀ i x, x ∈ Ioo (gridPoint G g) (gridPoint G (g+1)) → f i x=(G : ℝ)*mass i)
    (p : List α) :
    densityPrefixFrom f (gridPoint G g) p (gridPoint G (g+1))=
      (p.map mass).prod/(p.length.factorial : ℝ) := by
  rw [densityPrefixFrom_constant f (fun i => (G : ℝ)*mass i) _ _ hf p
    (gridPoint_strict hG (by omega)).le,gridPoint_width hG]
  have hp : (p.map (fun i => (G : ℝ)*mass i)).prod=
      (G : ℝ)^p.length*(p.map mass).prod := by
    simp [List.prod_map_mul,List.map_const']
  rw [hp]
  have hh : (1/(G : ℝ))^p.length*(G : ℝ)^p.length=1 := by
    rw [← mul_pow,one_div_mul_cancel (by exact_mod_cast Nat.ne_of_gt hG),one_pow]
  rw [← mul_assoc,hh,one_mul]

def extendBlocks {G : ℕ} (blocks : Fin G → List α) (g : ℕ) : List α :=
  if hg : g < G then blocks ⟨g,hg⟩ else []

theorem grid_blocks_prefix_suffix (f : α → ℝ → ℝ)
    (hf : ∀ i, LocallyIntegrable (f i) volume)
    (hrf : ∀ i, LocallyIntegrable (fun x => f i (1-x)) volume)
    (u : Fin K → ℝ) (M : UniformGridModel α K f u) (blocks : Fin M.G → List α)
    (N : ℕ) (hN : 0 < N)
    (hprob : ∀ g p, p.Nodup → normalizedCount N p (blocks g)=
      ((p.map (fun i => (M.mass i g : ℝ))).prod)/(p.length.factorial : ℝ)) :
    let bs := (List.range M.G).map (extendBlocks blocks)
    ∀ j ≤ M.G, ∀ p : List α, p.Nodup →
      normalizedCount N p (bs.take j).flatten=densityPrefix f p.reverse (gridPoint M.G j) ∧
      normalizedCount N p (bs.drop j).flatten=
        densityPrefix (fun i x => f i (1-x)) p (1-gridPoint M.G j) := by
  dsimp only
  let B := extendBlocks blocks
  let bs := (List.range M.G).map B
  have hB (g : ℕ) (hg : g < M.G) : B g=blocks ⟨g,hg⟩ := by simp [B,extendBlocks,hg]
  have hcell (g : ℕ) (hg : g < M.G) (p : List α) (hp : p.Nodup) :
      normalizedCount N p (B g).reverse=
        densityPrefixFrom f (gridPoint M.G g) p (gridPoint M.G (g+1)) := by
    rw [hB g hg,normalizedCount_reverse,hprob _ p.reverse (List.nodup_reverse.mpr hp)]
    rw [gridCell_integral f (fun i => (M.mass i ⟨g,hg⟩ : ℝ)) M.positive_grid g
      (fun i x hx => M.cell_density i ⟨g,hg⟩ x hx) p]
    simp [List.map_reverse]
  have hrcell (g : ℕ) (hg : g < M.G) (p : List α) (hp : p.Nodup) :
      normalizedCount N p ((B (M.G-1-g)).reverse).reverse=
        densityPrefixFrom (fun i x => f i (1-x)) (gridPoint M.G g) p (gridPoint M.G (g+1)) := by
    have hr : M.G-1-g < M.G := by omega
    rw [List.reverse_reverse,hB _ hr,hprob _ p hp]
    symm
    apply gridCell_integral _ (fun i => (M.mass i ⟨M.G-1-g,hr⟩ : ℝ)) M.positive_grid g
    intro i x hx
    apply M.cell_density i ⟨M.G-1-g,hr⟩ (1-x)
    have hGr : (0 : ℝ) < M.G := by exact_mod_cast M.positive_grid
    have hnv : ((M.G-1-g : ℕ) : ℝ)=(M.G : ℝ)-1-g := by
      rw [Nat.cast_sub (by omega),Nat.cast_sub (by omega),Nat.cast_one]
    dsimp only [gridPoint] at hx ⊢
    rw [hnv]
    push_cast
    constructor
    · apply (div_lt_iff₀ hGr).mpr
      have hh := (lt_div_iff₀ hGr).mp hx.2
      push_cast at hh
      nlinarith
    · apply (lt_div_iff₀ hGr).mpr
      have hh := (div_lt_iff₀ hGr).mp hx.1
      nlinarith
  intro j hj p hp
  have hprefix : (bs.take j).flatten=cellWord B j := by
    simp only [bs,← List.map_take,List.take_range,Nat.min_eq_left hj,cellWord,List.flatMap_def]
  have hsuffix : ((bs.drop j).flatten).reverse=
      cellWord (fun g => (B (M.G-1-g)).reverse) (M.G-j) := by
    have hjG : j+(M.G-j)=M.G := Nat.add_sub_of_le hj
    have hdrop : (List.range M.G).drop j=List.range' j (M.G-j) := by
      rw [List.range_eq_range',List.drop_range']
      simp
    simp only [bs,← List.map_drop,hdrop,List.reverse_flatten,← List.map_reverse,
      List.reverse_range',hjG,cellWord,List.flatMap_def,List.map_map,Function.comp_def]
  have hleft := cellWord_integral f hf (gridPoint M.G) B N hN j
    (fun g hg => hcell g (lt_of_lt_of_le hg hj)) p.reverse (List.nodup_reverse.mpr hp)
  rw [normalizedCount_reverse,List.reverse_reverse,← hprefix] at hleft
  have hright := cellWord_integral (fun i x => f i (1-x)) hrf (gridPoint M.G)
    (fun g => (B (M.G-1-g)).reverse) N hN (M.G-j)
    (fun g hg => hrcell g (lt_of_lt_of_le hg (Nat.sub_le _ _))) p hp
  rw [← hsuffix,List.reverse_reverse] at hright
  have hpoint : gridPoint M.G (M.G-j)=1-gridPoint M.G j := by
    unfold gridPoint
    rw [Nat.cast_sub hj]
    have hGr : (M.G : ℝ)≠0 := by exact_mod_cast Nat.ne_of_gt M.positive_grid
    rw [sub_div,div_self hGr]
  have hz : gridPoint M.G 0=0 := by simp [gridPoint]
  rw [hz,densityPrefixFrom_zero] at hleft
  rw [hz,densityPrefixFrom_zero,hpoint] at hright
  exact ⟨hleft,hright⟩

end FairDice
