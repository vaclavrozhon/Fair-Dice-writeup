import FairDice.GridRealization
import FairDice.CellMarkers
import FairDice.Elementary
import FairDice.RegularQuadrature

namespace FairDice

open MeasureTheory

local instance {α : Type*} [DecidableEq α] : BEq (Option α) := instBEqOfDecidableEq

theorem nodeMultiplicity_weighted_sum_real {K G : ℕ} (a : Fin K → Fin (G+1))
    (f : Fin (G+1) → ℝ) :
    ∑ i, (nodeMultiplicity a i : ℝ)*f i=∑ q, f (a q) := by
  classical
  calc
    _ = ∑ i : Fin (G+1), ∑ q : Fin K, if a q=i then f i else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      simp [nodeMultiplicity,Finset.sum_ite,Finset.sum_const]
    _ = _ := by rw [Finset.sum_comm]; simp

/-- Realize the proved continuous family by actual finite dice. The
distinguished die retains exactly `K` faces, and all ordinary dice have
the same positive number of faces. -/
theorem CorrectedFamily.finite_realization {m K : ℕ} (C : CorrectedFamily m K)
    (hm : 0 < m) (hK : 0 < K) :
    ∃ N : ℕ, 0 < N ∧ ∃ s : List (Option (Fin m)),
      PermutationFair s ∧ s.count none=K ∧ ∀ i, s.count (some i)=N := by
  classical
  obtain ⟨M⟩ := C.grid_model
  obtain ⟨hs,_,_,hc⟩ := elementary_construction m hm
  let F := m.factorial^(m-1)
  have hF : 0 < F := pow_pos (Nat.factorial_pos _) _
  obtain ⟨D,hD,blocks,_,htotal,hprobQ⟩ := finite_cell_profiles hs F hF hc
    M.mass M.mass_pos M.mass_sum
  let N := F*D
  have hN : 0 < N := Nat.mul_pos hF hD
  have hprob (g : Fin M.G) (p : List (Fin m)) (hp : p.Nodup) :
      normalizedCount N p (blocks g)=
        (p.map (fun i => (M.mass i g : ℝ))).prod/(p.length.factorial : ℝ) := by
    have hh := congrArg (fun x : ℚ => (x : ℝ)) (hprobQ g p hp)
    simp only [Rat.cast_div,Rat.cast_pow,Rat.cast_mul,Rat.cast_natCast] at hh
    convert hh using 1
    · simp only [normalizedCount,N,Nat.cast_mul]
    · simp only [Rat.cast_list_prod,List.map_map,Function.comp_def]
  let δ := fun i => densityCoefficients (C.selection i) (fun q => (C.node q : ℝ))
  have hf (i : Fin m) : LocallyIntegrable (C.density i) volume :=
    profileDensity_local C.bumpSystem C.selection δ i
  have hrf (i : Fin m) : LocallyIntegrable (fun x => C.density i (1-x)) volume :=
    profileDensity_local C.bumpSystem.reflect C.selection δ i
  let B := extendBlocks blocks
  let bs := (List.range M.G).map B
  have hlenbs : bs.length=M.G := by simp [bs]
  have hB (g : ℕ) (hg : g < M.G) : B g=blocks ⟨g,hg⟩ := by simp [B,extendBlocks,hg]
  have hcounts (i : Fin m) : bs.flatten.count i=N := by
    have he : bs.flatten.count i=∑ g : Fin M.G, (blocks g).count i := by
      simp only [bs,List.count_flatten,List.map_map,Function.comp_def]
      have hh := List.sum_toFinset (fun g => (B g).count i) (List.nodup_range (n := M.G))
      rw [← hh,List.toFinset_range,← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro g _
      rw [hB g.val g.isLt]
    exact he.trans (htotal i)
  let k : ℕ → ℕ := fun g => if hg : g < M.G+1 then nodeMultiplicity M.index ⟨g,hg⟩ else 0
  have hk (g : Fin (M.G+1)) : k g.val=nodeMultiplicity M.index g := by
    simp only [k,dif_pos g.isLt]
  let s := insertCellGaps bs k
  have hsnone : s.count none=K := by
    rw [insertCellGaps_none,hlenbs,← Fin.sum_univ_eq_sum_range]
    simp only [hk]
    exact nodeMultiplicity_sum M.index
  have hssome (i : Fin m) : s.count (some i)=N := by
    rw [insertCellGaps_some]
    exact hcounts i
  have hbridge := grid_blocks_prefix_suffix C.density hf hrf
    (fun q => (C.node q : ℝ)) M blocks N hN hprob
  have hmarked (p q : List (Fin m)) (hp : p.Nodup) (hq : q.Nodup) :
      (markedCount p q s : ℝ)/((K : ℝ)*(N : ℝ)^(p.length+q.length))=
        (∑ r, C.conditionalOrder p.reverse q r)/(K : ℝ) := by
    rw [markedCount_insertCellGaps,hlenbs,Nat.cast_sum,← Fin.sum_univ_eq_sum_range,Finset.sum_div]
    have hterm (g : Fin (M.G+1)) :
        ((k g.val*count p (bs.take g.val).flatten*count q (bs.drop g.val).flatten : ℕ) : ℝ)/
          ((K : ℝ)*(N : ℝ)^(p.length+q.length))=
        (nodeMultiplicity M.index g : ℝ)*
          (normalizedCount N p (bs.take g.val).flatten*
            normalizedCount N q (bs.drop g.val).flatten)/(K : ℝ) := by
      rw [hk]
      simp only [normalizedCount,Nat.cast_mul,pow_add]
      ring
    simp_rw [hterm]
    rw [← Finset.sum_div]
    congr 1
    rw [nodeMultiplicity_weighted_sum_real]
    apply Finset.sum_congr rfl
    intro r _
    have hi : (M.index r).val ≤ M.G := by omega
    rw [(hbridge (M.index r).val hi p hp).1,(hbridge (M.index r).val hi q hq).2,
      ← M.node_eq r]
    rfl
  have hfull (l : List (Option (Fin m))) (hl : l.Nodup)
      (hlen : l.length=Fintype.card (Option (Fin m))) :
      (count l s : ℝ)/((K : ℝ)*(N : ℝ)^m)=1/((m+1).factorial : ℝ) := by
    obtain ⟨p,q,rfl,hpq,hlenpq⟩ := full_pattern_split l hl hlen
    have hp := (List.nodup_append.mp hpq).1
    have hq := (List.nodup_append.mp hpq).2.1
    have hnd : (p.reverse++q).Nodup := by
      rw [List.nodup_append] at hpq ⊢
      refine ⟨List.nodup_reverse.mpr hpq.1,hpq.2.1,?_⟩
      intro a ha b hb
      exact hpq.2.2 a (List.mem_reverse.mp ha) b hb
    have hlen' : p.reverse.length+q.length=m := by simpa using hlenpq
    have hh := hmarked p q hp hq
    rw [C.uniform_order hm p.reverse q hnd hlen'] at hh
    have hlenpq' : p.length+q.length=m := by simpa using hlenpq
    simpa only [markedCount,hlenpq'] using hh
  have hfair : PermutationFair s := by
    constructor
    · intro a
      apply List.count_pos_iff.mp
      cases a with
      | none => rw [hsnone]; exact hK
      | some i => rw [hssome]; exact hN
    · intro p q hp hq hpl hql
      have heq := (hfull p hp hpl).trans (hfull q hq hql).symm
      have hden : (K : ℝ)*(N : ℝ)^m≠0 := by positivity
      exact_mod_cast (div_left_inj' hden).mp heq
  exact ⟨N,hN,s,hfair,hsnone,hssome⟩

/-- The prescribed-cardinality quadratic upper bound of the current
article, conditional only on the cited equal-weight quadrature theorem. -/
theorem individual_faces_upper (H : GilboaPeledExternal) :
    ∃ C₀ : ℕ, 0 < C₀ ∧ ∀ m K : ℕ, 0 < m → C₀*(m+1)^2 ≤ K →
      ∃ N : ℕ, 0 < N ∧ ∃ s : List (Option (Fin m)),
        PermutationFair s ∧ s.count none=K ∧ ∀ i, s.count (some i)=N := by
  obtain ⟨C₀,hC,hfamily⟩ := prescribed_density_family H
  refine ⟨C₀,hC,fun m K hm hsize => ?_⟩
  obtain ⟨C⟩ := hfamily m K hm hsize
  exact C.finite_realization hm (by nlinarith)

end FairDice
