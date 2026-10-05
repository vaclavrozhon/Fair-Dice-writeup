import FairDice.OrderResponse
import FairDice.FiniteCells

namespace FairDice

open MeasureTheory Set

noncomputable def gridPoint (G k : ℕ) : ℝ := (k : ℝ)/G

theorem gridPoint_strict {G : ℕ} (hG : 0 < G) : StrictMono (gridPoint G) := by
  intro a b hab
  exact (div_lt_div_iff_of_pos_right (by exact_mod_cast hG)).mpr (by exact_mod_cast hab)

theorem grid_Ioc_membership {G : ℕ} (hG : 0 < G) (g A B : ℕ) (x : ℝ)
    (hx : x ∈ Ioo (gridPoint G g) (gridPoint G (g+1))) :
    x ∈ Ioc (gridPoint G A) (gridPoint G B) ↔ A ≤ g ∧ g < B := by
  have hGr : (0 : ℝ) < G := by exact_mod_cast hG
  have hlo : (g : ℝ) < x*G := (div_lt_iff₀ hGr).mp hx.1
  have hhi : x*G < (g : ℝ)+1 := by
    simpa only [Nat.cast_add,Nat.cast_one] using (lt_div_iff₀ hGr).mp hx.2
  constructor
  · intro h
    have ha := (div_lt_iff₀ hGr).mp h.1
    have hb := (le_div_iff₀ hGr).mp h.2
    constructor
    · by_contra hh
      have hh' : (g : ℝ)+1 ≤ A := by exact_mod_cast (show g+1 ≤ A by omega)
      linarith
    · by_contra hh
      have hh' : (B : ℝ) ≤ g := by exact_mod_cast (show B ≤ g by omega)
      linarith
  · rintro ⟨ha,hb⟩
    have ha' : (A : ℝ) ≤ g := by exact_mod_cast ha
    have hb' : (g : ℝ)+1 ≤ B := by exact_mod_cast hb
    exact ⟨(div_lt_iff₀ hGr).mpr (by linarith),(le_div_iff₀ hGr).mpr (by linarith)⟩

/-- Actual densities constant on a rational grid, with normalized positive
rational cell masses and the distinguished nodes on grid boundaries. -/
structure UniformGridModel (ι : Type*) (K : ℕ) (f : ι → ℝ → ℝ) (u : Fin K → ℝ) where
  G : ℕ
  positive_grid : 0 < G
  index : Fin K → Fin (G+1)
  node_eq : ∀ q, u q=gridPoint G (index q).val
  mass : ι → Fin G → ℚ
  mass_pos : ∀ i g, 0 < mass i g
  mass_sum : ∀ i, ∑ g, mass i g=1
  cell_density : ∀ i (g : Fin G) x,
    x ∈ Ioo (gridPoint G g.val) (gridPoint G (g.val+1)) → f i x=(G : ℝ)*mass i g

theorem CorrectedFamily.grid_model {m K : ℕ} (C : CorrectedFamily m K) :
    Nonempty (UniformGridModel (Fin m) K C.density (fun q => (C.node q : ℝ))) := by
  classical
  let bp : (Fin K ⊕ (Fin K × Fin m × Fin 4)) → ℚ := fun z => match z with
    | .inl q => C.node q
    | .inr (q,j,v) => if v=0 then (C.intervals q).la j else
        if v=1 then (C.intervals q).lb j else
          if v=2 then (C.intervals q).ra j else (C.intervals q).rb j
  have hbp (z) : 0 ≤ bp z ∧ bp z ≤ 1 := by
    rcases z with q | ⟨q,j,v⟩
    · exact ⟨(C.node_interior q).1.le,(C.node_interior q).2.le⟩
    · dsimp only [bp]
      split_ifs
      · exact ⟨((C.intervals q).left_unit j).1,
          ((C.intervals q).left_pos j).le.trans ((C.intervals q).left_unit j).2⟩
      · exact ⟨((C.intervals q).left_unit j).1.trans ((C.intervals q).left_pos j).le,
          ((C.intervals q).left_unit j).2⟩
      · exact ⟨((C.intervals q).right_unit j).1,
          ((C.intervals q).right_pos j).le.trans ((C.intervals q).right_unit j).2⟩
      · exact ⟨((C.intervals q).right_unit j).1.trans ((C.intervals q).right_pos j).le,
          ((C.intervals q).right_unit j).2⟩
  obtain ⟨G,hG,A,hA⟩ := rational_nodes_common_grid bp hbp
  have hGr : (0 : ℝ) < G := by exact_mod_cast hG
  have hbpeq (z) : (bp z : ℝ)=gridPoint G (A z).val := by
    have hh : ((A z).val : ℝ)=(G : ℝ)*(bp z : ℝ) := by exact_mod_cast hA z
    unfold gridPoint
    rw [hh,mul_div_cancel_left₀ _ hGr.ne']
  let mid : Fin G → ℝ := fun g => (gridPoint G g.val+gridPoint G (g.val+1))/2
  have hmid (g : Fin G) : mid g ∈ Ioo (gridPoint G g.val) (gridPoint G (g.val+1)) := by
    have hh := gridPoint_strict hG (show g.val < g.val+1 by omega)
    dsimp [mid]
    constructor <;> linarith
  have hsame (q : Fin K) (g : Fin G) (x : ℝ)
      (hx : x ∈ Ioo (gridPoint G g.val) (gridPoint G (g.val+1))) :
      (C.intervals q).bump (C.node q) x=(C.intervals q).bump (C.node q) (mid g) := by
    have hi (j : Fin m) (v w : Fin 4) :
        (Ioc (bp (.inr (q,j,v)) : ℝ) (bp (.inr (q,j,w)) : ℝ)).indicator
          (fun _ => (1 : ℝ)) x=
        (Ioc (bp (.inr (q,j,v)) : ℝ) (bp (.inr (q,j,w)) : ℝ)).indicator
          (fun _ => (1 : ℝ)) (mid g) := by
      rw [hbpeq (.inr (q,j,v)),hbpeq (.inr (q,j,w))]
      have he := (grid_Ioc_membership hG g.val (A (.inr (q,j,v))).val
        (A (.inr (q,j,w))).val x hx).trans
        (grid_Ioc_membership hG g.val (A (.inr (q,j,v))).val
          (A (.inr (q,j,w))).val (mid g) (hmid g)).symm
      by_cases hh : x ∈ Ioc (gridPoint G (A (.inr (q,j,v))).val)
          (gridPoint G (A (.inr (q,j,w))).val)
      · rw [Set.indicator_of_mem hh,Set.indicator_of_mem (he.mp hh)]
      · rw [Set.indicator_of_notMem hh,Set.indicator_of_notMem (fun h => hh (he.mpr h))]
    have hleft (j : Fin m) := hi j 0 1
    have hright (j : Fin m) := hi j 2 3
    have hb0 (j : Fin m) : bp (.inr (q,j,0))=(C.intervals q).la j := by
      dsimp only [bp]; rw [if_pos rfl]
    have hb1 (j : Fin m) : bp (.inr (q,j,1))=(C.intervals q).lb j := by
      dsimp only [bp]; rw [if_neg (by decide : (1 : Fin 4)≠0),if_pos rfl]
    have hb2 (j : Fin m) : bp (.inr (q,j,2))=(C.intervals q).ra j := by
      dsimp only [bp]
      rw [if_neg (by decide : (2 : Fin 4)≠0),if_neg (by decide : (2 : Fin 4)≠1),if_pos rfl]
    have hb3 (j : Fin m) : bp (.inr (q,j,3))=(C.intervals q).rb j := by
      dsimp only [bp]
      rw [if_neg (by decide : (3 : Fin 4)≠0),if_neg (by decide : (3 : Fin 4)≠1),
        if_neg (by decide : (3 : Fin 4)≠2)]
    simp only [hb0,hb1,hb2,hb3] at hleft hright
    simp only [CorrectionIntervals.bump,momentStep,CorrectionIntervals.leftA,
      CorrectionIntervals.leftB,CorrectionIntervals.rightA,CorrectionIntervals.rightB,hleft,hright]
  have hdensity (i : Fin m) (g : Fin G) (x : ℝ)
      (hx : x ∈ Ioo (gridPoint G g.val) (gridPoint G (g.val+1))) :
      C.density i x=C.density i (mid g) := by
    unfold density profileDensity
    simp only [CorrectedFamily.bumpSystem]
    simp_rw [hsame _ g x hx]
  have hrat (i : Fin m) (g : Fin G) : ∃ c : ℚ, C.density i (mid g)=c := C.rational i (mid g)
  choose c hc using hrat
  let mass : Fin m → Fin G → ℚ := fun i g => c i g/G
  have hcell (i : Fin m) (g : Fin G) (x : ℝ)
      (hx : x ∈ Ioo (gridPoint G g.val) (gridPoint G (g.val+1))) :
      C.density i x=(G : ℝ)*(mass i g : ℝ) := by
    rw [hdensity i g x hx,hc]
    dsimp [mass]
    push_cast
    field_simp
  have hmasspos (i : Fin m) (g : Fin G) : 0 < mass i g := by
    have hp : (0 : ℝ) < (c i g : ℝ) := by
      have hh := C.positive i (mid g)
      change (1/2 : ℝ) ≤ C.density i (mid g) at hh
      rw [hc] at hh
      linarith
    exact div_pos (by exact_mod_cast hp) (by exact_mod_cast hG)
  have hint (i : Fin m) (g : Fin G) :
      (∫ x in gridPoint G g.val..gridPoint G (g.val+1), C.density i x)=(mass i g : ℝ) := by
    calc
      _ = ∫ x in gridPoint G g.val..gridPoint G (g.val+1), (G : ℝ)*(mass i g : ℝ) :=
        intervalIntegral.integral_congr_Ioo_of_le (gridPoint_strict hG (by omega)).le
          (fun x hx => hcell i g x hx)
      _ = _ := by simp [intervalIntegral.integral_const,gridPoint]; field_simp; ring
  have hsum (i : Fin m) : ∑ g, mass i g=1 := by
    have hh := intervalIntegral.sum_integral_adjacent_intervals (n := G)
      (a := gridPoint G) (fun k _ => correctedDensity_intervalIntegrable
        (C.selection i) C.intervals (fun q => (C.node q : ℝ)) _ _)
    change (∑ k ∈ Finset.range G, ∫ x in gridPoint G k..gridPoint G (k+1), C.density i x)=_ at hh
    rw [← Fin.sum_univ_eq_sum_range] at hh
    change (∑ g : Fin G, ∫ x in gridPoint G g.val..gridPoint G (g.val+1), C.density i x)=
      (∫ x in gridPoint G 0..gridPoint G G, C.density i x) at hh
    have hmass : (∑ g : Fin G, (mass i g : ℝ))=
        ∑ g : Fin G, ∫ x in gridPoint G g.val..gridPoint G (g.val+1), C.density i x :=
      Finset.sum_congr rfl (fun g _ => (hint i g).symm)
    rw [← hmass] at hh
    simp only [gridPoint,Nat.cast_zero,zero_div,div_self hGr.ne'] at hh
    have hn := C.normalized i
    change (∫ x in (0 : ℝ)..1, C.density i x)=1 at hn
    rw [hn] at hh
    exact_mod_cast hh
  exact ⟨⟨G,hG,fun q => A (.inl q),fun q => hbpeq (.inl q),mass,hmasspos,hsum,hcell⟩⟩

end FairDice
