import FairDice.BlockExpansion
import FairDice.RationalDesigns

namespace FairDice

/-- A finite family of positive rational masses can be cleared using one
common positive denominator, including simultaneous profiles for many dice. -/
theorem rational_cell_masses_integer {ι γ : Type*} [Fintype ι] [Fintype γ]
    (a : ι → γ → ℚ) (ha : ∀ i g, 0 < a i g) (hs : ∀ i, ∑ g, a i g = 1) :
    ∃ D : ℕ, 0 < D ∧ ∃ w : ι → γ → ℕ,
      (∀ i g, 0 < w i g) ∧ (∀ i g, (w i g : ℚ) = D * a i g) ∧
      ∀ i, ∑ g, w i g = D := by
  classical
  let D := ∏ x : ι × γ, (a x.1 x.2).den
  have hD : 0 < D := Finset.prod_pos (fun x _ => Rat.den_pos _)
  have hc (i : ι) (g : γ) : Clears D (a i g) := by
    apply Clears.of_dvd (d := (a i g).den) _
      (Finset.dvd_prod_of_mem (fun x : ι × γ => (a x.1 x.2).den) (Finset.mem_univ (i,g)))
    refine ⟨(a i g).num, ?_⟩
    have he := Rat.num_div_den (a i g)
    have hn : ((a i g).den : ℚ) ≠ 0 := by exact_mod_cast (a i g).den_ne_zero
    calc
      _ = ((a i g).den : ℚ) * ((a i g).num / (a i g).den) := by rw [he]
      _ = _ := by field_simp
  have hw (i : ι) (g : γ) := positive_integer_weight hD (ha i g) (hc i g)
  choose w hw he using hw
  refine ⟨D, hD, w, hw, he, fun i => ?_⟩
  have hh : (∑ g, (w i g : ℚ)) = D := by
    simp only [he, ← Finset.mul_sum, hs, mul_one]
  exact_mod_cast hh

variable {α : Type*} [DecidableEq α]

private theorem cut_denominator_product (ps ss : List (List α)) (N : α → ℚ)
    (hlen : ps.length = ss.length) :
    (List.zipWith (fun p s => (count p s : ℚ)/(p.map N).prod) ps ss).prod =
      ((List.zipWith (fun p s => (count p s : ℚ)) ps ss).prod)/
        ((ps.flatten.map N).prod) := by
  induction ps generalizing ss with
  | nil => cases ss <;> simp_all
  | cons p ps ih =>
    cases ss with
    | nil => simp at hlen
    | cons s ss =>
      have hl : ps.length = ss.length := by simpa using hlen
      simp only [List.zipWith_cons_cons, List.prod_cons, List.flatten_cons,
        List.map_append, List.prod_append]
      rw [ih ss hl]
      ring

/-- The full cut expansion for literal block words, normalized by the
actual total face counts. This also accommodates singleton boundary blocks. -/
theorem patternProbability_blocks (p : List α) (ss : List (List α)) :
    patternProbability ss.flatten p = ((patternCuts p ss.length).map (fun ps =>
      (List.zipWith (fun p s => (count p s : ℚ)/
        (p.map (fun a => (ss.flatten.count a : ℚ))).prod) ps ss).prod)).sum := by
  unfold patternProbability
  rw [count_blocks]
  simp only [Nat.cast_list_sum, List.map_map, Function.comp_def]
  simp_rw [div_eq_mul_inv]
  rw [← List.sum_map_mul_right]
  apply congrArg List.sum
  apply List.map_congr_left
  intro ps hps
  obtain ⟨hlen,hflat⟩ := patternCuts_length_flatten p ss.length ps hps
  have hh := cut_denominator_product ps ss (fun a => (ss.flatten.count a : ℚ)) hlen
  rw [hflat] at hh
  have hcast : ((List.zipWith count ps ss).prod : ℚ) =
      (List.zipWith (fun p s => (count p s : ℚ)) ps ss).prod := by
    rw [Nat.cast_list_prod]
    congr 1
    exact List.map_zipWith
  simpa only [div_eq_mul_inv, hcast, Nat.cast_list_prod, List.map_map, Function.comp_def] using hh.symm

variable [Fintype α]

/-- Blowing up a fixed fair word realizes the desired rational interval
masses, and all conditional within-cell orders remain uniform. -/
theorem fair_cell_probability {s : List α} (hs : PermutationFair s)
    (F D : ℕ) (hF : 0 < F) (hD : 0 < D) (hc : ∀ a, s.count a = F)
    (w : α → ℕ) (mass : α → ℚ) (hw : ∀ a, (w a : ℚ) = D * mass a)
    (p : List α) (hp : p.Nodup) :
    (count p (blowup w s) : ℚ)/(F*D : ℚ)^p.length =
      (p.map mass).prod / (p.length.factorial : ℚ) := by
  have hcount := partial_count_product hs p hp
  have hreal : (p.length.factorial : ℚ) * count p s = (F : ℚ)^p.length := by
    have hh : (p.map (fun a => s.count a)).prod = F^p.length := by simp [hc]
    rw [hh] at hcount
    exact_mod_cast hcount
  have hn : (p.length.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt (Nat.factorial_pos _)
  have hFq : (F : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hF
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hD
  rw [count_blowup w p s hp, Nat.cast_mul]
  have hpw : ((p.map w).prod : ℚ) = (D : ℚ)^p.length * (p.map mass).prod := by
    simp [Nat.cast_list_prod, List.map_map, Function.comp_def, hw, List.prod_map_mul, List.map_const']
  have hcs : (count p s : ℚ) = (F : ℚ)^p.length / (p.length.factorial : ℚ) :=
    (eq_div_iff hn).mpr (by simpa [mul_comm] using hreal)
  rw [hpw, hcs]
  field_simp
  ring

/-- Every positive rational cell profile is realized by actual finite
blocks with equal total multiplicity for all old dice. -/
theorem finite_cell_profiles {γ : Type*} [Fintype γ]
    {s : List α} (hs : PermutationFair s) (F : ℕ) (hF : 0 < F)
    (hc : ∀ a, s.count a = F) (mass : α → γ → ℚ)
    (hpos : ∀ a g, 0 < mass a g) (hsum : ∀ a, ∑ g, mass a g = 1) :
    ∃ D : ℕ, 0 < D ∧ ∃ blocks : γ → List α,
      (∀ g, PermutationFair (blocks g)) ∧
      (∀ a, ∑ g, (blocks g).count a = F*D) ∧
      ∀ g p, p.Nodup → (count p (blocks g) : ℚ)/(F*D : ℚ)^p.length =
        (p.map (fun a => mass a g)).prod / (p.length.factorial : ℚ) := by
  obtain ⟨D,hD,w,hw,he,hsw⟩ := rational_cell_masses_integer mass hpos hsum
  refine ⟨D,hD,fun g => blowup (fun a => w a g) s, ?_, ?_, ?_⟩
  · intro g
    exact permutationFair_blowup hs _ (fun a => hw a g)
  · intro a
    simp only [multiplicity_blowup, hc, ← Finset.sum_mul, hsw]
    ring
  · intro g p hp
    exact fair_cell_probability hs F D hF hD hc _ _ (fun a => he a g) p hp

end FairDice
