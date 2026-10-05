import FairDice.Probability

namespace FairDice

variable {α : Type*} [DecidableEq α]

/-- One suffix for each face of the distinguished die. Its entries are the
positions strictly after that face. Repeated equal suffixes remain repeated. -/
def faceSuffixes (a : α) : List α → List (List α)
  | [] => []
  | b :: s => if a = b then s :: faceSuffixes a s else faceSuffixes a s

theorem length_faceSuffixes (a : α) (s : List α) : (faceSuffixes a s).length = s.count a := by
  induction s with
  | nil => simp [faceSuffixes]
  | cons b s ih =>
    by_cases hab : a = b
    · subst b; simp [faceSuffixes, ih]
    · simp [faceSuffixes, hab, Ne.symm hab, ih]

theorem faceSuffixes_pattern_sum (a : α) (p s : List α) (hp : p.Nodup) :
    ((faceSuffixes a s).map (fun t => (p.map (fun b => t.count b)).prod)).sum =
      (p.permutations'.map (fun q => count (a :: q) s)).sum := by
  induction s with
  | nil => simp [faceSuffixes]
  | cons b s ih =>
    simp only [count_cons_cons, List.sum_map_add]
    by_cases hab : a = b
    · subst b
      simp only [faceSuffixes, if_true, List.map_cons, List.sum_cons]
      rw [ih, sum_permutation_counts _ _ hp]
      omega
    · simp [faceSuffixes, hab, ih]

variable [Fintype α]

/-- Marginal moment identity obtained by conditioning on the distinguished
face. It is the monomial version of the paper's comparison tensor. -/
theorem faceSuffixes_moment_nat {s : List α} (hs : PermutationFair s) (a : α)
    (p : List α) (hp : (a :: p).Nodup) :
    (p.length + 1) *
        ((faceSuffixes a s).map (fun t => (p.map (fun b => t.count b)).prod)).sum =
      s.count a * (p.map (fun b => s.count b)).prod := by
  rw [faceSuffixes_pattern_sum _ _ _ (List.nodup_cons.mp hp).2]
  have hconst (q : List α) (hq : q ∈ p.permutations') :
      count (a :: q) s = count (a :: p) s := by
    apply permutationFair_partialOrder hs (a :: p) hp
    · exact (List.mem_permutations'.mp hq).cons a
    · exact List.Perm.refl _
  rw [List.map_congr_left hconst]
  have hlen : p.permutations'.length = p.length.factorial := by
    rw [← (List.permutations_perm_permutations' _).length_eq, List.length_permutations]
  simp only [List.map_const', List.sum_replicate, hlen, nsmul_eq_mul, Nat.cast_id]
  have hh := partial_count_product hs (a :: p) hp
  simpa only [List.length_cons, Nat.factorial_succ, List.map_cons, List.prod_cons,
    Nat.mul_assoc] using hh

def tailProduct (s t p : List α) : ℚ :=
  (p.map (fun b => (t.count b : ℚ) / s.count b)).prod

omit [Fintype α] in
theorem tailProduct_eq_div (s t p : List α) :
    tailProduct s t p = ((p.map (fun b => t.count b)).prod : ℚ) /
      ((p.map (fun b => s.count b)).prod : ℚ) := by
  induction p with
  | nil => simp [tailProduct]
  | cons b p ih =>
    simp only [tailProduct, List.map_cons, List.prod_cons] at ih ⊢
    rw [ih]
    push_cast
    ring

theorem faceSuffixes_moment {s : List α} (hs : PermutationFair s) (a : α)
    (p : List α) (hp : (a :: p).Nodup) :
    ((faceSuffixes a s).map (fun t => tailProduct s t p)).sum =
      (s.count a : ℚ) / (p.length + 1 : ℚ) := by
  have hprod : 0 < (p.map (fun b => s.count b)).prod := by
    apply List.prod_pos
    intro x hx
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hx
    exact List.count_pos_iff.mpr (hs.1 b)
  have hsum := faceSuffixes_moment_nat hs a p hp
  have hsumQ : (p.length + 1 : ℚ) *
      ((((faceSuffixes a s).map (fun t => (p.map (fun b => t.count b)).prod)).sum : ℕ) : ℚ) =
        (s.count a : ℚ) * ((p.map (fun b => s.count b)).prod : ℚ) := by exact_mod_cast hsum
  simp only [tailProduct_eq_div, div_eq_mul_inv, List.sum_map_mul_right]
  have he : ((faceSuffixes a s).map (fun t => (((p.map (fun b => t.count b)).prod : ℕ) : ℚ))).sum =
      ((((faceSuffixes a s).map (fun t => (p.map (fun b => t.count b)).prod)).sum : ℕ) : ℚ) := by
    simp only [Nat.cast_list_sum, List.map_map, Function.comp_def]
  rw [he]
  have hprodQ : (((p.map (fun b => s.count b)).prod : ℕ) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt hprod
  simp only [← div_eq_mul_inv]
  apply (div_eq_div_iff hprodQ (by positivity : (p.length + 1 : ℚ) ≠ 0)).mpr
  nlinarith

end FairDice
