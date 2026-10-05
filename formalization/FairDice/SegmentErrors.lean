import FairDice.DisjointOrders
import FairDice.PalindromeCentering
import FairDice.BoundedChaos

namespace FairDice

variable {α : Type} [DecidableEq α] [Fintype α]

theorem restrict_append_word (A : Finset α) (s t : List α) :
    restrict A (s++t)=restrict A s++restrict A t := by simp [restrict]

theorem restrict_reverse_word (A : Finset α) (s : List α) :
    restrict A s.reverse=(restrict A s).reverse := by simp [restrict]

/-- A palindrome segment error only depends on the relative order of its
letters. Deleting every other letter leaves its literal subsequence count
and its normalized error unchanged. -/
theorem palindromeDelta_restrict (A : Finset α) (s : List α) (p : List A) :
    palindromeDelta s (p.map Subtype.val)=palindromeDelta (restrict A s) p := by
  simp only [palindromeDelta,List.length_map]
  rw [← count_restrict A p (s++s.reverse),restrict_append_word,restrict_reverse_word]

/-- Express the actual segment error through its induced relative
permutation. This connects the finite product-order law to the concrete
palindrome subsequence model. -/
theorem palindromeDelta_relative (A : Finset α) (s : List α) (hs : s.Nodup)
    (hfull : ∀ a : α, a ∈ s) (ρ : Equiv.Perm α) (p : List A) :
    palindromeDelta (s.map ρ) (p.map Subtype.val)=
      palindromeDelta (((Finset.univ : Finset A).toList).map
        (restrictionOrder A s hs hfull ρ)) p := by
  rw [palindromeDelta_restrict,restrictionOrder_spec]

/-- Centering holds inside the smaller segment alphabet itself. -/
theorem relative_segment_error_centered (A : Finset α) (p : List A) (hp : p.Nodup) :
    finiteMean (fun τ : Equiv.Perm A =>
      palindromeDelta (((Finset.univ : Finset A).toList).map τ) p)=0 := by
  have hh := palindromeDelta_centered (Finset.univ : Finset A).toList p
    (Finset.nodup_toList _) (fun a => by simp) hp
  unfold finiteMean
  rw [hh,zero_div]

/-- Every function of the disjoint segment errors has exactly the same
expectation under the independent uniform segment permutations. -/
theorem disjoint_segment_errors_uniform {B : Type} [Fintype B] [DecidableEq B]
    (J : B → Type) [∀ b, Fintype (J b)] [∀ b, DecidableEq (J b)]
    (A : ∀ b, J b → Finset α)
    (hA : ∀ b i j, i≠j → Disjoint (A b i) (A b j))
    (s : List α) (hs : s.Nodup) (hfull : ∀ a : α, a ∈ s)
    (p : ∀ b i, List (A b i)) (f : (∀ b, J b → ℝ) → ℝ) :
    finiteMean (fun ρ : B → Equiv.Perm α =>
      f (fun b i => palindromeDelta (s.map (ρ b)) ((p b i).map Subtype.val)))=
    finiteMean (fun τ : ∀ b i, Equiv.Perm (A b i) =>
      f (fun b i => palindromeDelta (((Finset.univ : Finset (A b i)).toList).map (τ b i)) (p b i))) := by
  simp_rw [palindromeDelta_relative _ s hs hfull]
  exact disjoint_block_orders_uniform J A hA s hs hfull (fun τ =>
    f (fun b i => palindromeDelta (((Finset.univ : Finset (A b i)).toList).map (τ b i)) (p b i)))

/-- The fixed-color chaos estimate for the actual independent global
permutations. Several disjoint segments may belong to the same block.
Independence, centering, and the factorial bound are all supplied by the
proved relative-order model; only classical Bonami remains external. -/
theorem disjoint_segment_chaos (H : BonamiExternal) {B : Type} [Fintype B] [DecidableEq B]
    (J : B → Type) [∀ b, Fintype (J b)] [∀ b, DecidableEq (J b)]
    (A : ∀ b, J b → Finset α)
    (hA : ∀ b i j, i≠j → Disjoint (A b i) (A b j))
    (s : List α) (hs : s.Nodup) (hfull : ∀ a : α, a ∈ s)
    (q : ∀ b i, List (A b i)) (hq : ∀ b i, (q b i).Nodup)
    (hk : ∀ b i, 3 ≤ (q b i).length)
    (p : ℝ) (hp : 2 ≤ p) (ell : ℕ) (c : Finset (Sigma J) → ℝ)
    (hc : ∀ I, I.card≠ell → c I=0) :
    finiteLp p (fun ρ : B → Equiv.Perm α => ∑ I : Finset (Sigma J), c I*
      ∏ v ∈ I, palindromeDelta (s.map (ρ v.1)) ((q v.1 v.2).map Subtype.val)) ≤
      (2*Real.sqrt (p-1))^ell * Real.sqrt (∑ I : Finset (Sigma J), (c I)^2*
        ∏ v ∈ I, ((q v.1 v.2).length.factorial*2/(2 : ℝ)^(q v.1 v.2).length)^2) := by
  let Ω := fun v : Sigma J => Equiv.Perm (A v.1 v.2)
  let Z := fun (v : Sigma J) (τ : Ω v) =>
    palindromeDelta (((Finset.univ : Finset (A v.1 v.2)).toList).map τ) (q v.1 v.2)
  let b := fun v : Sigma J => ((q v.1 v.2).length.factorial : ℝ)*2/(2 : ℝ)^(q v.1 v.2).length
  have hZ (v : Sigma J) : finiteMean (Z v)=0 := relative_segment_error_centered _ _ (hq v.1 v.2)
  have hZb (v : Sigma J) (τ : Ω v) : |Z v τ| ≤ b v :=
    palindromeDelta_bound _ _ ((Finset.nodup_toList _).map τ.injective) (hq v.1 v.2) (hk v.1 v.2)
  have ht : finiteLp p (fun ρ : B → Equiv.Perm α => ∑ I : Finset (Sigma J), c I*
      ∏ v ∈ I, palindromeDelta (s.map (ρ v.1)) ((q v.1 v.2).map Subtype.val)) =
        finiteLp p (independentChaos Ω c Z) := by
    unfold finiteLp
    congr 1
    rw [disjoint_segment_errors_uniform J A hA s hs hfull q
      (fun D => |∑ I : Finset (Sigma J), c I*∏ v ∈ I, D v.1 v.2|^p)]
    exact (finiteMean_equiv (Equiv.piCurry (fun b i => Equiv.Perm (A b i)))
      (fun τ => |∑ I : Finset (Sigma J), c I*∏ v ∈ I,
        palindromeDelta (((Finset.univ : Finset (A v.1 v.2)).toList).map (τ v.1 v.2)) (q v.1 v.2)|^p)).symm
  rw [ht]
  exact bounded_independent_chaos Ω H p hp ell c hc Z hZ b (fun v => by dsimp [b]; positivity) hZb

end FairDice
