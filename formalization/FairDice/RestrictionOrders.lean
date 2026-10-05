import FairDice.Restriction
import FairDice.Symmetrization
import FairDice.FiniteAverages

namespace FairDice

variable {α : Type*} [DecidableEq α] [Fintype α]

theorem restrict_nodup (A : Finset α) (s : List α) (hs : s.Nodup) : (restrict A s).Nodup := by
  have hh := hs.filter (fun a => decide (a ∈ A))
  rw [← map_restrict] at hh
  exact List.Nodup.of_map _ hh

theorem restrict_full (A : Finset α) (s : List α) (hfull : ∀ a : α, a ∈ s) :
    ∀ a : A, a ∈ restrict A s := by
  intro a
  apply List.mem_filterMap.mpr
  exact ⟨a.val,hfull a.val,by simp [a.property]⟩

private theorem full_word_length (s : List α) (hs : s.Nodup) (hfull : ∀ a : α, a ∈ s) :
    s.length=Fintype.card α := by
  have he : s.toFinset=Finset.univ := by ext a; simp [hfull a]
  rw [← List.toFinset_card_of_nodup hs,he,Finset.card_univ]

/-- The unique permutation that lists a full injective word in its order,
relative to the fixed canonical list of its alphabet. -/
noncomputable def fullWordPermutation (s : List α) (hs : s.Nodup)
    (hfull : ∀ a : α, a ∈ s) : Equiv.Perm α :=
  Classical.choose (exists_relabel (Finset.univ : Finset α).toList s (Finset.nodup_toList _)
    hs (by simpa using (full_word_length s hs hfull).symm))

theorem fullWordPermutation_spec (s : List α) (hs : s.Nodup) (hfull : ∀ a : α, a ∈ s) :
    ((Finset.univ : Finset α).toList).map (fullWordPermutation s hs hfull)=s :=
  Classical.choose_spec (exists_relabel (Finset.univ : Finset α).toList s (Finset.nodup_toList _)
    hs (by simpa using (full_word_length s hs hfull).symm))

theorem canonical_map_perm_injective (σ τ : Equiv.Perm α)
    (h : ((Finset.univ : Finset α).toList).map σ=((Finset.univ : Finset α).toList).map τ) : σ=τ := by
  ext a
  exact List.map_inj_left.mp h a (by simp)

/-- Relative order induced by a global permutation on a selected alphabet. -/
noncomputable def restrictionOrder (A : Finset α) (s : List α) (hs : s.Nodup)
    (hfull : ∀ a : α, a ∈ s) (ρ : Equiv.Perm α) : Equiv.Perm A :=
  fullWordPermutation (restrict A (s.map ρ)) (restrict_nodup A _ (hs.map ρ.injective))
    (restrict_full A _ (fun a => by
      rw [← ρ.apply_symm_apply a]
      exact List.mem_map.mpr ⟨ρ.symm a,hfull _,rfl⟩))

theorem restrictionOrder_spec (A : Finset α) (s : List α) (hs : s.Nodup)
    (hfull : ∀ a : α, a ∈ s) (ρ : Equiv.Perm α) :
    ((Finset.univ : Finset A).toList).map (restrictionOrder A s hs hfull ρ)=restrict A (s.map ρ) :=
  fullWordPermutation_spec _ _ _

/-- A permutation supported inside `A` relabels its restricted order. -/
theorem restrict_map_local (A : Finset α) (s : List α) (τ : Equiv.Perm A) :
    restrict A (s.map τ.ofSubtype)=(restrict A s).map τ := by
  induction s with
  | nil => rfl
  | cons a s ih =>
    by_cases ha : a ∈ A
    · have he : τ.ofSubtype a=(τ ⟨a,ha⟩).val := Equiv.Perm.ofSubtype_apply_of_mem τ ha
      have ht : τ.ofSubtype a ∈ A := he ▸ (τ ⟨a,ha⟩).property
      simpa [restrict,ha,ht,he] using ih
    · have he : τ.ofSubtype a=a := Equiv.Perm.ofSubtype_apply_of_not_mem τ ha
      simpa [restrict,ha,he] using ih

/-- The induced relative permutation transforms by ordinary composition. -/
theorem restrictionOrder_local (A : Finset α) (s : List α) (hs : s.Nodup)
    (hfull : ∀ a : α, a ∈ s) (ρ : Equiv.Perm α) (τ : Equiv.Perm A) :
    restrictionOrder A s hs hfull (ρ.trans τ.ofSubtype)=
      (restrictionOrder A s hs hfull ρ).trans τ := by
  apply canonical_map_perm_injective
  rw [restrictionOrder_spec]
  have hemap : s.map (ρ.trans τ.ofSubtype)=(s.map ρ).map τ.ofSubtype := by rw [List.map_map]; rfl
  rw [hemap]
  rw [restrict_map_local,← restrictionOrder_spec A s hs hfull ρ,List.map_map]
  rfl

/-- Relabelling that fixes a selected alphabet does not change its order. -/
theorem restrict_map_fix (A : Finset α) (s : List α) (e : Equiv.Perm α)
    (he : ∀ a ∈ A, e a=a) : restrict A (s.map e)=restrict A s := by
  induction s with
  | nil => rfl
  | cons a s ih =>
    by_cases ha : a ∈ A
    · simpa [restrict,ha,he a ha] using ih
    · have hea : e a ∉ A := by
        intro h
        have hh := he (e a) h
        exact ha (e.injective hh ▸ h)
      simpa [restrict,ha,hea] using ih

/-- Disjoint selected alphabets are unaffected by one another's internal
relabellings. This is the structural independence fact for disjoint segments. -/
theorem restrictionOrder_disjoint (A B : Finset α) (hAB : Disjoint A B)
    (s : List α) (hs : s.Nodup) (hfull : ∀ a : α, a ∈ s)
    (ρ : Equiv.Perm α) (τ : Equiv.Perm B) :
    restrictionOrder A s hs hfull (ρ.trans τ.ofSubtype)=restrictionOrder A s hs hfull ρ := by
  apply canonical_map_perm_injective
  rw [restrictionOrder_spec,restrictionOrder_spec]
  have hemap : s.map (ρ.trans τ.ofSubtype)=(s.map ρ).map τ.ofSubtype := by rw [List.map_map]; rfl
  rw [hemap]
  apply restrict_map_fix
  intro a ha
  exact Equiv.Perm.ofSubtype_apply_of_not_mem τ (fun hb => Finset.disjoint_left.mp hAB ha hb)

end FairDice
