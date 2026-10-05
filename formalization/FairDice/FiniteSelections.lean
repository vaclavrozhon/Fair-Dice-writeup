import FairDice.FiniteAverages

namespace FairDice

/-- Reindex a finite-subset sum along an embedding when all contributions
outside its image vanish. -/
theorem sum_finset_embedding {U V : Type*} [Fintype U] [Fintype V]
    [DecidableEq U] [DecidableEq V] (e : U ↪ V) (f : Finset V → ℝ)
    (hf : ∀ I, (¬ ∀ v ∈ I, v ∈ Set.range e) → f I=0) :
    (∑ J : Finset U, f (J.map e))=∑ I : Finset V, f I := by
  classical
  refine Fintype.sum_of_injective (fun J : Finset U => J.map e)
    (Finset.map_injective _) _ _ ?_ (fun _ => rfl)
  intro I hI
  apply hf I
  intro hall
  apply hI
  let J := (Finset.univ : Finset U).filter (fun u => e u ∈ I)
  refine ⟨J,?_⟩
  ext v
  constructor
  · intro hv
    obtain ⟨u,hu,rfl⟩ := Finset.mem_map.mp hv
    exact (Finset.mem_filter.mp hu).2
  · intro hv
    obtain ⟨u,rfl⟩ := hall v hv
    exact Finset.mem_map.mpr ⟨u,by simp [J,hv],rfl⟩

/-- A sum supported on subsets satisfying a predicate can be reindexed by
finite subsets of the corresponding subtype, without multiplicities. -/
theorem sum_finset_subtype {V : Type*} [Fintype V] [DecidableEq V]
    (P : V → Prop) [DecidablePred P] (f : Finset V → ℝ)
    (hf : ∀ I, (¬ ∀ v ∈ I, P v) → f I=0) :
    (∑ J : Finset {v // P v}, f (J.map (Function.Embedding.subtype P)))=
      ∑ I : Finset V, f I := by
  classical
  refine Fintype.sum_of_injective (fun J : Finset {v // P v} =>
    J.map (Function.Embedding.subtype P))
    (Finset.map_injective _) _ _ ?_ (fun _ => rfl)
  intro I hI
  apply hf I
  intro hall
  apply hI
  exact ⟨I.subtype P,Finset.subtype_map_of_mem hall⟩

/-- Products of functions of distinct coordinates have the product mean,
even when their labels form a subset of a larger index type. -/
theorem finiteMean_injective_product {B V Γ : Type*} [Fintype B] [DecidableEq B]
    [Fintype Γ] [Nonempty Γ] [DecidableEq V] (I : Finset V) (t : V → B)
    (ht : Set.InjOn t I) (f : V → Γ → ℝ) :
    finiteMean (fun x : B → Γ => ∏ v ∈ I, f v (x (t v)))=
      ∏ v ∈ I, finiteMean (f v) := by
  classical
  let fiber := fun b => I.filter (fun v => t v=b)
  let F := fun b x => ∏ v ∈ fiber b, f v x
  have hp (x : B → Γ) : (∏ b, F b (x b))=∏ v ∈ I, f v (x (t v)) := by
    calc
      _ = ∏ b : B, ∏ v ∈ fiber b, f v (x (t v)) := by
        apply Finset.prod_congr rfl
        intro b _
        apply Finset.prod_congr rfl
        intro v hv
        rw [(Finset.mem_filter.mp hv).2]
      _ = _ := Finset.prod_fiberwise_of_maps_to (s:=I) (t:=Finset.univ)
        (g:=t) (fun v _ => Finset.mem_univ (t v)) _
  rw [← show (fun x : B → Γ => ∏ b, F b (x b))=
      (fun x => ∏ v ∈ I, f v (x (t v))) from funext hp,
    finiteMean_pi_product (fun _ : B => Γ) F]
  have hm (b : B) : finiteMean (F b)=∏ v ∈ fiber b, finiteMean (f v) := by
    rcases (fiber b).eq_empty_or_nonempty with he | ⟨v,hv⟩
    · simp [F,he]
    · have hs : fiber b={v} := by
        apply Finset.eq_singleton_iff_unique_mem.mpr
        refine ⟨hv,?_⟩
        intro w hw
        exact ht (Finset.mem_filter.mp hw).1 (Finset.mem_filter.mp hv).1
          ((Finset.mem_filter.mp hw).2.trans (Finset.mem_filter.mp hv).2.symm)
      simp [F,hs]
  simp_rw [hm]
  exact Finset.prod_fiberwise_of_maps_to (s:=I) (t:=Finset.univ)
    (g:=t) (fun v _ => Finset.mem_univ (t v)) _

end FairDice
