import FairDice.RestrictionOrders
import FairDice.FiniteOrbits

namespace FairDice

variable {α ι : Type*} [DecidableEq α] [Fintype α] [DecidableEq ι] [Fintype ι]

private theorem restrictionOrder_list_product (A : ι → Finset α)
    (hA : ∀ i j, i≠j → Disjoint (A i) (A j)) (s : List α) (hs : s.Nodup)
    (hfull : ∀ a : α, a ∈ s) (τ : ∀ i, Equiv.Perm (A i))
    (L : List ι) (hL : L.Nodup) (i : ι) (ρ : Equiv.Perm α) :
    restrictionOrder (A i) s hs hfull ((L.map (fun j => (τ j).ofSubtype)).prod*ρ)=
      if i ∈ L then τ i*restrictionOrder (A i) s hs hfull ρ else restrictionOrder (A i) s hs hfull ρ := by
  induction L with
  | nil => simp
  | cons j L ih =>
    have hLj : j ∉ L := (List.nodup_cons.mp hL).1
    have hLn : L.Nodup := (List.nodup_cons.mp hL).2
    rw [List.map_cons,List.prod_cons,mul_assoc]
    by_cases hji : j=i
    · subst j
      have hh := restrictionOrder_local (A i) s hs hfull
        ((L.map (fun j => (τ j).ofSubtype)).prod*ρ) (τ i)
      change restrictionOrder (A i) s hs hfull
        ((τ i).ofSubtype*((L.map (fun j => (τ j).ofSubtype)).prod*ρ)) =
          τ i*restrictionOrder (A i) s hs hfull ((L.map (fun j => (τ j).ofSubtype)).prod*ρ) at hh
      rw [hh,ih hLn]
      simp [hLj]
    · have hh := restrictionOrder_disjoint (A i) (A j) (hA i j (Ne.symm hji)) s hs hfull
        ((L.map (fun j => (τ j).ofSubtype)).prod*ρ) (τ j)
      change restrictionOrder (A i) s hs hfull
        ((τ j).ofSubtype*((L.map (fun j => (τ j).ofSubtype)).prod*ρ)) =
          restrictionOrder (A i) s hs hfull ((L.map (fun j => (τ j).ofSubtype)).prod*ρ) at hh
      rw [hh,ih hLn]
      simp [Ne.symm hji]

/-- The relative orders on disjoint alphabets under one uniform global
permutation have exactly the independent uniform product law. The proof
uses actual local relabellings and finite averaging; no independence
assumption or external probabilistic premise is needed. -/
theorem disjoint_relative_orders_uniform (A : ι → Finset α)
    (hA : ∀ i j, i≠j → Disjoint (A i) (A j)) (s : List α) (hs : s.Nodup)
    (hfull : ∀ a : α, a ∈ s) (f : (∀ i, Equiv.Perm (A i)) → ℝ) :
    finiteMean (fun ρ : Equiv.Perm α => f (fun i => restrictionOrder (A i) s hs hfull ρ))=
      finiteMean f := by
  let feature := fun (ρ : Equiv.Perm α) (i : ι) => restrictionOrder (A i) s hs hfull ρ
  let action := fun τ : ∀ i, Equiv.Perm (A i) => Equiv.mulLeft
    ((((Finset.univ : Finset ι).toList).map (fun j => (τ j).ofSubtype)).prod)
  apply finite_orbit_uniform (fun i => Equiv.Perm (A i)) feature action _ f
  intro τ ρ
  funext i
  have hh := restrictionOrder_list_product A hA s hs hfull τ (Finset.univ : Finset ι).toList
    (Finset.nodup_toList _) i ρ
  simpa [feature,action] using hh

/-- The independence identity for arbitrary functions of each selected
relative order, including the segment errors and their powers. -/
theorem disjoint_relative_orders_product (A : ι → Finset α)
    (hA : ∀ i j, i≠j → Disjoint (A i) (A j)) (s : List α) (hs : s.Nodup)
    (hfull : ∀ a : α, a ∈ s) (f : ∀ i, Equiv.Perm (A i) → ℝ) :
    finiteMean (fun ρ : Equiv.Perm α => ∏ i, f i (restrictionOrder (A i) s hs hfull ρ))=
      ∏ i, finiteMean (f i) := by
  rw [disjoint_relative_orders_uniform A hA s hs hfull (fun τ => ∏ i, f i (τ i))]
  exact finiteMean_pi_product (fun i => Equiv.Perm (A i)) f

/-- The same product law across independent blocks and disjoint segments
inside each block. This is the complete finite independence model needed
after fixing the auxiliary colors in the article. -/
theorem disjoint_block_orders_uniform {B : Type*} [Fintype B] [DecidableEq B]
    (J : B → Type*) [∀ b, Fintype (J b)] [∀ b, DecidableEq (J b)]
    (A : ∀ b, J b → Finset α)
    (hA : ∀ b i j, i≠j → Disjoint (A b i) (A b j))
    (s : List α) (hs : s.Nodup) (hfull : ∀ a : α, a ∈ s)
    (f : (∀ b i, Equiv.Perm (A b i)) → ℝ) :
    finiteMean (fun ρ : B → Equiv.Perm α =>
      f (fun b i => restrictionOrder (A b i) s hs hfull (ρ b)))=finiteMean f := by
  let feature := fun (ρ : B → Equiv.Perm α) (b : B) (i : J b) =>
    restrictionOrder (A b i) s hs hfull (ρ b)
  let action := fun τ : ∀ b i, Equiv.Perm (A b i) => Equiv.piCongrRight (fun b => Equiv.mulLeft
    ((((Finset.univ : Finset (J b)).toList).map (fun j => (τ b j).ofSubtype)).prod))
  apply finite_orbit_uniform (fun b => ∀ i, Equiv.Perm (A b i)) feature action _ f
  intro τ ρ
  funext b i
  have hh := restrictionOrder_list_product (A b) (hA b) s hs hfull (τ b)
    (Finset.univ : Finset (J b)).toList (Finset.nodup_toList _) i (ρ b)
  simpa [feature,action] using hh

end FairDice
