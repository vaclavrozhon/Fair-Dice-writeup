import FairDice.FiniteAverages

namespace FairDice

/-- Interchanging two finite expectations is a finite Fubini identity. -/
theorem finiteMean_comm {Ω Γ : Type*} [Fintype Ω] [Fintype Γ] (f : Ω → Γ → ℝ) :
    finiteMean (fun x => finiteMean (f x))=finiteMean (fun y => finiteMean (fun x => f x y)) := by
  simp only [finiteMean,Finset.sum_div]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro x _
  ring

/-- A tuple of finite-group-valued features is uniform on the product
if every coordinatewise left translation is realized by a permutation of
the original sample space. This proves joint uniformity without treating
independence of derived features as an extra input. -/
theorem finite_orbit_uniform {Ω ι : Type*} [Fintype Ω] [Nonempty Ω] [Fintype ι] [DecidableEq ι]
    (G : ι → Type*) [∀ i, Group (G i)] [∀ i, Fintype (G i)]
    (feature : Ω → ∀ i, G i) (action : (∀ i, G i) → Ω ≃ Ω)
    (haction : ∀ τ x, feature (action τ x)=fun i => τ i*feature x i)
    (f : (∀ i, G i) → ℝ) : finiteMean (fun x => f (feature x))=finiteMean f := by
  classical
  have hτ (τ : ∀ i, G i) : finiteMean (fun x => f (feature (action τ x)))=
      finiteMean (fun x => f (feature x)) := finiteMean_equiv (action τ) (fun x => f (feature x))
  have hx (x : Ω) : finiteMean (fun τ : ∀ i, G i => f (fun i => τ i*feature x i))=finiteMean f := by
    exact finiteMean_equiv (Equiv.piCongrRight (fun i => Equiv.mulRight (feature x i))) f
  calc
    _ = finiteMean (fun τ : ∀ i, G i => finiteMean (fun x => f (feature (action τ x)))) := by
      simp only [hτ]
      simp
    _ = finiteMean (fun x => finiteMean (fun τ : ∀ i, G i => f (feature (action τ x)))) :=
      finiteMean_comm _
    _ = finiteMean (fun x => finiteMean (fun τ : ∀ i, G i => f (fun i => τ i*feature x i))) := by
      simp only [haction]
    _ = finiteMean f := by simp [hx]

end FairDice
