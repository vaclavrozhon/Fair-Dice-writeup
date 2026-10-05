import FairDice.IndividualUpper
import FairDice.QuadraticIndividual
import Mathlib.Logic.Equiv.Fin.Basic

namespace FairDice

local instance {α : Type*} [DecidableEq α] : BEq (Option α) := instBEqOfDecidableEq

/-- The upper half of `thm:individual-size`, for any specified die in an
alphabet of exactly `n` dice, at every sufficiently large prescribed size. -/
theorem prescribed_individual_size (H : GilboaPeledExternal) :
    ∃ C₀ : ℕ, 0 < C₀ ∧ ∀ n K : ℕ, 2 ≤ n → C₀*n^2 ≤ K →
      ∀ a : Fin n, ∃ N : ℕ, 0 < N ∧ ∃ s : List (Fin n),
        PermutationFair s ∧ s.count a=K ∧ ∀ b, b≠a → s.count b=N := by
  classical
  obtain ⟨C₀,hC,hupper⟩ := individual_faces_upper H
  refine ⟨C₀,hC,fun n K hn hsize a => ?_⟩
  cases n with
  | zero => omega
  | succ m =>
    obtain ⟨N,hN,s,hs,hsa,hsi⟩ := hupper m K (by omega) hsize
    let e := (finSuccEquiv' a).symm
    have he : e none=a := finSuccEquiv'_symm_none a
    have hc (b : Fin (m+1)) : (s.map e).count b=s.count (e.symm b) := by
      simpa only [e.apply_symm_apply] using
        List.count_map_of_injective s e e.injective (e.symm b)
    refine ⟨N,hN,s.map e,permutationFair_relabel e hs,?_,?_⟩
    · rw [hc,show e.symm a=none from by rw [← he,e.symm_apply_apply],hsa]
    · intro b hba
      rw [hc]
      cases h : e.symm b with
      | none =>
        have hb : b=a := by
          calc
            b=e (e.symm b) := (e.apply_symm_apply b).symm
            _=e none := congrArg e h
            _=a := he
        exact False.elim (hba hb)
      | some i => exact hsi i

def AttainableFaces (n : ℕ) (a : Fin n) (K : ℕ) : Prop :=
  ∃ s : List (Fin n), PermutationFair s ∧ s.count a=K

theorem attainableFaces_nonempty (n : ℕ) (a : Fin n) : ∃ K, AttainableFaces n a K := by
  obtain ⟨hs,_,_,hc⟩ := elementary_construction n (by have := a.isLt; omega)
  exact ⟨n.factorial^(n-1),elementaryWord n,hs,hc a⟩

/-- The article's actual minimum over finite permutation-fair families. -/
noncomputable def smallestDieFaces (n : ℕ) (a : Fin n) : ℕ := by
  classical
  exact Nat.find (attainableFaces_nonempty n a)

theorem smallestDieFaces_attainable (n : ℕ) (a : Fin n) :
    AttainableFaces n a (smallestDieFaces n a) := by
  classical
  exact Nat.find_spec (attainableFaces_nonempty n a)

theorem smallestDieFaces_le {n K : ℕ} (a : Fin n) (hK : AttainableFaces n a K) :
    smallestDieFaces n a ≤ K := by
  classical
  exact Nat.find_min' (attainableFaces_nonempty n a) hK

/-- `g(n)=Theta(n^2)`, expressed by explicit uniform two-sided inequalities
for the genuine minimum; the lower constant is `1/800`. -/
theorem optimal_individual_size (Q : ClassicalQuadratureExternal) (H : GilboaPeledExternal) :
    ∃ C₀ : ℕ, 0 < C₀ ∧ ∀ n : ℕ, 2 ≤ n → ∀ a : Fin n,
      (n : ℝ)^2/800 ≤ smallestDieFaces n a ∧ smallestDieFaces n a ≤ C₀*n^2 := by
  obtain ⟨C₀,hC,hupper⟩ := prescribed_individual_size H
  refine ⟨C₀,hC,fun n hn a => ?_⟩
  constructor
  · obtain ⟨s,hs,hsa⟩ := smallestDieFaces_attainable n a
    have hh := each_die_quadratic Q hs (by simpa using hn) a
    rw [hsa] at hh
    simp only [Fintype.card_fin] at hh
    have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hp := mul_nonneg (by linarith : (0 : ℝ) ≤ 3*n-2) (by linarith : (0 : ℝ) ≤ n-2)
    nlinarith
  · obtain ⟨N,hN,s,hs,hsa,_⟩ := hupper n (C₀*n^2) hn le_rfl a
    exact smallestDieFaces_le a ⟨s,hs,hsa⟩

end FairDice
