import FairDice.FiniteAverages

namespace FairDice

noncomputable def rademacherSign (b : Bool) : ℝ := if b then 1 else -1

noncomputable def rademacherChaos {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : Finset ι → ℝ) (ε : ι → Bool) : ℝ :=
  ∑ A : Finset ι, c A * ∏ v ∈ A, rademacherSign (ε v)

/-- Only the classical degree-ℓ Rademacher hypercontractive inequality is
assumed. Centering, boundedness, independent copies and their consequences
for general independent finite random variables are not included here. -/
structure BonamiExternal where
  moment_bound : ∀ {ι : Type} [Fintype ι] [DecidableEq ι]
    (p : ℝ) (hp : 2 ≤ p) (ell : ℕ) (c : Finset ι → ℝ),
    (∀ A, A.card ≠ ell → c A = 0) →
    finiteMean (fun ε : ι → Bool => |rademacherChaos c ε|^p) ≤
      ((Real.sqrt (p-1))^ell * Real.sqrt (∑ A : Finset ι, (c A)^2))^p

variable {ι : Type} [Fintype ι] [DecidableEq ι]
    (Ω : ι → Type) [∀ v, Fintype (Ω v)] [∀ v, Nonempty (Ω v)]

noncomputable def independentChaos (c : Finset ι → ℝ) (Z : ∀ v, Ω v → ℝ)
    (x : ∀ v, Ω v) : ℝ := ∑ A : Finset ι, c A * ∏ v ∈ A, Z v (x v)

/-- Averaging the independent-copy differences exactly recovers the original
chaos, using only centering and the product probability law. -/
theorem independentChaos_symmetrization (c : Finset ι → ℝ) (Z : ∀ v, Ω v → ℝ)
    (hZ : ∀ v, finiteMean (Z v) = 0) (x : ∀ v, Ω v) :
    finiteMean (fun y : ∀ v, Ω v =>
      independentChaos Ω c (fun v z => Z v (x v)-Z v z) y) = independentChaos Ω c Z x := by
  unfold independentChaos
  rw [finiteMean_sum]
  apply Finset.sum_congr rfl
  intro A _
  rw [finiteMean_const_mul, finiteMean_pi_subproduct Ω A (fun v z => Z v (x v)-Z v z)]
  simp [hZ]

noncomputable def pairSwap (ε : ι → Bool) :
    (∀ v, Ω v × Ω v) ≃ (∀ v, Ω v × Ω v) :=
  Equiv.piCongrRight (fun v => if ε v then Equiv.refl _ else Equiv.prodComm _ _)

private theorem pairSwap_difference (ε : ι → Bool) (Z : ∀ v, Ω v → ℝ)
    (s : ∀ v, Ω v × Ω v) (v : ι) :
    Z v ((pairSwap Ω ε s v).1)-Z v ((pairSwap Ω ε s v).2) =
      rademacherSign (ε v) * (Z v (s v).1-Z v (s v).2) := by
  cases h : ε v <;> simp [pairSwap, h, rademacherSign] <;> ring

private theorem pairSwap_chaos (c : Finset ι → ℝ) (ε : ι → Bool)
    (Z : ∀ v, Ω v → ℝ) (s : ∀ v, Ω v × Ω v) :
    independentChaos (fun v => Ω v × Ω v) c (fun v z => Z v z.1-Z v z.2) (pairSwap Ω ε s) =
      rademacherChaos (fun A => c A * ∏ v ∈ A, (Z v (s v).1-Z v (s v).2)) ε := by
  unfold independentChaos rademacherChaos
  apply Finset.sum_congr rfl
  intro A _
  simp only [pairSwap_difference, Finset.prod_mul_distrib]
  ring

private theorem bounded_difference_energy (ell : ℕ) (c : Finset ι → ℝ)
    (hc : ∀ A, A.card ≠ ell → c A = 0) (Z : ∀ v, Ω v → ℝ) (b : ι → ℝ)
    (hb : ∀ v, 0 ≤ b v) (hZb : ∀ v x, |Z v x| ≤ b v) (s : ∀ v, Ω v × Ω v) :
    (∑ A : Finset ι, (c A * ∏ v ∈ A, (Z v (s v).1-Z v (s v).2))^2) ≤
      (2 : ℝ)^(2*ell) * ∑ A : Finset ι, (c A)^2 * ∏ v ∈ A, (b v)^2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro A _
  by_cases hA : A.card = ell
  · have hd (v : ι) : (Z v (s v).1-Z v (s v).2)^2 ≤ (2*b v)^2 := by
      have hh := (abs_sub (Z v (s v).1) (Z v (s v).2)).trans
        (add_le_add (hZb v _) (hZb v _))
      nlinarith [sq_abs (Z v (s v).1-Z v (s v).2), abs_nonneg (Z v (s v).1-Z v (s v).2), hb v]
    calc
      _ = (c A)^2 * ∏ v ∈ A, (Z v (s v).1-Z v (s v).2)^2 := by rw [mul_pow, Finset.prod_pow]
      _ ≤ (c A)^2 * ∏ v ∈ A, (2*b v)^2 :=
        mul_le_mul_of_nonneg_left (Finset.prod_le_prod (fun _ _ => sq_nonneg _) (fun v _ => hd v)) (sq_nonneg _)
      _ = _ := by simp [mul_pow, Finset.prod_mul_distrib, hA, pow_mul]; ring
  · simp [hc A hA]

/-- The bounded multilinear chaos estimate in `lem:palindrome-chaos`, for
independent uniform finite coordinates. The finite probability model covers
independent random permutations and requires only classical Bonami as input. -/
theorem bounded_independent_chaos (B : BonamiExternal) (p : ℝ) (hp : 2 ≤ p)
    (ell : ℕ) (c : Finset ι → ℝ) (hc : ∀ A, A.card ≠ ell → c A = 0)
    (Z : ∀ v, Ω v → ℝ) (hZ : ∀ v, finiteMean (Z v) = 0)
    (b : ι → ℝ) (hb : ∀ v, 0 ≤ b v) (hZb : ∀ v x, |Z v x| ≤ b v) :
    finiteLp p (independentChaos Ω c Z) ≤ (2*Real.sqrt (p-1))^ell *
      Real.sqrt (∑ A : Finset ι, (c A)^2 * ∏ v ∈ A, (b v)^2) := by
  let S := ∑ A : Finset ι, (c A)^2 * ∏ v ∈ A, (b v)^2
  let C := (2*Real.sqrt (p-1))^ell * Real.sqrt S
  have hS : 0 ≤ S := Finset.sum_nonneg (fun A _ => mul_nonneg (sq_nonneg _) (Finset.prod_nonneg (fun _ _ => sq_nonneg _)))
  have hC : 0 ≤ C := by positivity
  apply finiteLp_le_of_moment (by linarith) hC
  have hJ (x : ∀ v, Ω v) : |independentChaos Ω c Z x|^p ≤
      finiteMean (fun y : ∀ v, Ω v => |independentChaos Ω c (fun v z => Z v (x v)-Z v z) y|^p) := by
    rw [← independentChaos_symmetrization Ω c Z hZ x]
    exact finiteMean_abs_rpow _ p (by linarith)
  have hstart := finiteMean_mono hJ
  have hpair : finiteMean (fun x : ∀ v, Ω v => finiteMean (fun y : ∀ v, Ω v =>
      |independentChaos Ω c (fun v z => Z v (x v)-Z v z) y|^p)) =
      finiteMean (fun s : ∀ v, Ω v × Ω v =>
        |independentChaos (fun v => Ω v × Ω v) c (fun v z => Z v z.1-Z v z.2) s|^p) := by
    rw [← finiteMean_prod (fun xy : ((∀ v, Ω v) × (∀ v, Ω v)) =>
      |independentChaos Ω c (fun v z => Z v (xy.1 v)-Z v z) xy.2|^p)]
    let e : ((∀ v, Ω v) × (∀ v, Ω v)) ≃ (∀ v, Ω v × Ω v) :=
      ⟨fun xy v => (xy.1 v,xy.2 v), fun s => (fun v => (s v).1,fun v => (s v).2),
        by intro xy; rcases xy with ⟨x,y⟩; rfl, by intro s; ext v <;> rfl⟩
    simpa [independentChaos, e] using finiteMean_equiv e
      (fun s : ∀ v, Ω v × Ω v =>
        |independentChaos (fun v => Ω v × Ω v) c (fun v z => Z v z.1-Z v z.2) s|^p)
  rw [hpair] at hstart
  have hcond (s : ∀ v, Ω v × Ω v) : finiteMean (fun ε : ι → Bool =>
      |rademacherChaos (fun A => c A * ∏ v ∈ A, (Z v (s v).1-Z v (s v).2)) ε|^p) ≤ C^p := by
    have hh := B.moment_bound p hp ell (fun A => c A * ∏ v ∈ A, (Z v (s v).1-Z v (s v).2))
      (fun A hA => by simp [hc A hA])
    have he := Real.sqrt_le_sqrt (bounded_difference_energy Ω ell c hc Z b hb hZb s)
    have heq : Real.sqrt ((2 : ℝ)^(2*ell)*S) = (2 : ℝ)^ell * Real.sqrt S := by
      rw [show (2 : ℝ)^(2*ell) = ((2 : ℝ)^ell)^2 by rw [Nat.mul_comm 2 ell, pow_mul],
        Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
    rw [heq] at he
    have hbase : (Real.sqrt (p-1))^ell * Real.sqrt (∑ A : Finset ι,
        (c A * ∏ v ∈ A, (Z v (s v).1-Z v (s v).2))^2) ≤ C := by
      calc
        _ ≤ (Real.sqrt (p-1))^ell * ((2 : ℝ)^ell * Real.sqrt S) :=
          mul_le_mul_of_nonneg_left he (by positivity)
        _ = C := by dsimp [C]; rw [mul_pow]; ring
    exact hh.trans (Real.rpow_le_rpow (by positivity) hbase (by linarith))
  have hswap (ε : ι → Bool) : finiteMean (fun s : ∀ v, Ω v × Ω v =>
      |independentChaos (fun v => Ω v × Ω v) c (fun v z => Z v z.1-Z v z.2) s|^p) =
      finiteMean (fun s : ∀ v, Ω v × Ω v =>
        |rademacherChaos (fun A => c A * ∏ v ∈ A, (Z v (s v).1-Z v (s v).2)) ε|^p) := by
    rw [← finiteMean_equiv (pairSwap Ω ε)]
    simp only [pairSwap_chaos]
  have hsign : finiteMean (fun s : ∀ v, Ω v × Ω v =>
      |independentChaos (fun v => Ω v × Ω v) c (fun v z => Z v z.1-Z v z.2) s|^p) ≤ C^p := by
    let f := fun (s : ∀ v, Ω v × Ω v) (ε : ι → Bool) =>
      |rademacherChaos (fun A => c A * ∏ v ∈ A, (Z v (s v).1-Z v (s v).2)) ε|^p
    have hm : finiteMean (fun ε : ι → Bool => finiteMean (fun s => f s ε)) =
        finiteMean (fun s => finiteMean (fun ε : ι → Bool => f s ε)) := by
      simp only [finiteMean, Finset.sum_div]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro ε _
      ring
    have hconst : finiteMean (fun ε : ι → Bool => finiteMean (fun s => f s ε)) =
        finiteMean (fun s : ∀ v, Ω v × Ω v =>
          |independentChaos (fun v => Ω v × Ω v) c (fun v z => Z v z.1-Z v z.2) s|^p) := by
      simp only [show (fun ε : ι → Bool => finiteMean (fun s => f s ε)) =
        (fun _ => finiteMean (fun s : ∀ v, Ω v × Ω v =>
          |independentChaos (fun v => Ω v × Ω v) c (fun v z => Z v z.1-Z v z.2) s|^p)) from
          funext (fun ε => (hswap ε).symm)]
      exact finiteMean_const _
    rw [← hconst, hm]
    exact (finiteMean_mono hcond).trans (by simp)
  exact hstart.trans hsign

end FairDice
