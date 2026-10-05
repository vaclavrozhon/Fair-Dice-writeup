import FairDice.ChaosColoring
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

namespace FairDice

/-- A single coordinate of a uniform finite product is uniform. -/
theorem finiteMean_apply {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Γ : ι → Type*) [∀ i, Fintype (Γ i)] [∀ i, Nonempty (Γ i)]
    (j : ι) (f : Γ j → ℝ) :
    finiteMean (fun x : ∀ i, Γ i => f (x j))=finiteMean f := by
  classical
  have he := finiteMean_equiv (Equiv.piSplitAt j Γ)
    (fun x : Γ j × (∀ i : {i // i≠j}, Γ i) => f x.1)
  change (finiteMean fun x => f ((Equiv.piSplitAt j Γ) x).1)=finiteMean f
  rw [he,finiteMean_prod]
  simp

/-- The first successful coin selects size `j+3`. Coins after this one are
unrestricted; the all-false outcome represents sizes above the cutoff. -/
def firstColorSuccess {N : ℕ} (bits : Fin N → Bool) (j : Fin N) : Prop :=
  ∀ i ∈ Finset.Iic j, bits i=decide (i=j)

instance {N : ℕ} (bits : Fin N → Bool) (j : Fin N) : Decidable (firstColorSuccess bits j) := by
  unfold firstColorSuccess
  infer_instance

theorem firstColorSuccess_unique {N : ℕ} (bits : Fin N → Bool) (j k : Fin N)
    (hj : firstColorSuccess bits j) (hk : firstColorSuccess bits k) : j=k := by
  by_contra h
  rcases lt_or_gt_of_ne h with hlt | hlt
  · have ha := hj j (Finset.mem_Iic.mpr le_rfl)
    have hb := hk j (Finset.mem_Iic.mpr hlt.le)
    simp [ne_of_lt hlt] at ha hb
    exact Bool.noConfusion (ha.symm.trans hb)
  · have ha := hk k (Finset.mem_Iic.mpr le_rfl)
    have hb := hj k (Finset.mem_Iic.mpr hlt.le)
    simp [ne_of_lt hlt] at ha hb
    exact Bool.noConfusion (ha.symm.trans hb)

theorem firstColorSuccess_mean {N : ℕ} (j : Fin N) :
    finiteMean (fun bits : Fin N → Bool => if firstColorSuccess bits j then (1 : ℝ) else 0)=
      1/(2 : ℝ)^(j.val+1) := by
  have hind (bits : Fin N → Bool) :
      (if firstColorSuccess bits j then (1 : ℝ) else 0)=
        ∏ i ∈ Finset.Iic j, if bits i=decide (i=j) then (1 : ℝ) else 0 := by
    rw [Finset.prod_boole]
    simp only [firstColorSuccess]
    congr 1
  simp_rw [hind]
  rw [finiteMean_pi_subproduct (fun _ : Fin N => Bool) (Finset.Iic j)
    (fun i b => if b=decide (i=j) then (1 : ℝ) else 0)]
  have hm (i : Fin N) :
      finiteMean (fun b : Bool => if b=decide (i=j) then (1 : ℝ) else 0)=1/2 := by
    by_cases h : i=j <;> norm_num [finiteMean,Fintype.sum_bool,h]
  simp only [hm,Finset.prod_const,Fin.card_Iic,div_pow,one_pow]

abbrev ColorChoice (N : ℕ) := (Fin N → Bool) × (∀ j : Fin N, Fin (j.val+3))

/-- The article's actual size/residue retention event, on a finite space.
Only sizes at most `N+2` are relevant to an `N+2`-letter pattern. -/
noncomputable def colorRetains {N : ℕ} (r : ColorChoice N) (j : Fin N) (a : ℕ) : Bool := by
  classical
  exact decide (firstColorSuccess r.1 j ∧ (r.2 j).val=a%(j.val+3))

theorem colorRetains_mean {N : ℕ} (j : Fin N) (a : ℕ) :
    finiteMean (fun r : ColorChoice N => keepIndicator (colorRetains r j a))=
      (1/(2 : ℝ)^(j.val+1))/(j.val+3) := by
  classical
  have hind (r : ColorChoice N) : keepIndicator (colorRetains r j a)=
      (if firstColorSuccess r.1 j then (1 : ℝ) else 0)*
        (if (r.2 j).val=a%(j.val+3) then (1 : ℝ) else 0) := by
    by_cases h : firstColorSuccess r.1 j <;>
      by_cases ha : (r.2 j).val=a%(j.val+3) <;>
        simp [keepIndicator,colorRetains,h,ha]
  let target : Fin (j.val+3) := ⟨a%(j.val+3),Nat.mod_lt _ (by omega)⟩
  have hm : finiteMean (fun b : Fin (j.val+3) =>
      if b.val=a%(j.val+3) then (1 : ℝ) else 0)=1/(j.val+3) := by
    have hh (b : Fin (j.val+3)) : b.val=a%(j.val+3) ↔ b=target := by
      change b.val=target.val ↔ b=target
      exact Fin.ext_iff.symm
    simp_rw [hh]
    simp [finiteMean,target]
  simp_rw [hind]
  rw [finiteMean_prod]
  change (finiteMean fun bits : Fin N → Bool => finiteMean fun residues : ∀ i : Fin N, Fin (i.val+3) =>
    (if firstColorSuccess bits j then (1 : ℝ) else 0)*
      (if (residues j).val=a%(j.val+3) then (1 : ℝ) else 0))=_
  simp_rw [finiteMean_const_mul]
  rw [finiteMean_apply (fun i : Fin N => Fin (i.val+3)) j
    (fun b => if b.val=a%(j.val+3) then (1 : ℝ) else 0),hm]
  rw [finiteMean_mul_const,firstColorSuccess_mean]
  ring

/-- Different retained segments in one block have the same selected size
and their starts have the same residue. -/
theorem colorRetains_compatible {N : ℕ} (r : ColorChoice N) (j k : Fin N) (a b : ℕ)
    (hj : colorRetains r j a=true) (hk : colorRetains r k b=true) :
    j=k ∧ a%(j.val+3)=b%(k.val+3) := by
  classical
  have hj' : firstColorSuccess r.1 j ∧ (r.2 j).val=a%(j.val+3) := by
    simpa [colorRetains] using hj
  have hk' : firstColorSuccess r.1 k ∧ (r.2 k).val=b%(k.val+3) := by
    simpa [colorRetains] using hk
  have he := firstColorSuccess_unique r.1 j k hj'.1 hk'.1
  subst k
  exact ⟨rfl,hj'.2.symm.trans hk'.2⟩

/-- Retention of a term with one specified segment in each selected block
has exactly the product probability used in the coloring energy. -/
theorem block_color_retention_mean {B : Type*} [Fintype B] [DecidableEq B]
    {N : ℕ} (I : Finset B) (j : B → Fin N) (a : B → ℕ) :
    finiteMean (fun r : B → ColorChoice N => ∏ i ∈ I,
      keepIndicator (colorRetains (r i) (j i) (a i)))=
        ∏ i ∈ I, ((1/(2 : ℝ)^((j i).val+1))/((j i).val+3)) := by
  rw [finiteMean_pi_subproduct (fun _ : B => ColorChoice N) I
    (fun i r => keepIndicator (colorRetains r (j i) (a i)))]
  simp_rw [colorRetains_mean]

end FairDice
