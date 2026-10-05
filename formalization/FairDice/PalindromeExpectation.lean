import FairDice.BlockExpansion
import FairDice.PalindromeCentering
import FairDice.FiniteMarkov

namespace FairDice

private theorem finiteMean_list_sum {Ω β : Type*} [Fintype Ω]
    (xs : List β) (f : β → Ω → ℝ) :
    finiteMean (fun ω => (xs.map (fun x => f x ω)).sum) = (xs.map (fun x => finiteMean (f x))).sum := by
  induction xs with
  | nil => simp [finiteMean]
  | cons x xs ih => simp [finiteMean_add, ih]

private theorem zipWith_ofFn {α β γ : Type*} {k : ℕ}
    (F : α → β → γ) (f : Fin k → α) (g : Fin k → β) :
    List.zipWith F (List.ofFn f) (List.ofFn g) = List.ofFn (fun i => F (f i) (g i)) := by
  apply List.ext_getElem (by simp)
  intro i hi hj
  simp [List.getElem_zipWith]

private theorem palindrome_cut_mean {n m : ℕ} (ps : List (List (Fin n)))
    (hlen : ps.length = m) (hp : ps.flatten.Nodup) :
    finiteMean (fun ρ : Fin m → Equiv.Perm (Fin n) =>
      (List.zipWith (fun p s => 1+palindromeDelta s p) ps
        ((List.finRange m).map (fun i => (List.finRange n).map (ρ i)))).prod) = 1 := by
  let p : Fin m → List (Fin n) := fun i => ps.get (Fin.cast hlen.symm i)
  have hps : ps = List.ofFn p := by
    rw [← List.ofFn_get ps]
    exact List.ofFn_congr hlen ps.get
  have hnodup (i : Fin m) : (p i).Nodup :=
    (List.nodup_flatten.mp hp).1 _ (List.get_mem _ _)
  have hc (i : Fin m) : finiteMean (fun e : Equiv.Perm (Fin n) =>
      1+palindromeDelta ((List.finRange n).map e) (p i)) = 1 := by
    rw [finiteMean_add, finiteMean_const]
    have hh := palindromeDelta_centered (List.finRange n) (p i)
      (List.nodup_finRange n) (fun _ => List.mem_finRange _) (hnodup i)
    simp [finiteMean, hh]
  simp only [hps, ← List.ofFn_eq_map, zipWith_ofFn, List.prod_ofFn]
  simp only [List.ofFn_eq_map]
  rw [finiteMean_pi_product (fun _ : Fin m => Equiv.Perm (Fin n))
    (fun i e => 1+palindromeDelta ((List.finRange n).map e) (p i))]
  simp [hc]

/-- Uniform independent relabellings center the entire normalized word
probability, including all interactions in the exact occupancy expansion. -/
theorem palindrome_relative_error_mean {n m : ℕ} (hm : 0 < m) (σ : Equiv.Perm (Fin n)) :
    finiteMean (fun ρ : Fin m → Equiv.Perm (Fin n) => palindromeRelativeError ρ σ) = 0 := by
  let p := (List.finRange n).map σ
  let ss := fun (ρ : Fin m → Equiv.Perm (Fin n)) =>
    (List.finRange m).map (fun i => (List.finRange n).map (ρ i))
  have hp : p.Nodup := (List.nodup_finRange n).map σ.injective
  have hplen : p.length = n := by simp [p]
  have hlen (ρ : Fin m → Equiv.Perm (Fin n)) : (ss ρ).length = m := by simp [ss]
  have hw (ρ : Fin m → Equiv.Perm (Fin n)) :
      ((ss ρ).map (fun s => s++s.reverse)).flatten = palindromeWord ρ := by
    simp [palindromeWord, ss, List.map_map, Function.comp_def]
  let weights := fun ps : List (List (Fin n)) => (n.factorial : ℝ)/
    ((m : ℝ)^n * (ps.map (fun p => (p.length.factorial : ℝ))).prod)
  have hex (ρ : Fin m → Equiv.Perm (Fin n)) : (palindromeRelativeError ρ σ)+1 =
      ((patternCuts p m).map (fun ps => weights ps *
        (List.zipWith (fun p s => 1+palindromeDelta s p) ps (ss ρ)).prod)).sum := by
    have hh := palindrome_occupancy_expansion p (ss ρ)
    rw [hw, hplen, hlen] at hh
    have hprob : (patternProbability (palindromeWord ρ) p : ℝ) =
        (count p (palindromeWord ρ) : ℝ)/(2*(m : ℝ))^n := by
      unfold patternProbability
      simp [palindromeWord_multiplicity, List.map_const', hplen]
    simpa [palindromeRelativeError, p, hprob, mul_div_assoc, weights] using hh
  have h : finiteMean (fun ρ : Fin m → Equiv.Perm (Fin n) => palindromeRelativeError ρ σ + 1) = 1 := by
    simp only [hex]
    rw [finiteMean_list_sum]
    have he : ((patternCuts p m).map (fun ps => finiteMean
        (fun ρ : Fin m → Equiv.Perm (Fin n) => weights ps *
          (List.zipWith (fun p s => 1+palindromeDelta s p) ps (ss ρ)).prod))).sum =
        ((patternCuts p m).map weights).sum := by
      congr 1
      apply List.map_congr_left
      intro ps hps
      obtain ⟨hl,hflat⟩ := patternCuts_length_flatten p m ps hps
      rw [finiteMean_const_mul, palindrome_cut_mean ps hl (hflat ▸ hp), mul_one]
    rw [he]
    simpa [weights, hplen] using palindrome_occupancy_weights_sum p m hm
  rw [finiteMean_add, finiteMean_const] at h
  linarith

end FairDice
