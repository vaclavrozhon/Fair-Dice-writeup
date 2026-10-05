import FairDice.PalindromeExpectation

namespace FairDice

noncomputable def palindromeCutWeight (n m : ℕ) (ps : List (List (Fin n))) : ℝ :=
  (n.factorial : ℝ)/((m : ℝ)^n*(ps.map (fun p => (p.length.factorial : ℝ))).prod)

noncomputable def palindromeCutDelta {n m : ℕ} (ρ : Fin m → Equiv.Perm (Fin n))
    (ps : List (List (Fin n))) (i : Fin m) : ℝ :=
  palindromeDelta ((List.finRange n).map (ρ i)) (ps[i.val]?.getD [])

/-- The part of the concrete cut expansion selecting the nonconstant
contribution in exactly the blocks indexed by `I`. -/
noncomputable def palindromeBlockPart {n m : ℕ} (σ : Equiv.Perm (Fin n))
    (I : Finset (Fin m)) (ρ : Fin m → Equiv.Perm (Fin n)) : ℝ :=
  ((patternCuts ((List.finRange n).map σ) m).map (fun ps =>
    palindromeCutWeight n m ps * ∏ i ∈ I, palindromeCutDelta ρ ps i)).sum

private theorem cut_list_ofFn {n m : ℕ} (ps : List (List (Fin n))) (hlen : ps.length=m) :
    ps=List.ofFn (fun i : Fin m => ps[i.val]?.getD []) := by
  let f := fun i : Fin m => ps.get (Fin.cast hlen.symm i)
  have hh : ps=List.ofFn f := by
    rw [← List.ofFn_get ps]
    exact List.ofFn_congr hlen ps.get
  rw [hh]
  apply congrArg List.ofFn
  funext i
  simp [f]

private theorem cut_vector_product {n m : ℕ} (ρ : Fin m → Equiv.Perm (Fin n))
    (ps : List (List (Fin n))) (hlen : ps.length=m) :
    (List.zipWith (fun p s => 1+palindromeDelta s p) ps
      ((List.finRange m).map (fun i => (List.finRange n).map (ρ i)))).prod =
        ∏ i : Fin m, (1+palindromeCutDelta ρ ps i) := by
  have hs : ((List.finRange m).map (fun i => (List.finRange n).map (ρ i))) =
      List.ofFn (fun i => (List.finRange n).map (ρ i)) := List.ofFn_eq_map.symm
  conv_lhs => rw [cut_list_ofFn ps hlen,hs]
  have hz : List.zipWith (fun p s => 1+palindromeDelta s p)
      (List.ofFn (fun i : Fin m => ps[i.val]?.getD []))
      (List.ofFn (fun i => (List.finRange n).map (ρ i))) =
        List.ofFn (fun i => 1+palindromeCutDelta ρ ps i) := by
    apply List.ext_getElem (by simp)
    intro i hi hj
    simp [List.getElem_zipWith,palindromeCutDelta]
  rw [hz,List.prod_ofFn]

/-- Every interaction in the actual word is represented by its block set;
this is the homogeneous expansion preceding `eq:palindrome-colored`. -/
theorem palindrome_block_part_expansion {n m : ℕ} (ρ : Fin m → Equiv.Perm (Fin n))
    (σ : Equiv.Perm (Fin n)) :
    palindromeRelativeError ρ σ+1 = ∑ I : Finset (Fin m), palindromeBlockPart σ I ρ := by
  let p := (List.finRange n).map σ
  let ss := (List.finRange m).map (fun i => (List.finRange n).map (ρ i))
  have hplen : p.length=n := by simp [p]
  have hlen : ss.length=m := by simp [ss]
  have hw : (ss.map (fun s => s++s.reverse)).flatten=palindromeWord ρ := by
    simp [ss,palindromeWord,List.map_map,Function.comp_def]
  have hprob : (patternProbability (palindromeWord ρ) p : ℝ)=
      (count p (palindromeWord ρ) : ℝ)/(2*(m : ℝ))^n := by
    unfold patternProbability
    simp [palindromeWord_multiplicity,List.map_const',hplen]
  have he := palindrome_occupancy_expansion p ss
  rw [hplen,hlen,hw] at he
  have hz : palindromeRelativeError ρ σ+1 =
      ((patternCuts p m).map (fun ps => palindromeCutWeight n m ps*
        ∏ i : Fin m, (1+palindromeCutDelta ρ ps i))).sum := by
    have hx : ((patternCuts p m).map (fun ps => palindromeCutWeight n m ps*
        (List.zipWith (fun p s => 1+palindromeDelta s p) ps ss).prod)).sum =
        ((patternCuts p m).map (fun ps => palindromeCutWeight n m ps*
          ∏ i : Fin m, (1+palindromeCutDelta ρ ps i))).sum := by
      congr 1
      apply List.map_congr_left
      intro ps hps
      rw [cut_vector_product ρ ps (patternCuts_length_flatten p m ps hps).1]
    rw [← hx]
    simpa [palindromeRelativeError,p,hprob,palindromeCutWeight,mul_div_assoc] using he
  rw [hz]
  simp only [Finset.prod_one_add,Finset.powerset_univ,Finset.mul_sum]
  unfold palindromeBlockPart
  simp only [List.sum_eq_foldr, p]
  induction patternCuts ((List.finRange n).map σ) m with
  | nil => simp
  | cons ps qs ih => simp [Finset.sum_add_distrib,ih]

/-- The empty selected block set is precisely the constant one. -/
theorem palindrome_block_part_empty {n m : ℕ} (hm : 0 < m)
    (σ : Equiv.Perm (Fin n)) (ρ : Fin m → Equiv.Perm (Fin n)) :
    palindromeBlockPart σ ∅ ρ=1 := by
  simpa [palindromeBlockPart,palindromeCutWeight] using
    palindrome_occupancy_weights_sum ((List.finRange n).map σ) m hm

/-- The exact error is the sum over nonempty block sets. -/
theorem palindrome_error_nonempty_parts {n m : ℕ} (hm : 0 < m)
    (σ : Equiv.Perm (Fin n)) (ρ : Fin m → Equiv.Perm (Fin n)) :
    palindromeRelativeError ρ σ =
      ∑ I ∈ (Finset.univ : Finset (Finset (Fin m))).erase ∅, palindromeBlockPart σ I ρ := by
  have he := palindrome_block_part_expansion ρ σ
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (∅ : Finset (Fin m))),
    palindrome_block_part_empty hm] at he
  linarith

/-- A selected part depends only on its selected blocks. -/
theorem palindrome_part_depends {n m : ℕ} (σ : Equiv.Perm (Fin n)) (I : Finset (Fin m))
    (ρ ρ' : Fin m → Equiv.Perm (Fin n)) (h : ∀ i ∈ I, ρ i=ρ' i) :
    palindromeBlockPart σ I ρ=palindromeBlockPart σ I ρ' := by
  unfold palindromeBlockPart
  congr 1
  apply List.map_congr_left
  intro ps _
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  simp only [palindromeCutDelta,h i hi]

private theorem finiteMean_listSum {Ω β : Type*} [Fintype Ω] (xs : List β) (f : β → Ω → ℝ) :
    finiteMean (fun ω => (xs.map (fun x => f x ω)).sum)=
      (xs.map (fun x => finiteMean (f x))).sum := by
  induction xs with
  | nil => simp [finiteMean]
  | cons x xs ih => simp [finiteMean_add,ih]

/-- Each block part is separately centered in every selected block, for
the actual uniform random permutations, including all its cut terms. -/
theorem palindrome_part_centered {n m : ℕ} (σ : Equiv.Perm (Fin n))
    (I : Finset (Fin m)) (i : Fin m) (hi : i ∈ I)
    (ρ : Fin m → Equiv.Perm (Fin n)) :
    finiteMean (fun e : Equiv.Perm (Fin n) => palindromeBlockPart σ I (Function.update ρ i e))=0 := by
  classical
  unfold palindromeBlockPart
  rw [finiteMean_listSum]
  apply List.sum_eq_zero
  intro x hx
  obtain ⟨ps,hps,rfl⟩ := List.mem_map.mp hx
  let p := (List.finRange n).map σ
  have hp : p.Nodup := (List.nodup_finRange n).map σ.injective
  obtain ⟨hlen,hflat⟩ := patternCuts_length_flatten p m ps hps
  have hpseg : (ps[i.val]?.getD []).Nodup := by
    cases he : ps[i.val]? with
    | none => simp
    | some q =>
      simpa using (List.nodup_flatten.mp (hflat ▸ hp)).1 q (List.mem_of_getElem? he)
  have hcenter : finiteMean (fun e : Equiv.Perm (Fin n) =>
      palindromeDelta ((List.finRange n).map e) (ps[i.val]?.getD []))=0 := by
    have hh := palindromeDelta_centered (List.finRange n) (ps[i.val]?.getD [])
      (List.nodup_finRange n) (fun _ => List.mem_finRange _) hpseg
    simp [finiteMean,hh]
  have hrest (e : Equiv.Perm (Fin n)) :
      (∏ j ∈ I.erase i, palindromeCutDelta (Function.update ρ i e) ps j)=
        ∏ j ∈ I.erase i, palindromeCutDelta ρ ps j := by
    apply Finset.prod_congr rfl
    intro j hj
    simp only [palindromeCutDelta,Function.update_of_ne (Finset.mem_erase.mp hj).1]
  have hprod (e : Equiv.Perm (Fin n)) :
      (∏ j ∈ I, palindromeCutDelta (Function.update ρ i e) ps j)=
        (∏ j ∈ I.erase i, palindromeCutDelta ρ ps j)*
          palindromeDelta ((List.finRange n).map e) (ps[i.val]?.getD []) := by
    rw [← Finset.prod_erase_mul I _ hi,hrest]
    simp [palindromeCutDelta]
  simp_rw [hprod]
  rw [finiteMean_const_mul,finiteMean_const_mul,hcenter,mul_zero,mul_zero]

end FairDice
