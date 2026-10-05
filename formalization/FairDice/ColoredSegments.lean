import FairDice.ColorRetention
import FairDice.ResidueSegments
import FairDice.FiniteSelections

namespace FairDice

/-- All consecutive target segments of admissible length at least three. -/
abbrev ConsecutiveSegment (n : ℕ) :=
  {t : Fin (n+1) × Fin (n-2) // t.1.val+t.2.val+3 ≤ n}

def segmentStart {n : ℕ} (t : ConsecutiveSegment n) : ℕ := t.val.1.val
def segmentSizeIndex {n : ℕ} (t : ConsecutiveSegment n) : Fin (n-2) := t.val.2
def segmentLength {n : ℕ} (t : ConsecutiveSegment n) : ℕ := t.val.2.val+3

theorem segment_fits {n : ℕ} (t : ConsecutiveSegment n) :
    segmentStart t+segmentLength t ≤ n := by
  exact t.property

theorem segment_eq {n : ℕ} {u v : ConsecutiveSegment n}
    (ha : segmentStart u=segmentStart v) (hk : segmentSizeIndex u=segmentSizeIndex v) : u=v := by
  apply Subtype.ext
  exact Prod.ext (Fin.ext ha) hk

noncomputable def segmentRetained {n : ℕ} (r : ColorChoice (n-2))
    (t : ConsecutiveSegment n) : Bool :=
  colorRetains r (segmentSizeIndex t) (segmentStart t)

noncomputable def segmentRetentionWeight {n : ℕ} (t : ConsecutiveSegment n) : ℝ :=
  (1/(2 : ℝ)^((segmentSizeIndex t).val+1))/segmentLength t

theorem segmentRetentionWeight_pos {n : ℕ} (t : ConsecutiveSegment n) :
    0 < segmentRetentionWeight t := by
  unfold segmentRetentionWeight segmentLength
  positivity

theorem retained_segment_alphabets_disjoint {n : ℕ} (σ : Equiv.Perm (Fin n))
    (r : ColorChoice (n-2)) (u v : ConsecutiveSegment n) (hu : segmentRetained r u=true)
    (hv : segmentRetained r v=true) (hne : u≠v) :
    Disjoint (segmentAlphabet σ (segmentStart u) (segmentLength u) (segment_fits u))
      (segmentAlphabet σ (segmentStart v) (segmentLength v) (segment_fits v)) := by
  have hc := colorRetains_compatible r (segmentSizeIndex u) (segmentSizeIndex v)
    (segmentStart u) (segmentStart v) hu hv
  have hk : segmentLength u=segmentLength v := congrArg (fun j : Fin (n-2) => j.val+3) hc.1
  have ha : segmentStart u≠segmentStart v := fun h => hne (segment_eq h hc.1)
  have hvfit : segmentStart v+segmentLength u ≤ n := by rw [hk]; exact segment_fits v
  have hmod : segmentStart u%segmentLength u=segmentStart v%segmentLength u := by
    have hh := hc.2
    change segmentStart u%segmentLength u=segmentStart v%segmentLength v at hh
    rwa [← hk] at hh
  have hh := residue_segment_alphabets_disjoint σ (segmentLength u)
    (segmentStart u) (segmentStart v) (by dsimp [segmentLength]; omega)
    (segment_fits u) hvfit ha hmod
  simpa only [hk] using hh

variable {n : ℕ} {B : Type} [Fintype B] [DecidableEq B]

abbrev BlockSegment (B : Type) (n : ℕ) := Σ _ : B, ConsecutiveSegment n

noncomputable def segmentTermRetained (r : B → ColorChoice (n-2))
    (I : Finset (BlockSegment B n)) : Bool := by
  classical
  exact decide (∀ v ∈ I, segmentRetained (r v.1) v.2=true)

noncomputable def segmentTermWeight (I : Finset (BlockSegment B n)) : ℝ :=
  ∏ v ∈ I, segmentRetentionWeight v.2

theorem segment_term_retention_mean (I : Finset (BlockSegment B n))
    (hI : Set.InjOn (fun v : BlockSegment B n => v.1) I) :
    finiteMean (fun r : B → ColorChoice (n-2) => keepIndicator (segmentTermRetained r I))=
      segmentTermWeight I := by
  classical
  have hp (r : B → ColorChoice (n-2)) : keepIndicator (segmentTermRetained r I)=
      ∏ v ∈ I, keepIndicator (segmentRetained (r v.1) v.2) := by
    simp only [keepIndicator,segmentTermRetained,decide_eq_true_eq]
    rw [Finset.prod_boole]
    split_ifs <;> rfl
  simp_rw [hp]
  rw [finiteMean_injective_product I Sigma.fst hI
    (fun v r => keepIndicator (segmentRetained r v.2))]
  unfold segmentTermWeight
  apply Finset.prod_congr rfl
  intro v _
  simpa [segmentRetained,segmentRetentionWeight,segmentLength,segmentSizeIndex] using
    colorRetains_mean (segmentSizeIndex v.2) (segmentStart v.2)

noncomputable def segmentError (σ : Equiv.Perm (Fin n))
    (v : BlockSegment B n) (ρ : B → Equiv.Perm (Fin n)) : ℝ :=
  palindromeDelta ((List.finRange n).map (ρ v.1))
    ((segmentPattern σ (segmentStart v.2) (segmentLength v.2) (segment_fits v.2)).map Subtype.val)

noncomputable def segmentErrorBound (v : BlockSegment B n) : ℝ :=
  ((segmentLength v.2).factorial : ℝ)*2/(2 : ℝ)^segmentLength v.2

/-- For a fixed actual color, all retained segment variables have disjoint
alphabets inside each block. Reindexing preserves every coefficient and
its squared energy, so the proved segment chaos estimate applies. -/
theorem fixed_color_segment_chaos (H : BonamiExternal) (σ : Equiv.Perm (Fin n))
    (r : B → ColorChoice (n-2)) (p : ℝ) (hp : 2 ≤ p) (ell : ℕ)
    (c : Finset (BlockSegment B n) → ℝ) (hc : ∀ I, I.card≠ell → c I=0) :
    finiteLp p (coloredSum segmentTermRetained segmentTermWeight c
      (fun I ρ => ∏ v ∈ I, segmentError σ v ρ) r) ≤
      (2*Real.sqrt (p-1))^ell*Real.sqrt
        (coloredEnergy segmentTermRetained segmentTermWeight c
          (fun I => ∏ v ∈ I, segmentErrorBound v) r) := by
  classical
  let J := fun b : B => {t : ConsecutiveSegment n // segmentRetained (r b) t=true}
  let E : Sigma J ↪ BlockSegment B n := Function.Embedding.sigmaMap
    (Function.Embedding.refl B) (fun b => Function.Embedding.subtype
      (fun t : ConsecutiveSegment n => segmentRetained (r b) t=true))
  let A := fun b (t : J b) => segmentAlphabet σ (segmentStart t.val)
    (segmentLength t.val) (segment_fits t.val)
  let q := fun b (t : J b) => segmentPattern σ (segmentStart t.val)
    (segmentLength t.val) (segment_fits t.val)
  have hqlen (b : B) (t : J b) : (q b t).length=segmentLength t.val := by
    simp [q,segmentPattern]
  let C := fun I => (c I/segmentTermWeight I)*keepIndicator (segmentTermRetained r I)
  have hA (b : B) (u v : J b) (hne : u≠v) : Disjoint (A b u) (A b v) :=
    retained_segment_alphabets_disjoint σ (r b) u.val v.val u.property v.property
      (fun h => hne (Subtype.ext h))
  have hout (I : Finset (BlockSegment B n))
      (hI : ¬ ∀ v ∈ I, v ∈ Set.range E) : C I=0 := by
    have hz : segmentTermRetained r I=false := by
      apply Bool.eq_false_iff.mpr
      intro ht
      have hall : ∀ v ∈ I, segmentRetained (r v.1) v.2=true := by
        simpa [segmentTermRetained] using ht
      apply hI
      intro v hv
      exact ⟨⟨v.1,⟨v.2,hall v hv⟩⟩,rfl⟩
    simp [C,hz,keepIndicator]
  have hs (ρ : B → Equiv.Perm (Fin n)) :
      (∑ U : Finset (Sigma J), C (U.map E)*∏ v ∈ U, segmentError σ (E v) ρ)=
        ∑ I : Finset (BlockSegment B n), C I*∏ v ∈ I, segmentError σ v ρ := by
    simpa only [Finset.prod_map] using sum_finset_embedding E
      (fun I => C I*∏ v ∈ I, segmentError σ v ρ)
      (fun I hI => by rw [hout I hI,zero_mul])
  have he : (∑ U : Finset (Sigma J), (C (U.map E))^2*
      ∏ v ∈ U, (segmentErrorBound (E v))^2)=
        ∑ I : Finset (BlockSegment B n), (C I)^2*∏ v ∈ I, (segmentErrorBound v)^2 := by
    simpa only [Finset.prod_map] using sum_finset_embedding E
      (fun I => (C I)^2*∏ v ∈ I, (segmentErrorBound v)^2)
      (fun I hI => by rw [hout I hI]; simp)
  have hh := disjoint_segment_chaos H J A hA (List.finRange n) (List.nodup_finRange n)
    (fun a => List.mem_finRange a) q
    (fun b t => segmentPattern_nodup σ _ _ _)
    (fun b t => by rw [hqlen]; dsimp [segmentLength]; omega)
    p hp ell (fun U => C (U.map E))
    (fun U hU => by simp [C,hc (U.map E) (by simpa using hU)])
  change finiteLp p (fun ρ => ∑ I : Finset (BlockSegment B n), C I*
      ∏ v ∈ I, segmentError σ v ρ) ≤
    (2*Real.sqrt (p-1))^ell*Real.sqrt (∑ I : Finset (BlockSegment B n),
      (C I)^2*(∏ v ∈ I, segmentErrorBound v)^2)
  simp_rw [← Finset.prod_pow]
  rw [← he,← show (fun ρ : B → Equiv.Perm (Fin n) => ∑ U : Finset (Sigma J),
      C (U.map E)*∏ v ∈ U, segmentError σ (E v) ρ)=
        (fun ρ => ∑ I : Finset (BlockSegment B n), C I*∏ v ∈ I, segmentError σ v ρ)
      from funext hs]
  simp only [hqlen] at hh
  exact hh

/-- The complete coloring inequality for actual consecutive palindrome
segments, with their inverse retention factors. The only external premise
is Bonami; no independence, retention probability, or fixed-color norm
estimate is supplied as a hypothesis. -/
theorem colored_segment_chaos (H : BonamiExternal) (σ : Equiv.Perm (Fin n))
    (p : ℝ) (hp : 2 ≤ p) (ell : ℕ) (c : Finset (BlockSegment B n) → ℝ)
    (hc : ∀ I, I.card≠ell → c I=0)
    (hblock : ∀ I, c I≠0 → Set.InjOn (fun v : BlockSegment B n => v.1) I) :
    finiteLp p (fun ρ : B → Equiv.Perm (Fin n) =>
      ∑ I : Finset (BlockSegment B n), c I*∏ v ∈ I, segmentError σ v ρ) ≤
      (2*Real.sqrt (p-1))^ell*Real.sqrt (∑ I : Finset (BlockSegment B n),
        (c I)^2*(∏ v ∈ I, segmentErrorBound v)^2/segmentTermWeight I) := by
  apply colored_average_bound_supported segmentTermRetained segmentTermWeight c
    (fun I => ∏ v ∈ I, segmentErrorBound v)
    (fun I => (Finset.prod_pos (fun v _ => segmentRetentionWeight_pos v.2)).ne')
    (fun I hI => segment_term_retention_mean I (hblock I hI))
    (fun I ρ => ∏ v ∈ I, segmentError σ v ρ) p (by linarith)
    ((2*Real.sqrt (p-1))^ell) (by positivity)
  exact fun r => fixed_color_segment_chaos H σ r p hp ell c hc

/-- `eq:palindrome-colored` in product-energy form, for an arbitrary
restriction on the selected indices (encoded by setting coefficients to zero).
Each selected block occurs once; no sign assumption on coefficients is needed. -/
theorem palindrome_colored (H : BonamiExternal) (σ : Equiv.Perm (Fin n))
    (p : ℝ) (hp : 2 ≤ p) (ell : ℕ) (c : Finset (BlockSegment B n) → ℝ)
    (hc : ∀ I, I.card≠ell → c I=0)
    (hblock : ∀ I, c I≠0 → Set.InjOn (fun v : BlockSegment B n => v.1) I) :
    finiteLp p (fun ρ : B → Equiv.Perm (Fin n) =>
      ∑ I : Finset (BlockSegment B n), c I*∏ v ∈ I, segmentError σ v ρ) ≤
      (2*Real.sqrt (p-1))^ell*Real.sqrt (∑ I : Finset (BlockSegment B n),
        (c I)^2*∏ v ∈ I, (segmentErrorBound v)^2/segmentRetentionWeight v.2) := by
  simpa only [segmentTermWeight, ← Finset.prod_pow, Finset.prod_div_distrib,
    mul_div_assoc] using colored_segment_chaos H σ p hp ell c hc hblock

end FairDice
