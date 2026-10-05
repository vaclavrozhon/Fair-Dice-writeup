import FairDice.PrefixOrder

namespace FairDice

open MeasureTheory Set

variable {ι : Type*}

noncomputable def densityPrefixFrom (f : ι → ℝ → ℝ) (a : ℝ) : List ι → ℝ → ℝ
  | [],_ => 1
  | i::js,t => ∫ x in a..t, densityPrefixFrom f a js x*f i x

theorem densityPrefixFrom_continuous (f : ι → ℝ → ℝ)
    (hf : ∀ i, LocallyIntegrable (f i) volume) (a : ℝ) (js : List ι) :
    Continuous (densityPrefixFrom f a js) := by
  induction js with
  | nil => exact continuous_const
  | cons i js ih =>
    have hi : LocallyIntegrable (fun x => densityPrefixFrom f a js x*f i x) volume := by
      convert local_mul_continuous (hf i) ih using 1
      funext x
      ring
    exact intervalIntegral.continuous_primitive (local_interval_integrable hi) a

theorem densityPrefixFrom_zero (f : ι → ℝ → ℝ) (js : List ι) (t : ℝ) :
    densityPrefixFrom f 0 js t=densityPrefix f js t := by
  induction js generalizing t with
  | nil => rfl
  | cons i js ih => simp only [densityPrefixFrom,densityPrefix,correctionPrimitive,ih]

/-- Splitting a strict ordered integral at any boundary. This is the exact
continuous counterpart of the cut identity for counts in concatenated words. -/
theorem densityPrefixFrom_split (f : ι → ℝ → ℝ)
    (hf : ∀ i, LocallyIntegrable (f i) volume) (js : List ι) (a b c : ℝ) :
    densityPrefixFrom f a js c=
      ∑ k ∈ Finset.range (js.length+1),
        densityPrefixFrom f a (js.drop k) b*densityPrefixFrom f b (js.take k) c := by
  induction js generalizing c with
  | nil => simp [densityPrefixFrom]
  | cons i js ih =>
    have hint (a : ℝ) (us : List ι) :
        LocallyIntegrable (fun x => densityPrefixFrom f a us x*f i x) volume := by
      convert local_mul_continuous (hf i) (densityPrefixFrom_continuous f hf a us) using 1
      funext x
      ring
    have hsum (x : ℝ) : densityPrefixFrom f a js x*f i x=
        ∑ k ∈ Finset.range (js.length+1), densityPrefixFrom f a (js.drop k) b*
          (densityPrefixFrom f b (js.take k) x*f i x) := by
      rw [ih,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      ring
    have hbc : (∫ x in b..c, densityPrefixFrom f a js x*f i x)=
        ∑ k ∈ Finset.range (js.length+1), densityPrefixFrom f a (js.drop k) b*
          densityPrefixFrom f b (i::js.take k) c := by
      simp_rw [hsum]
      rw [intervalIntegral.integral_finsetSum (f := fun k x =>
        densityPrefixFrom f a (js.drop k) b*(densityPrefixFrom f b (js.take k) x*f i x))
        (fun k _ => local_interval_integrable
          (local_const_mul (hint b (js.take k)) _) b c)]
      simp_rw [intervalIntegral.integral_const_mul]
      rfl
    calc
      _ = densityPrefixFrom f a (i::js) b+
          (∫ x in b..c, densityPrefixFrom f a js x*f i x) :=
        (intervalIntegral.integral_add_adjacent_intervals
          (local_interval_integrable (hint a js) a b)
          (local_interval_integrable (hint a js) b c)).symm
      _ = densityPrefixFrom f a (i::js) b+
          ∑ k ∈ Finset.range (js.length+1), densityPrefixFrom f a (js.drop k) b*
            densityPrefixFrom f b (i::js.take k) c := by rw [hbc]
      _ = _ := by
        conv_rhs => rw [List.length_cons,Finset.sum_range_succ']
        simp only [List.drop_zero,List.take_zero,List.drop_succ_cons,List.take_succ_cons,
          densityPrefixFrom,mul_one]
        rw [add_comm]

end FairDice
