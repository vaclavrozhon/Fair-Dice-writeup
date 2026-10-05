import FairDice.ApproximateThreshold

namespace FairDice

theorem palindromeMomentScale_nonneg {n m p : ℝ} (hn : 0 ≤ n) (hm : 0 ≤ m) :
    0 ≤ palindromeMomentScale n m p := by unfold palindromeMomentScale; positivity

theorem palindromeMomentScale_square {n m p : ℝ} (hn : 0 ≤ n) (hm : 0 ≤ m) (hp : 0 ≤ p) :
    (palindromeMomentScale n m p)^2=n^(11/2 : ℝ)*p/m^5 := by
  have hn' := Real.rpow_mul hn (11/4 : ℝ) 2
  have hm' := Real.rpow_mul hm (5/2 : ℝ) 2
  norm_num at hn' hm'
  unfold palindromeMomentScale
  rw [div_pow,mul_pow,Real.sq_sqrt hp,← hn',← hm']

theorem palindrome_scale_small {n m p : ℝ} (hn : 0 < n) (hp : 0 < p)
    (hm : 8*n^(11/10 : ℝ)*p^(1/5 : ℝ) ≤ m) :
    palindromeMomentScale n m p ≤ 1/160 := by
  have hth : 0 < 8*n^(11/10 : ℝ)*p^(1/5 : ℝ) := by positivity
  have hm0 : 0 < m := hth.trans_le hm
  have hh := Real.rpow_le_rpow hth.le hm (by norm_num : (0 : ℝ) ≤ 5/2)
  have he : (8*n^(11/10 : ℝ)*p^(1/5 : ℝ))^(5/2 : ℝ) =
      (8 : ℝ)^(5/2 : ℝ)*n^(11/4 : ℝ)*Real.sqrt p := by
    rw [Real.mul_rpow (by positivity) (by positivity),Real.mul_rpow (by norm_num) (by positivity),
      ← Real.rpow_mul hn.le,← Real.rpow_mul hp.le]
    norm_num
    rw [← Real.sqrt_eq_rpow]
    ring
    simp
  rw [he] at hh
  have hc : (160 : ℝ) ≤ (8 : ℝ)^(5/2 : ℝ) := by
    rw [show (5/2 : ℝ)=2+1/2 by norm_num,Real.rpow_add (by norm_num),
      Real.rpow_two,← Real.sqrt_eq_rpow]
    norm_num
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 8),Real.sqrt_nonneg (8 : ℝ)]
  have hh' := mul_le_mul_of_nonneg_right hc
    (show 0 ≤ n^(11/4 : ℝ)*Real.sqrt p by positivity)
  unfold palindromeMomentScale
  apply (div_le_iff₀ (Real.rpow_pos_of_pos hm0 (5/2))).mpr
  nlinarith

/-- The moment threshold implies both the ratio lower bound and the
quantitative exponential margin used in the long-support calculation. -/
theorem palindrome_ratio_threshold {n m p : ℝ} (hn : 1 ≤ n) (hp : 1 ≤ p)
    (hpn : p ≤ n^2) (hm : 8*n^(11/10 : ℝ)*p^(1/5 : ℝ) ≤ m) :
    8 ≤ m/n ∧ 4*p/(m/n)^4 ≤ 1/1024 := by
  have hn0 : 0 < n := lt_of_lt_of_le (by norm_num) hn
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have he : n^(11/10 : ℝ)=n*n^(1/10 : ℝ) := by
    rw [show (11/10 : ℝ)=1+1/10 by norm_num,Real.rpow_add hn0,Real.rpow_one]
  have ht : 8*n^(1/10 : ℝ)*p^(1/5 : ℝ) ≤ m/n := by
    apply (le_div_iff₀ hn0).mpr
    rw [he] at hm
    nlinarith
  have hn1 : 1 ≤ n^(1/10 : ℝ) := Real.one_le_rpow hn (by norm_num)
  have hp1 : 1 ≤ p^(1/5 : ℝ) := Real.one_le_rpow hp (by norm_num)
  have ht8 : 8 ≤ m/n := by
    nlinarith [mul_le_mul hn1 hp1 (by norm_num : (0 : ℝ) ≤ 1) (by positivity)]
  refine ⟨ht8,?_⟩
  have h4 := pow_le_pow_left₀ (by positivity : 0 ≤ 8*n^(1/10 : ℝ)*p^(1/5 : ℝ)) ht 4
  have hn4 := Real.rpow_mul hn0.le (1/10 : ℝ) 4
  have hp4 := Real.rpow_mul hp0.le (1/5 : ℝ) 4
  norm_num at hn4 hp4
  simp only [mul_pow] at h4
  rw [← hn4,← hp4] at h4
  norm_num at h4
  have hpcomp := Real.rpow_le_rpow hp0.le hpn (by norm_num : (0 : ℝ) ≤ 1/5)
  have hncomp := Real.rpow_mul hn0.le 2 (1/5 : ℝ)
  norm_num at hncomp
  rw [← hncomp] at hpcomp
  have hpfull : p^(1/5 : ℝ)*p^(4/5 : ℝ)=p := by rw [← Real.rpow_add hp0]; norm_num
  have hpbound := mul_le_mul_of_nonneg_right hpcomp (Real.rpow_nonneg hp0.le (4/5))
  rw [hpfull] at hpbound
  have ht0 : 0 < m/n := lt_of_lt_of_le (by norm_num) ht8
  apply (div_le_iff₀ (pow_pos ht0 4)).mpr
  nlinarith

theorem palindrome_ratio_scale {n m p : ℝ} (hn : 0 < n) (hm : 0 < m) :
    palindromeMomentScale n m p=n^(1/4 : ℝ)*Real.sqrt p*(m/n)^(-5/2 : ℝ) := by
  rw [show (-5/2 : ℝ)=-(5/2) by ring,Real.div_rpow hm.le hn.le,
    Real.rpow_neg hm.le,Real.rpow_neg hn.le]
  have hn' : n^(11/4 : ℝ)=n^(1/4 : ℝ)*n^(5/2 : ℝ) := by
    rw [← Real.rpow_add hn]; norm_num
  unfold palindromeMomentScale
  rw [hn']
  field_simp

end FairDice
