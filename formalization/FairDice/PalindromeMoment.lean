import FairDice.RestrictedMoments
import FairDice.MomentArithmetic

namespace FairDice

theorem shortChaosScale_eq {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    {p : ℝ} (hp : 0 ≤ p) :
    shortChaosScale n m p=2*Real.sqrt 160*palindromeMomentScale n m p := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hn6 : (n : ℝ)^6=(n : ℝ)^(11/2 : ℝ)*Real.sqrt n := by
    rw [Real.sqrt_eq_rpow,← Real.rpow_add hn0]
    norm_num
  have hs : (shortChaosScale n m p)^2=
      (2*Real.sqrt 160*palindromeMomentScale n m p)^2 := by
    unfold shortChaosScale
    rw [mul_pow,mul_pow,Real.sq_sqrt hp,Real.sq_sqrt (by positivity),
      mul_pow,mul_pow,Real.sq_sqrt (by norm_num),palindromeMomentScale_square hn0.le hm0.le hp]
    field_simp [ne_of_gt hm0,ne_of_gt (Real.sqrt_pos.mpr hn0)]
    rw [hn6]
    ring
  have hleft : 0 ≤ shortChaosScale n m p := by unfold shortChaosScale; positivity
  have hright : 0 ≤ 2*Real.sqrt 160*palindromeMomentScale n m p :=
    mul_nonneg (by positivity) (palindromeMomentScale_nonneg hn0.le hm0.le)
  nlinarith

theorem globalChaosScale_eq {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    {p : ℝ} (hp : 0 ≤ p) :
    globalChaosScale n m p=2*(n : ℝ)^(1/4 : ℝ)*palindromeMomentScale n m p := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hq := Real.rpow_mul hn0.le (1/4 : ℝ) 2
  norm_num at hq
  have hn6 : (n : ℝ)^(1/2 : ℝ)*(n : ℝ)^(11/2 : ℝ)=(n : ℝ)^6 := by
    rw [← Real.rpow_add hn0]; norm_num
  have hs : (globalChaosScale n m p)^2=
      (2*(n : ℝ)^(1/4 : ℝ)*palindromeMomentScale n m p)^2 := by
    unfold globalChaosScale
    rw [mul_pow,mul_pow,Real.sq_sqrt hp,Real.sq_sqrt (by positivity),
      mul_pow,mul_pow,← hq,palindromeMomentScale_square hn0.le hm0.le hp]
    rw [← hn6]
    ring
  have hleft : 0 ≤ globalChaosScale n m p := by unfold globalChaosScale; positivity
  have hright : 0 ≤ 2*(n : ℝ)^(1/4 : ℝ)*palindromeMomentScale n m p :=
    mul_nonneg (by positivity) (palindromeMomentScale_nonneg hn0.le hm0.le)
  nlinarith

/-- The chosen tilt has exactly the scalar energy asserted in the article. -/
theorem palindrome_tilt_calculation {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    {p : ℝ} (hp : 0 ≤ p) (ht : 1 ≤ (m : ℝ)/n) :
    let t := (m : ℝ)/n
    let θ := t^(1/3 : ℝ)
    1 ≤ θ ∧ θ*(n : ℝ)^2/(2*(m : ℝ)^2) ≤ 1/2 ∧
      (tiltedChaosScale n m p θ)^2=4*p*n/t^4 := by
  dsimp only
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  let t : ℝ := (m : ℝ)/n
  let θ : ℝ := t^(1/3 : ℝ)
  have ht0 : 0 < t := div_pos hm0 hn0
  have hθ : 1 ≤ θ := Real.one_le_rpow ht (by norm_num)
  have hθ3 : θ^3=t := by
    dsimp [θ]
    rw [← Real.rpow_natCast,← Real.rpow_mul ht0.le]
    norm_num
  have hθ2 : θ ≤ t^2 := by
    dsimp [θ]
    simpa using Real.rpow_le_rpow_of_exponent_le ht (by norm_num : (1/3 : ℝ) ≤ 2)
  have hz : θ*(n : ℝ)^2/(2*(m : ℝ)^2)=θ/(2*t^2) := by
    dsimp [t]; field_simp
  refine ⟨hθ,?_,?_⟩
  · rw [hz]
    apply (div_le_iff₀ (by positivity : (0 : ℝ)<2*t^2)).mpr
    linarith
  · unfold tiltedChaosScale
    rw [mul_pow,mul_pow,Real.sq_sqrt hp,Real.sq_sqrt (by positivity),hz,div_pow,hθ3]
    dsimp [t]
    field_simp
    ring

/-- The exponential long-support bound is at most one moment scale once
the alphabet has at least sixty letters. -/
theorem palindrome_long_scalar {n m : ℕ} (hn : 60 ≤ n) (hm : 0 < m)
    {p : ℝ} (hp : 2 ≤ p) (ht8 : 8 ≤ (m : ℝ)/n)
    (hmargin : 4*p/((m : ℝ)/n)^4 ≤ 1/1024) :
    Real.sqrt 2*(((m : ℝ)/n)^(1/3 : ℝ))^(-(n : ℝ)/4)*
      Real.exp ((tiltedChaosScale n m p (((m : ℝ)/n)^(1/3 : ℝ)))^2) ≤
        palindromeMomentScale n m p := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  let t : ℝ := (m : ℝ)/n
  have ht0 : 0 < t := div_pos hm0 hn0
  have ht1 : 1 ≤ t := by dsimp [t]; linarith
  have hcalc := (palindrome_tilt_calculation (by omega : 0<n) hm (by linarith : 0 ≤ p) ht1).2.2
  have hlog : 1/2 ≤ Real.log t := by
    have hh := Real.one_sub_inv_le_log_of_pos ht0
    have hi : t⁻¹ ≤ 1/2 := by
      rw [← one_div]
      apply (div_le_iff₀ ht0).mpr
      dsimp [t]; linarith
    linarith
  have hA : 4*p*n/t^4 ≤ (n : ℝ)*Real.log t/24 := by
    have hh := mul_le_mul_of_nonneg_right hmargin hn0.le
    change (4*p/t^4)*(n : ℝ) ≤ (1/1024)*(n : ℝ) at hh
    have hl := mul_le_mul_of_nonneg_left hlog hn0.le
    rw [div_mul_eq_mul_div] at hh
    nlinarith
  have he : Real.sqrt 2*(t^(1/3 : ℝ))^(-(n : ℝ)/4)*
      Real.exp (4*p*n/t^4)=Real.sqrt 2*Real.exp (-(n : ℝ)/12*Real.log t+4*p*n/t^4) := by
    rw [← Real.rpow_mul ht0.le,show (1/3 : ℝ)*(-(n : ℝ)/4)=-(n : ℝ)/12 by ring,
      Real.rpow_def_of_pos ht0,
      show Real.log t*(-(n : ℝ)/12)=-(n : ℝ)/12*Real.log t by ring,Real.exp_add]
    ring
  rw [hcalc]
  change Real.sqrt 2*(t^(1/3 : ℝ))^(-(n : ℝ)/4)*Real.exp (4*p*n/t^4) ≤ _
  rw [he]
  calc
    _ ≤ Real.sqrt 2*Real.exp (-(n : ℝ)/24*Real.log t) := by
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by linarith)) (by positivity)
    _ = Real.sqrt 2*t^(-(n : ℝ)/24) := by rw [Real.rpow_def_of_pos ht0]; congr 2; ring
    _ ≤ Real.sqrt 2*t^(-5/2 : ℝ) := by
      apply mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le ht1 _) (by positivity)
      have hn60 : (60 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    _ ≤ (n : ℝ)^(1/4 : ℝ)*Real.sqrt p*t^(-5/2 : ℝ) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have hn1 : 1 ≤ (n : ℝ)^(1/4 : ℝ) := Real.one_le_rpow (by exact_mod_cast (by omega : 1≤n)) (by norm_num)
      have hp' := Real.sqrt_le_sqrt hp
      nlinarith [Real.sqrt_nonneg p,Real.sqrt_nonneg (2 : ℝ)]
    _ = _ := (palindrome_ratio_scale hn0 hm0).symm

/-- The uniform moment estimate of the article for the actual palindrome
word. Only classical Bonami hypercontractivity and the two scalar Poisson
estimates remain external; no word-specific moment estimate is assumed. -/
theorem palindrome_uniform_moment {n m : ℕ} (B : BonamiExternal) (H : PoissonEstimates)
    (hn : 3 ≤ n) (p : ℝ) (hp : 2 ≤ p) (hpn : p ≤ (n : ℝ)^2)
    (hm : 8*(n : ℝ)^(11/10 : ℝ)*p^(1/5 : ℝ) ≤ m)
    (σ : Equiv.Perm (Fin n)) :
    finiteLp p (fun ρ : Fin m → Equiv.Perm (Fin n) => palindromeRelativeError ρ σ) ≤
      32*palindromeMomentScale n m p := by
  have hnNat : 0 < n := by omega
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hnNat
  have hp0 : 0 < p := by linarith
  have hratio := palindrome_ratio_threshold (by exact_mod_cast (by omega : 1≤n))
    (by linarith : 1≤p) hpn hm
  have hnmR : (n : ℝ) ≤ m := by
    have hh := (le_div_iff₀ hn0).mp hratio.1
    linarith
  have hnm : n ≤ m := by exact_mod_cast hnmR
  have hmNat : 0 < m := by omega
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hmNat
  have hscale := palindrome_scale_small hn0 hp0 hm
  have hscale0 := palindromeMomentScale_nonneg hn0.le hm0.le (p := p)
  by_cases hnsmall : n < 60
  · have hnquarter : (n : ℝ)^(1/4 : ℝ) ≤ 3 := by
      have hh := Real.rpow_le_rpow hn0.le (show (n : ℝ) ≤ 81 by exact_mod_cast (by omega : n≤81))
        (by norm_num : (0 : ℝ) ≤ 1/4)
      have h81 : (81 : ℝ)^(1/4 : ℝ)=3 := by
        rw [show (81 : ℝ)=(3 : ℝ)^4 by norm_num,
          ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 3)]
        norm_num
      rwa [h81] at hh
    have hb : globalChaosScale n m p ≤ 6*palindromeMomentScale n m p := by
      rw [globalChaosScale_eq hnNat hmNat hp0.le]
      nlinarith
    have hb0 : 0 ≤ globalChaosScale n m p := by unfold globalChaosScale; positivity
    have hbquarter : globalChaosScale n m p ≤ 1/4 := by linarith
    have hnorm := palindrome_global_norm B σ p hp hmNat hnm (by linarith)
    apply hnorm.trans
    have hgeom : globalChaosScale n m p/(1-globalChaosScale n m p) ≤
        (4/3)*globalChaosScale n m p := by
      apply (div_le_iff₀ (by linarith : 0 < 1-globalChaosScale n m p)).mpr
      nlinarith
    linarith
  · have hnlarge : 60 ≤ n := by omega
    have haeq := shortChaosScale_eq hnNat hmNat hp0.le
    have ha0 : 0 ≤ shortChaosScale n m p := by unfold shortChaosScale; positivity
    have hsqrt : Real.sqrt 160 ≤ 40/3 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 160),Real.sqrt_nonneg (160 : ℝ)]
    have ha : shortChaosScale n m p ≤ 1/6 := by
      rw [haeq]
      have hh := mul_le_mul_of_nonneg_left hscale (show 0 ≤ 2*Real.sqrt 160 by positivity)
      nlinarith
    let θ := ((m : ℝ)/n)^(1/3 : ℝ)
    have htilt := palindrome_tilt_calculation hnNat hmNat hp0.le (by linarith : 1 ≤ (m : ℝ)/n)
    have hnorm := palindrome_short_long_norm B H σ p hp hmNat hnm (by linarith) θ htilt.1 htilt.2.1
    have hlong := palindrome_long_scalar hnlarge hmNat hp hratio.1 hratio.2
    have hgeom : shortChaosScale n m p/(1-shortChaosScale n m p) ≤ (6/5)*shortChaosScale n m p := by
      apply (div_le_iff₀ (by linarith : 0 < 1-shortChaosScale n m p)).mpr
      nlinarith
    have hsqrt' : (12/5)*Real.sqrt 160+1 ≤ (32 : ℝ) := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 160),Real.sqrt_nonneg (160 : ℝ)]
    apply hnorm.trans
    have hh := mul_le_mul_of_nonneg_right hsqrt' hscale0
    rw [haeq] at hgeom
    dsimp [θ] at hnorm ⊢
    rw [haeq]
    linarith

/-- The new random-palindrome approximation theorem, with the explicit
face threshold and success probability at least one half. -/
theorem palindrome_approximate {n m : ℕ} (B : BonamiExternal) (H : PoissonEstimates)
    {ε : ℝ} (hn : 3 ≤ n) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hm : 16*(n : ℝ)^(13/10 : ℝ)*(Real.log n)^(1/5 : ℝ)*ε^(-2/5 : ℝ) ≤ m) :
    finiteEventMass (fun ρ : Fin m → Equiv.Perm (Fin n) =>
      ∃ σ : Equiv.Perm (Fin n), ε ≤ |palindromeRelativeError ρ σ|) ≤ 1/2 ∧
    ∃ ρ : Fin m → Equiv.Perm (Fin n), ∀ q : List (Fin n), q.Nodup → q.length=n →
      |(patternProbability (palindromeWord ρ) q : ℝ)-1/(n.factorial : ℝ)| ≤ ε/(n.factorial : ℝ) :=
  palindrome_approximate_from_uniform_moment hn hε hε1 hm
    (fun p hp hpn hm σ => palindrome_uniform_moment B H hn p hp hpn hm σ)

end FairDice
