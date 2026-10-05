import FairDice.IteratedIntegrals

namespace FairDice

open MeasureTheory Set

theorem integral_shifted_power (a t : ℝ) (k : ℕ) :
    (∫ x in a..t, (x-a)^k)=(t-a)^(k+1)/(k+1 : ℝ) := by
  rw [intervalIntegral.integral_comp_sub_right (fun x : ℝ => x^k) a,integral_pow]
  simp

/-- A constant-density cell has the uniform conditional order law, for
every sublist; endpoints do not affect its Lebesgue integral. -/
theorem densityPrefixFrom_constant {ι : Type*} (f : ι → ℝ → ℝ) (c : ι → ℝ)
    (a b : ℝ) (hconst : ∀ i x, x ∈ Ioo a b → f i x=c i) (js : List ι)
    (hab : a ≤ b) :
    densityPrefixFrom f a js b=(b-a)^js.length*(js.map c).prod/(js.length.factorial : ℝ) := by
  have hall : ∀ (us : List ι) (t : ℝ), t ∈ Icc a b →
      densityPrefixFrom f a us t=(t-a)^us.length*(us.map c).prod/(us.length.factorial : ℝ) := by
    intro us
    induction us with
    | nil => intro t ht; simp [densityPrefixFrom]
    | cons i us ih =>
      intro t ht
      have he : (∫ x in a..t, densityPrefixFrom f a us x*f i x)=
          ∫ x in a..t, ((us.map c).prod*c i/(us.length.factorial : ℝ))*(x-a)^us.length := by
        apply intervalIntegral.integral_congr_Ioo_of_le ht.1
        intro x hx
        dsimp only
        rw [ih x ⟨hx.1.le,hx.2.le.trans ht.2⟩,hconst i x ⟨hx.1,hx.2.trans_le ht.2⟩]
        ring
      simp only [densityPrefixFrom,he,intervalIntegral.integral_const_mul,integral_shifted_power,
        List.length_cons,List.map_cons,List.prod_cons,Nat.factorial_succ,Nat.cast_mul]
      push_cast
      field_simp
  exact hall js b ⟨hab,le_rfl⟩

end FairDice
