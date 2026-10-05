import FairDice.PrefixResponse
import FairDice.OrderKernels

namespace FairDice

open Polynomial

noncomputable def CorrectedFamily.density {m K : ℕ} (C : CorrectedFamily m K) :=
  profileDensity C.bumpSystem C.selection
    (fun i => densityCoefficients (C.selection i) (fun q => (C.node q : ℝ)))

noncomputable def CorrectedFamily.coefficient {m K : ℕ} (C : CorrectedFamily m K)
    (i : Fin m) (q : Fin K) :=
  nodalDensityCoefficient C.selection
    (fun i => densityCoefficients (C.selection i) (fun q => (C.node q : ℝ))) i q

theorem CorrectedFamily.coefficient_moment {m K : ℕ} (C : CorrectedFamily m K)
    (i : Fin m) (p : ℝ[X]) :
    (∑ q, C.coefficient i q*p.eval (C.node q : ℝ))/(K : ℝ)=
      densityMomentFunctional (C.selection i) (fun q => (C.node q : ℝ)) p := by
  classical
  rw [densityMomentFunctional_apply]
  congr 1
  unfold coefficient nodalDensityCoefficient
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  simp only [ite_mul,zero_mul]
  simp

noncomputable def CorrectedFamily.neighborMoment {m K : ℕ} (C : CorrectedFamily m K)
    (js : List (Fin m)) (p : ℝ[X]) : ℝ :=
  match js with
  | [] => 0
  | i::_ => densityMomentFunctional (C.selection i) (fun q => (C.node q : ℝ)) p

/-- The left list is reversed; the right list is in chronological order.
Both factors are literal iterated integrals of the corrected densities. -/
noncomputable def CorrectedFamily.conditionalOrder {m K : ℕ} (C : CorrectedFamily m K)
    (L R : List (Fin m)) (q : Fin K) : ℝ :=
  densityPrefix C.density L (C.node q : ℝ)*
    densityPrefix (fun i x => C.density i (1-x)) R (1-(C.node q : ℝ))

theorem CorrectedFamily.prefix_node {m K : ℕ} (C : CorrectedFamily m K)
    (i : Fin m) (js : List (Fin m)) (hnd : (i::js).Nodup)
    (hlen : js.length+1 ≤ m) (q : Fin K) :
    densityPrefix C.density (i::js) (C.node q : ℝ)=
      uniformPrefix (js.length+1) (C.node q : ℝ)+
        C.coefficient i q*uniformPrefix js.length (C.node q : ℝ) := by
  have h := densityPrefix_at_node C.bumpSystem C.selection
    (fun i => densityCoefficients (C.selection i) (fun q => (C.node q : ℝ)))
    C.selection_disjoint i js hnd hlen q
  change densityPrefix C.density (i::js) (C.node q : ℝ)=
    uniformPrefix (js.length+1) (C.node q : ℝ)+
      C.coefficient i q*(1*uniformPrefix js.length (C.node q : ℝ)) at h
  simpa only [one_mul] using h

theorem CorrectedFamily.suffix_node {m K : ℕ} (C : CorrectedFamily m K)
    (i : Fin m) (js : List (Fin m)) (hnd : (i::js).Nodup)
    (hlen : js.length+1 ≤ m) (q : Fin K) :
    densityPrefix (fun i x => C.density i (1-x)) (i::js) (1-(C.node q : ℝ))=
      uniformPrefix (js.length+1) (1-(C.node q : ℝ))-
        C.coefficient i q*uniformPrefix js.length (1-(C.node q : ℝ)) := by
  have h := densityPrefix_at_node C.bumpSystem.reflect C.selection
    (fun i => densityCoefficients (C.selection i) (fun q => (C.node q : ℝ)))
    C.selection_disjoint i js hnd hlen q
  change densityPrefix (fun i x => C.density i (1-x)) (i::js) (1-(C.node q : ℝ))=
    uniformPrefix (js.length+1) (1-(C.node q : ℝ))+
      C.coefficient i q*((-1)*uniformPrefix js.length (1-(C.node q : ℝ))) at h
  simpa only [neg_one_mul,mul_neg,← sub_eq_add_neg] using h

theorem CorrectedFamily.order_response {m K : ℕ} (C : CorrectedFamily m K)
    (L R : List (Fin m)) (hnd : (L++R).Nodup) (hlen : L.length+R.length ≤ m) :
    (∑ q, C.conditionalOrder L R q)/(K : ℝ)=
      (∑ q, (orderKernel L.length R.length).eval (C.node q : ℝ))/(K : ℝ)+
        C.neighborMoment L (orderKernel (L.length-1) R.length)-
        C.neighborMoment R (orderKernel L.length (R.length-1)) := by
  classical
  let δ := fun i => densityCoefficients (C.selection i) (fun q => (C.node q : ℝ))
  have hpoint (q : Fin K) : C.conditionalOrder L R q=
      (orderKernel L.length R.length).eval (C.node q : ℝ)+
      (match L with
        | [] => 0
        | i::_ => C.coefficient i q*(orderKernel (L.length-1) R.length).eval (C.node q : ℝ))-
      (match R with
        | [] => 0
        | j::_ => C.coefficient j q*(orderKernel L.length (R.length-1)).eval (C.node q : ℝ)) := by
    unfold conditionalOrder
    cases L with
    | nil =>
      cases R with
      | nil => simp [densityPrefix,orderKernel_eval]
      | cons j R =>
        rw [C.suffix_node j R (by simpa using hnd) (by simpa using hlen) q]
        simp only [densityPrefix,List.length_nil,List.length_cons,
          Nat.add_sub_cancel_right,one_mul]
        simp only [orderKernel_eval,uniformPrefix,pow_zero,Nat.factorial_zero,Nat.cast_one,one_mul]
        ring
    | cons i L =>
      rw [C.prefix_node i L hnd.of_append_left (by simp only [List.length_cons] at hlen; omega) q]
      cases R with
      | nil =>
        simp only [densityPrefix,List.length_cons,List.length_nil,Nat.add_sub_cancel_right,
          mul_one,sub_zero]
        simp only [orderKernel_eval,uniformPrefix,pow_zero,Nat.factorial_zero,Nat.cast_one,mul_one]
      | cons j R =>
        rw [C.suffix_node j R hnd.of_append_right (by simp only [List.length_cons] at hlen; omega) q]
        have hij : i≠j := by
          intro hij
          have hh := (List.nodup_cons.mp hnd).1
          apply hh
          simp [hij]
        have hz : C.coefficient i q*C.coefficient j q=0 :=
          nodalDensityCoefficient_mul C.selection δ C.selection_disjoint i j hij q
        simp only [List.length_cons,Nat.add_sub_cancel_right]
        change (uniformPrefix (L.length+1) (C.node q : ℝ)+
          C.coefficient i q*uniformPrefix L.length (C.node q : ℝ))*
          (uniformPrefix (R.length+1) (1-(C.node q : ℝ))-
          C.coefficient j q*uniformPrefix R.length (1-(C.node q : ℝ)))=_
        simp only [orderKernel_eval,uniformPrefix]
        calc
          _ = (C.node q : ℝ)^(L.length+1)*(1-(C.node q : ℝ))^(R.length+1)/
                ((L.length+1).factorial*(R.length+1).factorial : ℝ)+
              C.coefficient i q*((C.node q : ℝ)^L.length*(1-(C.node q : ℝ))^(R.length+1)/
                (L.length.factorial*(R.length+1).factorial : ℝ))-
              C.coefficient j q*((C.node q : ℝ)^(L.length+1)*(1-(C.node q : ℝ))^R.length/
                ((L.length+1).factorial*R.length.factorial : ℝ))-
              (C.coefficient i q*C.coefficient j q)*
                ((C.node q : ℝ)^L.length*(1-(C.node q : ℝ))^R.length/
                  (L.length.factorial*R.length.factorial : ℝ)) := by ring
          _ = _ := by rw [hz]; ring
  simp_rw [hpoint]
  rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,sub_div,add_div]
  congr 2
  · cases L with
    | nil => simp [neighborMoment]
    | cons i L => exact C.coefficient_moment i _
  · cases R with
    | nil => simp [neighborMoment]
    | cons i R => exact C.coefficient_moment i _

/-- Complete repaired full-order law. No order-response hypothesis remains. -/
theorem CorrectedFamily.uniform_order {m K : ℕ} (C : CorrectedFamily m K) (hm : 0 < m)
    (L R : List (Fin m)) (hnd : (L++R).Nodup) (hlen : L.length+R.length=m) :
    (∑ q, C.conditionalOrder L R q)/(K : ℝ)=1/((m+1).factorial : ℝ) := by
  classical
  let j₀ : Fin m := ⟨0,hm⟩
  let T := densityMomentFunctional (C.selection j₀) (fun q => (C.node q : ℝ))
  have hleft : C.neighborMoment L (orderKernel (L.length-1) R.length)=
      T (if L.length=0 then 0 else orderKernel (L.length-1) R.length) := by
    cases L with
    | nil => simp [neighborMoment,T]
    | cons i L =>
      simp only [neighborMoment,List.length_cons,Nat.add_sub_cancel_right,
        if_neg (by omega : L.length+1≠0)]
      have hh : L.length+R.length < m := by simp only [List.length_cons] at hlen; omega
      exact C.common_functional i j₀ _ ((orderKernel_degree L.length R.length).trans_lt hh)
  have hright : C.neighborMoment R (orderKernel L.length (R.length-1))=
      T (if R.length=0 then 0 else orderKernel L.length (R.length-1)) := by
    cases R with
    | nil => simp [neighborMoment,T]
    | cons i R =>
      simp only [neighborMoment,List.length_cons,Nat.add_sub_cancel_right,
        if_neg (by omega : R.length+1≠0)]
      have hh : L.length+R.length < m := by simp only [List.length_cons] at hlen; omega
      exact C.common_functional i j₀ _ ((orderKernel_degree L.length R.length).trans_lt hh)
  rw [C.order_response L R hnd hlen.le,hleft,hright]
  have hrepair := C.repaired_moments j₀ (orderKernel L.length R.length)
    ((orderKernel_degree _ _).trans hlen.le)
  change T (orderKernel L.length R.length).derivative=_ at hrepair
  rw [orderKernel_derivative,map_sub] at hrepair
  rw [add_sub_assoc,hrepair,orderKernel_integral,hlen]
  ring

end FairDice
