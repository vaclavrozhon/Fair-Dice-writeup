import FairDice.ReflectedBumps

namespace FairDice

open MeasureTheory

variable {ι : Type*} {m K : ℕ}

noncomputable def profileDensity (S : LocalBumpSystem m K) (e : ι → Fin m ↪ Fin K)
    (δ : ι → Fin m → ℝ) (i : ι) (x : ℝ) : ℝ :=
  1+∑ r, δ i r*S.bump (e i r) x

theorem profileDensity_local (S : LocalBumpSystem m K) (e : ι → Fin m ↪ Fin K)
    (δ : ι → Fin m → ℝ) (i : ι) :
    LocallyIntegrable (profileDensity S e δ i) volume := by
  have hs := locallyIntegrable_finsetSum Finset.univ
    (fun r _ => local_const_mul (S.integrableLocal (e i r)) (δ i r))
  have hc : LocallyIntegrable (fun _ : ℝ => (1 : ℝ)) volume :=
    (continuous_const : Continuous (fun _ : ℝ => (1 : ℝ))).locallyIntegrable
  exact hc.add hs

noncomputable def densityPrefix (f : ι → ℝ → ℝ) : List ι → ℝ → ℝ
  | [],_ => 1
  | i::js,t => correctionPrimitive (fun x => densityPrefix f js x*f i x) t

/-- In a reversed prefix list, `a` counts preceding uniform coordinates
and `b` counts following uniform coordinates. -/
def responseTerms : List ι → List (ι × ℕ × ℕ)
  | [] => []
  | i::js => (i,js.length,0)::(responseTerms js).map (fun v => (v.1,v.2.1,v.2.2+1))

theorem responseTerms_data (js : List ι) (v : ι × ℕ × ℕ) (hv : v ∈ responseTerms js) :
    v.1 ∈ js ∧ v.2.1+v.2.2+1=js.length := by
  induction js generalizing v with
  | nil => simp [responseTerms] at hv
  | cons i js ih =>
    simp only [responseTerms,List.mem_cons] at hv
    rcases hv with rfl | hv
    · simp
    · obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hv
      have hh := ih w hw
      exact ⟨List.mem_cons_of_mem _ hh.1,by simp only [List.length_cons]; omega⟩

noncomputable def shiftedResponseSum (S : LocalBumpSystem m K) (e : ι → Fin m ↪ Fin K)
    (δ : ι → Fin m → ℝ) (js : List ι) (h : ℕ) (x : ℝ) : ℝ :=
  ((responseTerms js).map (fun v => ∑ r, δ v.1 r*S.response (e v.1 r) v.2.1 (v.2.2+h) x)).sum

theorem continuous_list_sum {β : Type*} (xs : List β) (f : β → ℝ → ℝ)
    (hf : ∀ b, Continuous (f b)) : Continuous (fun x => (xs.map (fun b => f b x)).sum) := by
  induction xs with
  | nil => simpa using (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ)))
  | cons b xs ih =>
    simp only [List.map_cons,List.sum_cons]
    convert (hf b).add ih using 1
    funext x
    rfl

theorem shiftedResponseSum_continuous (S : LocalBumpSystem m K) (e : ι → Fin m ↪ Fin K)
    (δ : ι → Fin m → ℝ) (js : List ι) (h : ℕ) : Continuous (shiftedResponseSum S e δ js h) := by
  apply continuous_list_sum
  intro v
  exact continuous_finsetSum _ (fun r _ => continuous_const.mul (S.response_continuous _ _ _))

theorem primitive_list_sum {β : Type*} (xs : List β) (f : β → ℝ → ℝ)
    (hf : ∀ b, Continuous (f b)) (t : ℝ) :
    correctionPrimitive (fun x => (xs.map (fun b => f b x)).sum) t =
      (xs.map (fun b => correctionPrimitive (f b) t)).sum := by
  induction xs with
  | nil => simp [correctionPrimitive]
  | cons b xs ih =>
    simp only [List.map_cons,List.sum_cons,correctionPrimitive] at ih ⊢
    rw [intervalIntegral.integral_add ((hf b).intervalIntegrable _ _)
      ((continuous_list_sum xs f hf).intervalIntegrable _ _),ih]

theorem shiftedResponseSum_primitive (S : LocalBumpSystem m K) (e : ι → Fin m ↪ Fin K)
    (δ : ι → Fin m → ℝ) (js : List ι) (h : ℕ) (t : ℝ) :
    correctionPrimitive (shiftedResponseSum S e δ js h) t=shiftedResponseSum S e δ js (h+1) t := by
  unfold shiftedResponseSum
  rw [primitive_list_sum (responseTerms js)
    (fun v x => ∑ r, δ v.1 r*S.response (e v.1 r) v.2.1 (v.2.2+h) x)
    (fun v => continuous_finsetSum _
      (fun r _ => (S.response_continuous _ _ _).const_mul (δ v.1 r))) t]
  apply congrArg List.sum
  apply List.map_congr_left
  intro v _
  unfold correctionPrimitive
  dsimp only
  rw [intervalIntegral.integral_finsetSum
    (f := fun r x => δ v.1 r*S.response (e v.1 r) v.2.1 (v.2.2+h) x)
    (fun r _ => local_interval_integrable (local_const_mul (S.response_local _ _ _) (δ v.1 r)) 0 t)]
  apply Finset.sum_congr rfl
  intro r _
  rw [intervalIntegral.integral_const_mul]
  change δ v.1 r*correctionPrimitive (S.response (e v.1 r) v.2.1 (v.2.2+h)) t=_
  rw [S.response_primitive]
  congr 2

theorem shiftedResponseSum_cons (S : LocalBumpSystem m K) (e : ι → Fin m ↪ Fin K)
    (δ : ι → Fin m → ℝ) (i : ι) (js : List ι) (h : ℕ) (t : ℝ) :
    shiftedResponseSum S e δ (i::js) h t =
      (∑ r, δ i r*S.response (e i r) js.length h t)+shiftedResponseSum S e δ js (h+1) t := by
  simp only [shiftedResponseSum,responseTerms,List.map_cons,List.sum_cons,List.map_map,Nat.zero_add]
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro v _
  apply Finset.sum_congr rfl
  intro r _
  dsimp only
  congr 2
  omega

noncomputable def uniformPrefix (a : ℕ) (t : ℝ) : ℝ := t^a/(a.factorial : ℝ)

theorem uniformPrefix_primitive (a : ℕ) (t : ℝ) :
    correctionPrimitive (uniformPrefix a) t=uniformPrefix (a+1) t := by
  unfold correctionPrimitive uniformPrefix
  rw [intervalIntegral.integral_div,integral_pow]
  simp only [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,zero_pow (by omega : a+1≠0),sub_zero]
  field_simp

/-- The entire multi-bump cross term is pointwise zero, rather than being
assumed as a cancellation hypothesis about order probabilities. -/
theorem shiftedResponseSum_mul_new_bumps [DecidableEq ι]
    (S : LocalBumpSystem m K) (e : ι → Fin m ↪ Fin K) (δ : ι → Fin m → ℝ)
    (he : ∀ i j, i≠j → ∀ r s, e i r≠e j s)
    (js : List ι) (i : ι) (hi : i∉js) (hlen : js.length ≤ m) (x : ℝ) :
    shiftedResponseSum S e δ js 0 x*(∑ r, δ i r*S.bump (e i r) x)=0 := by
  unfold shiftedResponseSum
  rw [← List.sum_map_mul_right]
  apply List.sum_eq_zero
  intro z hz
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hz
  obtain ⟨hvlist,hvlen⟩ := responseTerms_data js v hv
  rw [Finset.sum_mul]
  apply Finset.sum_eq_zero
  intro r _
  rw [Finset.mul_sum]
  apply Finset.sum_eq_zero
  intro s _
  have hvi : v.1≠i := fun h => hi (h ▸ hvlist)
  have hh := S.response_mul_bump (e v.1 r) (e i s) (he _ _ hvi r s)
    v.2.1 (v.2.2+0) (by omega) x
  calc
    _ = (δ v.1 r*δ i s)*(S.response (e v.1 r) v.2.1 (v.2.2+0) x*S.bump (e i s) x) := by ring
    _ = 0 := by rw [hh,mul_zero]

/-- Exact ordered-prefix expansion. Disjoint corrections prevent every
nonlinear interaction; the surviving responses are the actual iterated
Lebesgue integrals. -/
theorem densityPrefix_expansion [DecidableEq ι]
    (S : LocalBumpSystem m K) (e : ι → Fin m ↪ Fin K) (δ : ι → Fin m → ℝ)
    (he : ∀ i j, i≠j → ∀ r s, e i r≠e j s)
    (js : List ι) (hjs : js.Nodup) (hlen : js.length ≤ m) (t : ℝ) :
    densityPrefix (profileDensity S e δ) js t=
      uniformPrefix js.length t+shiftedResponseSum S e δ js 0 t := by
  induction js generalizing t with
  | nil => simp [densityPrefix,uniformPrefix,shiftedResponseSum,responseTerms]
  | cons i js ih =>
    obtain ⟨hi,hjs'⟩ := List.nodup_cons.mp hjs
    have hlen' : js.length ≤ m := by simp only [List.length_cons] at hlen; omega
    have hprod (x : ℝ) : densityPrefix (profileDensity S e δ) js x*profileDensity S e δ i x =
        uniformPrefix js.length x+shiftedResponseSum S e δ js 0 x+
          ∑ r, δ i r*(S.bump (e i r) x*x^js.length/(js.length.factorial : ℝ)) := by
      rw [ih hjs' hlen']
      unfold profileDensity
      have hh := shiftedResponseSum_mul_new_bumps S e δ he js i hi hlen' x
      calc
        _ = uniformPrefix js.length x+shiftedResponseSum S e δ js 0 x+
            uniformPrefix js.length x*(∑ r, δ i r*S.bump (e i r) x)+
              shiftedResponseSum S e δ js 0 x*(∑ r, δ i r*S.bump (e i r) x) := by ring
        _ = _ := by
          rw [hh,add_zero]
          congr 1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro r _
          unfold uniformPrefix
          ring
    simp only [densityPrefix,hprod,correctionPrimitive,List.length_cons]
    have hU : Continuous (uniformPrefix js.length) := by unfold uniformPrefix; fun_prop
    have hE := shiftedResponseSum_continuous S e δ js 0
    have hB : IntervalIntegrable (fun x => ∑ r, δ i r*S.weighted (e i r) js.length x) volume 0 t :=
      local_interval_integrable (locallyIntegrable_finsetSum _ (fun r _ =>
        local_const_mul (S.weighted_local (e i r) js.length) (δ i r))) 0 t
    have hUE : IntervalIntegrable (fun x => uniformPrefix js.length x+shiftedResponseSum S e δ js 0 x) volume 0 t := by
      convert (hU.intervalIntegrable (μ := volume) 0 t).add
        (hE.intervalIntegrable (μ := volume) 0 t) using 1
    change (∫ x in (0 : ℝ)..t, uniformPrefix js.length x+shiftedResponseSum S e δ js 0 x+
      ∑ r, δ i r*S.weighted (e i r) js.length x)=_
    rw [intervalIntegral.integral_add hUE hB,
      intervalIntegral.integral_add (hU.intervalIntegrable 0 t) (hE.intervalIntegrable 0 t)]
    change correctionPrimitive (uniformPrefix js.length) t+
      correctionPrimitive (shiftedResponseSum S e δ js 0) t+
        (∫ x in (0 : ℝ)..t, ∑ r, δ i r*S.weighted (e i r) js.length x)=_
    rw [uniformPrefix_primitive,shiftedResponseSum_primitive,shiftedResponseSum_cons]
    rw [intervalIntegral.integral_finsetSum (f := fun r x => δ i r*S.weighted (e i r) js.length x)
      (fun r _ => local_interval_integrable
        (local_const_mul (S.weighted_local (e i r) js.length) (δ i r)) 0 t)]
    simp_rw [intervalIntegral.integral_const_mul]
    change uniformPrefix (js.length+1) t+shiftedResponseSum S e δ js 1 t+
      (∑ r, δ i r*S.response (e i r) js.length 0 t)=_
    ring

end FairDice
