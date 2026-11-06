module

public import PaperP1.Arithmetic.PrimeLogMertens
public import PaperP1.Arithmetic.RealTripleConvolution
public import PaperP1.PNT.LogGrowth

/-! # Actual logarithmic prime bands and uniform negligible triple-convolution error -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimeLogDiameter
open Finset Nat PaperP1 Filter
open scoped Classical Topology

def mass (S : Finset ℕ) : ℝ := ∑ p ∈ S, Real.log (p : ℝ)/(p : ℝ)

def constant : ℝ := 2*(Real.log 4+PrimeLogMertens.primePowerTotal+5)+1

theorem constant_pos : 0 < constant := by
  have hh := PrimeLogMertens.primePowerTotal_nonneg
  have hl : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
  dsimp only [constant]
  linarith

theorem coefficient_nonneg (n : ℕ) : 0 ≤ PrimeLogMertens.coefficient n := by
  unfold PrimeLogMertens.coefficient
  split_ifs
  · exact div_nonneg (Real.log_natCast_nonneg n) (Nat.cast_nonneg n)
  · exact le_rfl

theorem interval_identity (A B : ℕ) (hAB : A ≤ B) :
    mass ((Ioc A B).filter Nat.Prime)=PrimeLogMertens.weightedPrimes B-PrimeLogMertens.weightedPrimes A := by
  have hset : range (B+1) \ range (A+1)=Ioc A B := by
    ext n
    rw [Finset.mem_sdiff,Finset.mem_range,Finset.mem_range,Finset.mem_Ioc]
    omega
  have hsub : range (A+1) ⊆ range (B+1) := range_mono (by omega)
  change mass ((Ioc A B).filter Nat.Prime)=(∑ n ∈ range (B+1), PrimeLogMertens.coefficient n)-
    ∑ n ∈ range (A+1), PrimeLogMertens.coefficient n
  rw [← sum_sdiff hsub, hset,add_sub_cancel_right]
  rw [mass,sum_filter]
  apply sum_congr rfl
  intro p hp
  exact (by rfl : (if p.Prime then Real.log (p : ℝ)/(p : ℝ) else 0)=PrimeLogMertens.coefficient p)

theorem interval_mass_bound (A B : ℕ) (hA : 1 ≤ A) (hAB : A ≤ B) :
    mass ((Ioc A B).filter Nat.Prime) ≤ Real.log (B : ℝ)-Real.log (A : ℝ)+
      2*(Real.log 4+PrimeLogMertens.primePowerTotal+5) := by
  rw [interval_identity A B hAB]
  have ha := PrimeLogMertens.natural_error A hA
  have hb := PrimeLogMertens.natural_error B (hA.trans hAB)
  linarith [(abs_le.mp ha).1,(abs_le.mp hb).2]

theorem log_reciprocal_le_one (n : ℕ) (hn : 1 ≤ n) : Real.log (n : ℝ)/(n : ℝ) ≤ 1 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  apply (div_le_one hn0).mpr
  linarith [Real.log_le_sub_one_of_pos hn0]

theorem diameter_bound (S : Finset ℕ) (D : ℝ) (hS : ∀ p ∈ S, Nat.Prime p)
    (hD0 : 0 ≤ D) (hD : ∀ p ∈ S, ∀ q ∈ S, Real.log (p : ℝ)-Real.log (q : ℝ) ≤ D) :
    mass S ≤ D+constant := by
  by_cases hne : S.Nonempty
  · let A := S.min' hne
    let B := S.max' hne
    have hAmem : A ∈ S := S.min'_mem hne
    have hBmem : B ∈ S := S.max'_mem hne
    have hAprime := hS A hAmem
    have hAB : A ≤ B := S.le_max' A hAmem
    have hsub : S.erase A ⊆ (Ioc A B).filter Nat.Prime := by
      intro p hp
      have hpS := (mem_erase.mp hp).2
      refine mem_filter.mpr ⟨mem_Ioc.mpr ⟨?_,S.le_max' p hpS⟩,hS p hpS⟩
      exact lt_of_le_of_ne (S.min'_le p hpS) (Ne.symm (mem_erase.mp hp).1)
    have hmass : mass (S.erase A) ≤ mass ((Ioc A B).filter Nat.Prime) :=
      sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ ↦
        div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p))
    have he : mass S=mass (S.erase A)+Real.log (A : ℝ)/(A : ℝ) := (sum_erase_add S _ hAmem).symm
    rw [he]
    have hi := interval_mass_bound A B hAprime.one_le hAB
    have hs := log_reciprocal_le_one A hAprime.one_le
    have hd := hD B hBmem A hAmem
    dsimp only [constant]
    linarith
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne,mass,sum_empty]
    exact add_nonneg hD0 constant_pos.le

def reciprocalMass (R : ℝ) (S : Finset ℕ) : ℝ :=
  ∑ p ∈ S, Real.log (p : ℝ)/((p : ℝ)*Real.log (R/(p : ℝ)))

theorem band_weight_bound (R U : ℝ) (hR : 0 < R) (hU : 0 < U) (S : Finset ℕ)
    (hS : ∀ p ∈ S, Nat.Prime p ∧ U ≤ Real.log (R/(p : ℝ)) ∧ Real.log (R/(p : ℝ)) ≤ 2*U) :
    reciprocalMass R S ≤ 1+constant/U := by
  have hmass := diameter_bound S U (fun p hp ↦ (hS p hp).1) hU.le (by
    intro p hp q hq
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (hS p hp).1.ne_zero
    have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (hS q hq).1.ne_zero
    have hu := (hS p hp).2.1
    have hv := (hS q hq).2.2
    rw [Real.log_div hR.ne' hp0] at hu
    rw [Real.log_div hR.ne' hq0] at hv
    linarith)
  calc
    _ ≤ ∑ p ∈ S, (Real.log (p : ℝ)/(p : ℝ))/U := by
      apply sum_le_sum
      intro p hp
      rw [← div_div]
      exact div_le_div_of_nonneg_left
        (div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)) hU (hS p hp).2.1
    _ = mass S/U := by simp only [mass,div_eq_mul_inv,sum_mul]
    _ ≤ (U+constant)/U := div_le_div_of_nonneg_right hmass hU.le
    _ = _ := by field_simp

theorem dyadic_cover (a u : ℝ) (ha : 0 < a) (hlow : a ≤ u) (K : ℕ) :
    u ≤ a*(2 : ℝ)^K → ∃ j ∈ range (K+1), a*(2 : ℝ)^j ≤ u ∧ u ≤ 2*(a*(2 : ℝ)^j) := by
  induction K with
  | zero =>
    intro hupper
    refine ⟨0,by simp,?_,?_⟩
    · simpa only [pow_zero,mul_one] using hlow
    · simp only [pow_zero,mul_one] at hupper ⊢
      linarith
  | succ K ih =>
    intro hupper
    by_cases hsmall : u ≤ a*(2 : ℝ)^K
    · obtain ⟨j,hj,hl,hu⟩ := ih hsmall
      exact ⟨j,mem_range.mpr (by have := mem_range.mp hj; omega),hl,hu⟩
    · refine ⟨K,mem_range.mpr (by omega),(lt_of_not_ge hsmall).le,?_⟩
      rw [pow_succ] at hupper
      nlinarith

theorem geometric_inverse_bound (K : ℕ) : (∑ j ∈ range K, 1/(2 : ℝ)^j) ≤ 2 := by
  have hh (K : ℕ) : (∑ j ∈ range K, 1/(2 : ℝ)^j)=2-2/(2 : ℝ)^K := by
    induction K with
    | zero => simp
    | succ K ih => rw [sum_range_succ,ih,pow_succ]; ring
  rw [hh]
  exact sub_le_self _ (by positivity)

theorem dyadic_weight_budget (R a : ℝ) (hR : 0 < R) (ha : 0 < a)
    (K : ℕ) (S : Finset ℕ)
    (hS : ∀ p ∈ S, Nat.Prime p ∧ a ≤ Real.log (R/(p : ℝ)) ∧
      Real.log (R/(p : ℝ)) ≤ a*(2 : ℝ)^K) :
    reciprocalMass R S ≤ ((K+1 : ℕ) : ℝ)+2*constant/a := by
  let w : ℕ → ℝ := fun p ↦ Real.log (p : ℝ)/((p : ℝ)*Real.log (R/(p : ℝ)))
  let cond (j p : ℕ) : Prop := a*(2 : ℝ)^j ≤ Real.log (R/(p : ℝ)) ∧
    Real.log (R/(p : ℝ)) ≤ 2*(a*(2 : ℝ)^j)
  let B (j : ℕ) : Finset ℕ := S.filter (cond j)
  have hw (p : ℕ) (hp : p ∈ S) : 0 ≤ w p :=
    div_nonneg (Real.log_natCast_nonneg p) (mul_nonneg (Nat.cast_nonneg p) (ha.le.trans (hS p hp).2.1))
  have hpoint (p : ℕ) (hp : p ∈ S) : w p ≤ ∑ j ∈ range (K+1), if cond j p then w p else 0 := by
    obtain ⟨j,hj,hl,hu⟩ := dyadic_cover a (Real.log (R/(p : ℝ))) ha (hS p hp).2.1 K (hS p hp).2.2
    have hc : cond j p := ⟨hl,hu⟩
    have hh := single_le_sum (f := fun k ↦ if cond k p then w p else 0)
      (fun k hk ↦ by
        split_ifs
        · exact hw p hp
        · exact le_rfl) hj
    simpa only [ite_eq_left hc] using hh
  have he : (∑ p ∈ S, ∑ j ∈ range (K+1), if cond j p then w p else 0)=
      ∑ j ∈ range (K+1), reciprocalMass R (B j) := by
    rw [sum_comm]
    apply sum_congr rfl
    intro j hj
    exact (sum_filter (cond j) w).symm
  calc
    _ ≤ ∑ p ∈ S, ∑ j ∈ range (K+1), if cond j p then w p else 0 := sum_le_sum hpoint
    _ = ∑ j ∈ range (K+1), reciprocalMass R (B j) := he
    _ ≤ ∑ j ∈ range (K+1), (1+constant/(a*(2 : ℝ)^j)) := by
      apply sum_le_sum
      intro j hj
      apply band_weight_bound R (a*(2 : ℝ)^j) hR (by positivity)
      intro p hp
      exact ⟨(hS p (mem_filter.mp hp).1).1,(mem_filter.mp hp).2⟩
    _ = ((K+1 : ℕ) : ℝ)+(constant/a)*∑ j ∈ range (K+1), 1/(2 : ℝ)^j := by
      rw [sum_add_distrib,sum_const,card_range,nsmul_eq_mul,mul_one,mul_sum]
      congr 1
      apply sum_congr rfl
      intro j hj
      ring
    _ ≤ ((K+1 : ℕ) : ℝ)+(constant/a)*2 := add_le_add le_rfl
      (mul_le_mul_of_nonneg_left (geometric_inverse_bound (K+1)) (div_nonneg constant_pos.le ha.le))
    _ = _ := by ring

theorem logarithmic_weight_budget (R a b : ℝ) (hR : 0 < R) (ha : 0 < a) (hab : a ≤ b)
    (S : Finset ℕ) (hS : ∀ p ∈ S, Nat.Prime p ∧ a ≤ Real.log (R/(p : ℝ)) ∧ Real.log (R/(p : ℝ)) ≤ b) :
    reciprocalMass R S ≤ Real.log (b/a)/Real.log 2+2+2*constant/a := by
  let r := Real.log (b/a)/Real.log 2
  let K := ⌈r⌉₊
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have htwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hr : 0 ≤ r := div_nonneg (Real.log_nonneg ((one_le_div ha).mpr hab)) htwo.le
  have hK : r ≤ (K : ℝ) := Nat.le_ceil _
  have hKupper : (K : ℝ) ≤ r+1 := (Nat.ceil_lt_add_one hr).le
  have hlog : Real.log (b/a) ≤ (K : ℝ)*Real.log 2 := (div_le_iff₀ htwo).mp hK
  have hpow : b ≤ a*(2 : ℝ)^K := by
    have hp : b/a ≤ (2 : ℝ)^K := by
      apply (Real.log_le_log_iff (div_pos hb ha) (by positivity)).mp
      simpa only [Real.log_pow] using hlog
    have hh := (div_le_iff₀ ha).mp hp
    nlinarith
  have hh := dyadic_weight_budget R a hR ha K S (by
    intro p hp
    exact ⟨(hS p hp).1,(hS p hp).2.1,(hS p hp).2.2.trans hpow⟩)
  have hKplus : ((K+1 : ℕ) : ℝ) ≤ r+2 := by push_cast; linarith
  exact hh.trans (by dsimp only [r] at hKplus; linarith)

theorem convolution_weight_bound (X : ℕ) (hX : 4 ≤ X) (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p ∧ 2*p ≤ X) :
    RealTripleConvolution.reciprocalWeight X P ≤
      Real.log (Real.log (X : ℝ)/Real.log 2)/Real.log 2+2+2*constant/Real.log 2 := by
  have hX0 : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have htwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  change reciprocalMass (X : ℝ) P ≤ _
  apply logarithmic_weight_budget (X : ℝ) (Real.log 2) (Real.log (X : ℝ)) hX0 htwo
    (Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 2 ≤ X)))
  intro p hp
  have hprime := (hP p hp).1
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hprime.pos
  refine ⟨hprime,?_,?_⟩
  · apply Real.log_le_log (by norm_num)
    apply (le_div_iff₀ hp0).mpr
    exact_mod_cast (hP p hp).2
  · exact Real.log_le_log (div_pos hX0 hp0) (div_le_self hX0.le (by exact_mod_cast hprime.one_le))

def bound (X : ℕ) : ℝ :=
  Real.log (Real.log (X : ℝ)/Real.log 2)/Real.log 2+2+2*constant/Real.log 2

theorem bound_ratio_tendsto : Tendsto (fun X : ℕ ↦ bound X/Real.log (X : ℝ)) atTop (nhds 0) := by
  have hlog : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hh := (PNT.tendsto_pow_log_div_pow_atTop 1 1 zero_lt_one).comp hlog
  have hl : Tendsto (fun X : ℕ ↦ Real.log (Real.log (X : ℝ))/Real.log (X : ℝ)) atTop (nhds 0) := by
    simpa only [Real.rpow_one,Function.comp_def] using hh
  have hi : Tendsto (fun X : ℕ ↦ 1/Real.log (X : ℝ)) atTop (nhds 0) := by
    simpa only [one_div,Function.comp_def] using tendsto_inv_atTop_zero.comp hlog
  let d := 2+2*constant/Real.log 2-Real.log (Real.log 2)/Real.log 2
  have hc := (hl.div_const (Real.log 2)).add (hi.const_mul d)
  have he : (fun X : ℕ ↦ Real.log (Real.log (X : ℝ))/Real.log (X : ℝ)/Real.log 2+d*(1/Real.log (X : ℝ)))
      =ᶠ[atTop] (fun X : ℕ ↦ bound X/Real.log (X : ℝ)) := by
    filter_upwards [eventually_ge_atTop 4] with X hX
    have htwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    have hXlog : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < X))
    dsimp only [bound,d]
    rw [Real.log_div hXlog.ne' htwo.ne']
    ring
  simpa only [zero_div,mul_zero,add_zero] using hc.congr' he

theorem triple_error_small_uniform (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, 4 ≤ X₀ ∧ ∀ X ≥ X₀, ∀ P : Finset ℕ,
      (∀ p ∈ P, Nat.Prime p ∧ 2*p ≤ X) → ∀ f : ℕ →* ℂ,
      (∀ n : ℕ, 0 < n → ‖f n‖ ≤ 1) →
      ‖(RealTripleConvolution.restricted f X P-RealTripleConvolution.triple f X P)/
        (Real.log (X : ℝ) : ℂ)‖ ≤ ε*(X : ℝ) := by
  let c := 1+PrimeLogMertens.primePowerTotal
  have hc : 0 < c := by dsimp only [c]; linarith [PrimeLogMertens.primePowerTotal_nonneg]
  have hh := bound_ratio_tendsto.eventually (eventually_lt_nhds (div_pos hε hc))
  obtain ⟨X₀,hX₀⟩ := eventually_atTop.mp hh
  refine ⟨max X₀ 4,le_max_right _ _,?_⟩
  intro X hX P hP f hf
  have hX4 : 4 ≤ X := (le_max_right _ _).trans hX
  have hr := hX₀ X ((le_max_left _ _).trans hX)
  have hlog : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < X))
  have he := RealTripleConvolution.triple_error f hf X P hP
  have hw := convolution_weight_bound X hX4 P hP
  have hsmall : c*(bound X/Real.log (X : ℝ)) ≤ ε := by
    simpa only [mul_comm] using (le_div_iff₀ hc).mp hr.le
  rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hlog]
  calc
    _ ≤ (c*(X : ℝ)*RealTripleConvolution.reciprocalWeight X P)/Real.log (X : ℝ) :=
      div_le_div_of_nonneg_right he hlog.le
    _ ≤ (c*(X : ℝ)*bound X)/Real.log (X : ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hw (mul_nonneg hc.le (Nat.cast_nonneg X))) hlog.le
    _ = (X : ℝ)*(c*(bound X/Real.log (X : ℝ))) := by ring
    _ ≤ (X : ℝ)*ε := mul_le_mul_of_nonneg_left hsmall (Nat.cast_nonneg X)
    _ = _ := by ring
end PaperP1.PrimeLogDiameter



