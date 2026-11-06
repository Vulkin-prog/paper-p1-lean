module

public import PaperP1.Analysis.PrimeLogDiameter

/-! # Actual prime-edge errors and uniform total triple-convolution approximation -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimeTruncation
open Finset Nat PaperP1 MultiplicativeLogConvolution RealTripleConvolution Filter
open scoped Classical Topology

def retained (X Z : ℕ) : Finset ℕ := (Icc 1 X).filter (fun p ↦ p.Prime ∧ Z < p ∧ 2*p ≤ X)

def term (f : ℕ →* ℂ) (X p : ℕ) : ℂ := (Real.log (p : ℝ) : ℂ)*f p*summatory f (X/p)

theorem retained_subset (X Z : ℕ) : retained X Z ⊆ (Icc 1 X).filter Nat.Prime := by
  intro p hp
  exact mem_filter.mpr ⟨(mem_filter.mp hp).1,(mem_filter.mp hp).2.1⟩

theorem term_reciprocal_bound (f : ℕ →* ℂ) (hf : ∀ n : ℕ, 0 < n → ‖f n‖ ≤ 1)
    (X p : ℕ) (hp : p.Prime) : ‖term f X p‖ ≤ (X : ℝ)*(Real.log (p : ℝ)/(p : ℝ)) := by
  have hlog : 0 ≤ Real.log (p : ℝ) := Real.log_natCast_nonneg p
  rw [term,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hlog]
  calc
    _ ≤ (Real.log (p : ℝ)*1)*((X/p : ℕ) : ℝ) := by
      apply mul_le_mul
      · exact mul_le_mul_of_nonneg_left (hf p hp.pos) hlog
      · exact summatory_norm f hf (X/p)
      · exact norm_nonneg _
      · positivity
    _ ≤ (Real.log (p : ℝ)*1)*((X : ℝ)/(p : ℝ)) :=
      mul_le_mul_of_nonneg_left Nat.cast_div_le (by positivity)
    _ = _ := by ring

theorem term_large_bound (f : ℕ →* ℂ) (hf : ∀ n : ℕ, 0 < n → ‖f n‖ ≤ 1)
    (X p : ℕ) (hp : p.Prime) (hpX : p ≤ X) (hlarge : X < 2*p) :
    ‖term f X p‖ ≤ Real.log (p : ℝ) := by
  have hlow : 1 ≤ X/p := (Nat.le_div_iff_mul_le hp.pos).mpr (by simpa using hpX)
  have hhigh : X/p < 2 := (Nat.div_lt_iff_lt_mul hp.pos).mpr hlarge
  have hq : X/p=1 := by omega
  have hs : summatory f (X/p)=1 := by simp [hq,summatory]
  rw [term,hs,mul_one,norm_mul,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (Real.log_natCast_nonneg p)]
  exact (mul_le_mul_of_nonneg_left (hf p hp.pos) (Real.log_natCast_nonneg p)).trans_eq (mul_one _)

theorem prime_log_prefix (X : ℕ) :
    (∑ p ∈ (Icc 1 X).filter Nat.Prime, Real.log (p : ℝ)) ≤ Real.log 4*(X : ℝ) := by
  have hset : Icc 1 X=Ioc 0 X := by ext n; simp only [mem_Icc,mem_Ioc]; omega
  have hh := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg X)
  simpa only [Chebyshev.theta,Nat.floor_natCast,← hset] using hh

theorem prime_mass_prefix (S : Finset ℕ) (Z : ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ p ≤ Z) :
    (∑ p ∈ S, Real.log (p : ℝ)/(p : ℝ)) ≤ PrimeLogMertens.weightedPrimes Z := by
  calc
    _ = ∑ p ∈ S, PrimeLogMertens.coefficient p := by
      apply sum_congr rfl
      intro p hp
      exact (ite_eq_left (hS p hp).1).symm
    _ ≤ ∑ p ∈ range (Z+1), PrimeLogMertens.coefficient p :=
      sum_le_sum_of_subset_of_nonneg (fun p hp ↦ mem_range.mpr (by have := (hS p hp).2; omega))
        (fun p _ _ ↦ PrimeLogDiameter.coefficient_nonneg p)
    _ = _ := rfl

theorem truncation_error (f : ℕ →* ℂ) (hf : ∀ n : ℕ, 0 < n → ‖f n‖ ≤ 1)
    (X Z : ℕ) : ‖prime f X-restricted f X (retained X Z)‖ ≤
      (X : ℝ)*(PrimeLogMertens.weightedPrimes Z+Real.log 4) := by
  let Q := (Icc 1 X).filter Nat.Prime
  let E := Q \ retained X Z
  have he : prime f X-restricted f X (retained X Z)=∑ p ∈ E, term f X p := by
    change (∑ p ∈ Q, term f X p)-(∑ p ∈ retained X Z, term f X p)=_
    rw [← sum_sdiff (retained_subset X Z),add_sub_cancel_right]
  have hpoint (p : ℕ) (hp : p ∈ E) : ‖term f X p‖ ≤
      (if p ≤ Z then (X : ℝ)*(Real.log (p : ℝ)/(p : ℝ)) else 0)+
      (if X < 2*p then Real.log (p : ℝ) else 0) := by
    have hE := mem_sdiff.mp hp
    have hQ := mem_filter.mp hE.1
    by_cases hsmall : p ≤ Z
    · rw [ite_eq_left hsmall]
      have hn : 0 ≤ if X < 2*p then Real.log (p : ℝ) else 0 := by
        split_ifs
        · exact Real.log_natCast_nonneg p
        · exact le_rfl
      exact (term_reciprocal_bound f hf X p hQ.2).trans (le_add_of_nonneg_right hn)
    · have hlarge : X < 2*p := by
        by_contra h
        exact hE.2 (mem_filter.mpr ⟨hQ.1,hQ.2,lt_of_not_ge hsmall,not_lt.mp h⟩)
      rw [ite_eq_right hsmall,ite_eq_left hlarge,zero_add]
      exact term_large_bound f hf X p hQ.2 (mem_Icc.mp hQ.1).2 hlarge
  have hnonneg (p : ℕ) : 0 ≤
      (if p ≤ Z then (X : ℝ)*(Real.log (p : ℝ)/(p : ℝ)) else 0)+
      (if X < 2*p then Real.log (p : ℝ) else 0) := by positivity [Real.log_natCast_nonneg p]
  have hs : (∑ p ∈ Q, if p ≤ Z then (X : ℝ)*(Real.log (p : ℝ)/(p : ℝ)) else 0) ≤
      (X : ℝ)*PrimeLogMertens.weightedPrimes Z := by
    rw [← sum_filter,← mul_sum]
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg X)
    apply prime_mass_prefix
    intro p hp
    exact ⟨(mem_filter.mp (mem_filter.mp hp).1).2,(mem_filter.mp hp).2⟩
  have hl : (∑ p ∈ Q, if X < 2*p then Real.log (p : ℝ) else 0) ≤ Real.log 4*(X : ℝ) := by
    calc
      _ ≤ ∑ p ∈ Q, Real.log (p : ℝ) := by
        apply sum_le_sum
        intro p hp
        split_ifs
        · exact le_rfl
        · exact Real.log_natCast_nonneg p
      _ ≤ _ := prime_log_prefix X
  rw [he]
  calc
    _ ≤ ∑ p ∈ E, ‖term f X p‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ E, ((if p ≤ Z then (X : ℝ)*(Real.log (p : ℝ)/(p : ℝ)) else 0)+
        (if X < 2*p then Real.log (p : ℝ) else 0)) := sum_le_sum hpoint
    _ ≤ ∑ p ∈ Q, ((if p ≤ Z then (X : ℝ)*(Real.log (p : ℝ)/(p : ℝ)) else 0)+
        (if X < 2*p then Real.log (p : ℝ) else 0)) :=
      sum_le_sum_of_subset_of_nonneg sdiff_subset (fun p _ _ ↦ hnonneg p)
    _ ≤ (X : ℝ)*PrimeLogMertens.weightedPrimes Z+Real.log 4*(X : ℝ) := by
      rw [sum_add_distrib]
      exact add_le_add hs hl
    _ = _ := by ring

def edgeBudget (Z : ℕ) : ℝ :=
  1+PrimeLogMertens.primePowerTotal+PrimeLogMertens.weightedPrimes Z+Real.log 4

def cutoff (A X : ℕ) : ℕ := ⌊(Real.log (X : ℝ))^A⌋₊

theorem first_truncated_reconstruction (f : ℕ →* ℂ)
    (hf : ∀ n : ℕ, 0 < n → ‖f n‖ ≤ 1) (X Z : ℕ) (hX : 2 ≤ X) :
    ‖summatory f X-restricted f X (retained X Z)/(Real.log (X : ℝ) : ℂ)‖ ≤
      (X : ℝ)*edgeBudget Z/Real.log (X : ℝ) := by
  have hlog : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < X))
  have he : summatory f X-restricted f X (retained X Z)/(Real.log (X : ℝ) : ℂ)=
      (summatory f X-prime f X/(Real.log (X : ℝ) : ℂ))+
        (prime f X-restricted f X (retained X Z))/(Real.log (X : ℝ) : ℂ) := by ring
  rw [he]
  have hn : ‖(prime f X-restricted f X (retained X Z))/(Real.log (X : ℝ) : ℂ)‖ ≤
      (X : ℝ)*(PrimeLogMertens.weightedPrimes Z+Real.log 4)/Real.log (X : ℝ) := by
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hlog]
    exact div_le_div_of_nonneg_right (truncation_error f hf X Z) hlog.le
  have hh := (norm_add_le _ _).trans (add_le_add (normalized_prime_reconstruction f hf X hX) hn)
  calc
    _ ≤ (1+PrimeLogMertens.primePowerTotal)*(X : ℝ)/Real.log (X : ℝ)+
        (X : ℝ)*(PrimeLogMertens.weightedPrimes Z+Real.log 4)/Real.log (X : ℝ) := hh
    _ = _ := by dsimp only [edgeBudget]; ring

theorem total_triple_reconstruction (f : ℕ →* ℂ)
    (hf : ∀ n : ℕ, 0 < n → ‖f n‖ ≤ 1) (X Z : ℕ) (hX : 4 ≤ X) :
    ‖summatory f X-triple f X (retained X Z)/(Real.log (X : ℝ) : ℂ)‖ ≤
      (X : ℝ)*(edgeBudget Z+(1+PrimeLogMertens.primePowerTotal)*PrimeLogDiameter.bound X)/Real.log (X : ℝ) := by
  have hlog : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < X))
  have hP : ∀ p ∈ retained X Z, p.Prime ∧ 2*p ≤ X := by
    intro p hp
    exact ⟨(mem_filter.mp hp).2.1,(mem_filter.mp hp).2.2.2⟩
  have he : summatory f X-triple f X (retained X Z)/(Real.log (X : ℝ) : ℂ)=
      (summatory f X-restricted f X (retained X Z)/(Real.log (X : ℝ) : ℂ))+
        (restricted f X (retained X Z)-triple f X (retained X Z))/(Real.log (X : ℝ) : ℂ) := by ring
  rw [he]
  have hn : ‖(restricted f X (retained X Z)-triple f X (retained X Z))/(Real.log (X : ℝ) : ℂ)‖ ≤
      ((1+PrimeLogMertens.primePowerTotal)*(X : ℝ)*PrimeLogDiameter.bound X)/Real.log (X : ℝ) := by
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hlog]
    apply div_le_div_of_nonneg_right _ hlog.le
    exact (triple_error f hf X (retained X Z) hP).trans
      (mul_le_mul_of_nonneg_left (PrimeLogDiameter.convolution_weight_bound X hX (retained X Z) hP)
        (mul_nonneg (by linarith [PrimeLogMertens.primePowerTotal_nonneg]) (Nat.cast_nonneg X)))
  have hh := (norm_add_le _ _).trans (add_le_add (first_truncated_reconstruction f hf X Z (by omega)) hn)
  calc
    _ ≤ (X : ℝ)*edgeBudget Z/Real.log (X : ℝ)+
        ((1+PrimeLogMertens.primePowerTotal)*(X : ℝ)*PrimeLogDiameter.bound X)/Real.log (X : ℝ) := hh
    _ = _ := by ring

theorem cutoff_prime_mass_ratio_tendsto (A : ℕ) :
    Tendsto (fun X : ℕ ↦ PrimeLogMertens.weightedPrimes (cutoff A X)/Real.log (X : ℝ)) atTop (nhds 0) := by
  have hlog : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hll : Tendsto (fun X : ℕ ↦ Real.log (Real.log (X : ℝ))/Real.log (X : ℝ)) atTop (nhds 0) := by
    simpa only [Real.rpow_one,Function.comp_def] using (PNT.tendsto_pow_log_div_pow_atTop 1 1 zero_lt_one).comp hlog
  have hi : Tendsto (fun X : ℕ ↦ 1/Real.log (X : ℝ)) atTop (nhds 0) := by
    simpa only [one_div,Function.comp_def] using tendsto_inv_atTop_zero.comp hlog
  have hu : Tendsto (fun X : ℕ ↦ ((A : ℝ)*Real.log (Real.log (X : ℝ))+(Real.log 4+4))/Real.log (X : ℝ)) atTop (nhds 0) := by
    have hc := (hll.const_mul (A : ℝ)).add (hi.const_mul (Real.log 4+4))
    have he : (fun X : ℕ ↦ (A : ℝ)*(Real.log (Real.log (X : ℝ))/Real.log (X : ℝ))+
        (Real.log 4+4)*(1/Real.log (X : ℝ)))=
        (fun X : ℕ ↦ ((A : ℝ)*Real.log (Real.log (X : ℝ))+(Real.log 4+4))/Real.log (X : ℝ)) := by
      funext X
      ring
    rw [he] at hc
    simpa only [mul_zero,zero_add] using hc
  have hnonneg : ∀ᶠ X : ℕ in atTop, 0 ≤ PrimeLogMertens.weightedPrimes (cutoff A X)/Real.log (X : ℝ) := by
    filter_upwards [hlog.eventually (eventually_ge_atTop 1)] with X hX
    exact div_nonneg (sum_nonneg (fun p _ ↦ PrimeLogDiameter.coefficient_nonneg p)) (by linarith)
  have hupper : ∀ᶠ X : ℕ in atTop,
      PrimeLogMertens.weightedPrimes (cutoff A X)/Real.log (X : ℝ) ≤
        ((A : ℝ)*Real.log (Real.log (X : ℝ))+(Real.log 4+4))/Real.log (X : ℝ) := by
    filter_upwards [hlog.eventually (eventually_ge_atTop 1)] with X hX
    have hpow : (1 : ℝ) ≤ (Real.log (X : ℝ))^A := one_le_pow₀ hX
    have hZ : 1 ≤ cutoff A X := Nat.le_floor (by simpa only [Nat.cast_one] using hpow)
    have hZ0 : (0 : ℝ) < cutoff A X := by exact_mod_cast hZ
    have hZle : (cutoff A X : ℝ) ≤ (Real.log (X : ℝ))^A := Nat.floor_le (by positivity)
    have hmass := (PrimeLogMertens.natural_bounds (cutoff A X) hZ).2
    have hlogZ : Real.log (cutoff A X : ℝ) ≤ (A : ℝ)*Real.log (Real.log (X : ℝ)) := by
      have hh := Real.log_le_log hZ0 hZle
      rwa [Real.log_pow] at hh
    exact div_le_div_of_nonneg_right (hmass.trans (add_le_add hlogZ le_rfl)) (by linarith)
  exact squeeze_zero' hnonneg hupper hu

def errorRatio (A X : ℕ) : ℝ :=
  (edgeBudget (cutoff A X)+(1+PrimeLogMertens.primePowerTotal)*PrimeLogDiameter.bound X)/Real.log (X : ℝ)

theorem errorRatio_tendsto (A : ℕ) : Tendsto (errorRatio A) atTop (nhds 0) := by
  have hlog : Tendsto (fun X : ℕ ↦ Real.log (X : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  have hi : Tendsto (fun X : ℕ ↦ 1/Real.log (X : ℝ)) atTop (nhds 0) := by
    simpa only [one_div,Function.comp_def] using tendsto_inv_atTop_zero.comp hlog
  let c := 1+PrimeLogMertens.primePowerTotal+Real.log 4
  let d := 1+PrimeLogMertens.primePowerTotal
  have hc := ((cutoff_prime_mass_ratio_tendsto A).add (hi.const_mul c)).add
    (PrimeLogDiameter.bound_ratio_tendsto.const_mul d)
  have he : (fun X : ℕ ↦ PrimeLogMertens.weightedPrimes (cutoff A X)/Real.log (X : ℝ)+
      c*(1/Real.log (X : ℝ))+d*(PrimeLogDiameter.bound X/Real.log (X : ℝ)))=errorRatio A := by
    funext X
    dsimp only [c,d,errorRatio,edgeBudget]
    ring
  rw [he] at hc
  simpa only [mul_zero,zero_add,add_zero] using hc

theorem total_triple_small_uniform (A : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, 4 ≤ X₀ ∧ ∀ X ≥ X₀, ∀ f : ℕ →* ℂ,
      (∀ n : ℕ, 0 < n → ‖f n‖ ≤ 1) →
      ‖summatory f X-triple f X (retained X (cutoff A X))/(Real.log (X : ℝ) : ℂ)‖ ≤ ε*(X : ℝ) := by
  obtain ⟨X₀,hX₀⟩ := eventually_atTop.mp ((errorRatio_tendsto A).eventually (eventually_lt_nhds hε))
  refine ⟨max X₀ 4,le_max_right _ _,?_⟩
  intro X hX f hf
  have hX4 : 4 ≤ X := (le_max_right _ _).trans hX
  have hr := (hX₀ X ((le_max_left _ _).trans hX)).le
  have he := total_triple_reconstruction f hf X (cutoff A X) hX4
  calc
    _ ≤ (X : ℝ)*errorRatio A X := by
      simpa only [errorRatio,mul_div_assoc] using he
    _ ≤ (X : ℝ)*ε := mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg X)
    _ = _ := by ring
end PaperP1.PrimeTruncation


