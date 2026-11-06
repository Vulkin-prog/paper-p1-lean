module

public import PaperP1.Arithmetic.PrimeAvoidanceSieve
public import PaperP1.Arithmetic.PrimeHarmonicWindow
public import PaperP1.Asymptotics.ModerateOrder
public import PaperP1.Analysis.ClippedPowerSum

/-! # Actual slowly growing prime bands with negligible Ramare support exceptions -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SlowPrimeBandSieve
open Finset Filter PaperP1 PrimeAvoidanceSieve
open scoped Classical

def lower (N : ℕ) : ℝ := Real.log (Real.log N)
def upper (N : ℕ) : ℝ := Real.log N
def primes (N : ℕ) : Finset ℕ := (Ioc ⌊lower N⌋₊ ⌊upper N⌋₊).filter Nat.Prime

theorem lower_tendsto : Tendsto lower atTop atTop := ModerateOrder.loglog_tendsto_atTop

theorem upper_tendsto : Tendsto upper atTop atTop := PrimeLogBudget.log_nat_tendsto_atTop

theorem geometry_eventually : ∀ᶠ N : ℕ in atTop, 2 ≤ lower N ∧ lower N ≤ upper N := by
  filter_upwards [lower_tendsto.eventually (eventually_ge_atTop 2),
    upper_tendsto.eventually (eventually_ge_atTop 1)] with N hl hu
  refine ⟨hl,?_⟩
  exact Real.log_le_self (by linarith : 0 ≤ upper N)

theorem real_sub_log_tendsto : Tendsto (fun x : ℝ ↦ x-Real.log x) atTop atTop := by
  have hratio : Tendsto (fun x : ℝ ↦ Real.log x/x) atTop (nhds 0) := by
    simpa only [Real.rpow_one] using PNT.tendsto_pow_log_div_pow_atTop 1 1 zero_lt_one
  refine tendsto_atTop.2 ?_
  intro b
  filter_upwards [hratio.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1/2)),
    eventually_ge_atTop (max 1 (2*b))] with x hx hbig
  have hxpos : 0 < x := by linarith [le_max_left 1 (2*b)]
  have hlog := (div_lt_iff₀ hxpos).mp hx
  have hxb : 2*b ≤ x := (le_max_right 1 (2*b)).trans hbig
  linarith

theorem harmonic_gap_tendsto :
    Tendsto (fun N : ℕ ↦ Real.log (Real.log (upper N))-Real.log (Real.log (lower N))) atTop atTop := by
  have hu := Real.tendsto_log_atTop.comp lower_tendsto
  exact real_sub_log_tendsto.comp hu

theorem reciprocal_mass_tendsto : Tendsto (fun N ↦ reciprocalMass (primes N)) atTop atTop := by
  have hloglow := Real.tendsto_log_atTop.comp lower_tendsto
  refine tendsto_atTop.2 ?_
  intro b
  filter_upwards [geometry_eventually,
    hloglow.eventually (eventually_ge_atTop (2*PrimeLogMertens.budget+1)),
    harmonic_gap_tendsto.eventually (eventually_ge_atTop (b+1))] with N hgeom hden hgap
  change 2*PrimeLogMertens.budget+1 ≤ Real.log (lower N) at hden
  have hlog : 0 < Real.log (lower N) := Real.log_pos (by linarith [hgeom.1])
  have he := PrimeHarmonicWindow.finite_window_bound (lower N) (upper N) hgeom.1 hgeom.2
  have herr : 2*PrimeLogMertens.budget/Real.log (lower N) ≤ 1 :=
    (div_le_iff₀ hlog).mpr (by linarith)
  have hlo := (abs_le.mp (he.trans herr)).1
  change -(1 : ℝ) ≤ reciprocalMass (primes N)-
    (Real.log (Real.log (upper N))-Real.log (Real.log (lower N))) at hlo
  linarith

theorem prime_card_bound (N : ℕ) : (primes N).card ≤ ⌊upper N⌋₊ := by
  have hs : primes N ⊆ Ioc 0 ⌊upper N⌋₊ := by
    intro p hp
    obtain ⟨hpint,hprime⟩ := mem_filter.mp hp
    exact mem_Ioc.mpr ⟨hprime.pos,(mem_Ioc.mp hpint).2⟩
  simpa only [Nat.card_Ioc,Nat.sub_zero] using card_le_card hs

theorem normalized_card_square_tendsto :
    Tendsto (fun N : ℕ ↦ ((primes N).card : ℝ)^2/(N : ℝ)) atTop (nhds 0) := by
  have hlog : Tendsto (fun N : ℕ ↦ (Real.log N)^2/(N : ℝ)) atTop (nhds 0) := by
    have hh := (PNT.tendsto_pow_log_div_pow_atTop 1 2 zero_lt_one).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa only [Real.rpow_one,Real.rpow_two,Function.comp_def] using hh
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlog
  · exact Filter.Eventually.of_forall (fun N ↦ by positivity)
  · filter_upwards [upper_tendsto.eventually (eventually_ge_atTop 0)] with N hu
    have hcard : ((primes N).card : ℝ) ≤ (⌊upper N⌋₊ : ℝ) := by exact_mod_cast prime_card_bound N
    have hc : ((primes N).card : ℝ) ≤ upper N := hcard.trans (Nat.floor_le hu)
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hc 2) (Nat.cast_nonneg _)

theorem primes_below_polynomial_cutoff_eventually (a : ℝ) (ha : 0 < a) :
    ∀ᶠ N : ℕ in atTop, ∀ p ∈ primes N, p ≤ ⌊(N : ℝ)^a⌋₊ := by
  have hratio : Tendsto (fun N : ℕ ↦ Real.log N/(N : ℝ)^a) atTop (nhds 0) := by
    have hh := (PNT.tendsto_pow_log_div_pow_atTop a 1 ha).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa only [Real.rpow_one,Function.comp_def] using hh
  filter_upwards [hratio.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    eventually_ge_atTop 1] with N hsmall hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hpower : 0 < (N : ℝ)^a := Real.rpow_pos_of_pos hNpos a
  have hlog : Real.log N ≤ (N : ℝ)^a := by
    have hh := (div_lt_iff₀ hpower).mp hsmall
    linarith
  intro p hp
  have hu := (mem_Ioc.mp (mem_filter.mp hp).1).2
  exact hu.trans (Nat.floor_mono hlog)
theorem avoidance_density_tendsto :
    Tendsto (fun N : ℕ ↦ ((avoiding (primes N) (2*N)).card : ℝ)/(N : ℝ)) atTop (nhds 0) := by
  have hi : Tendsto (fun N ↦ (reciprocalMass (primes N))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp reciprocal_mass_tendsto
  have hb : Tendsto (fun N : ℕ ↦ 2/reciprocalMass (primes N)+
      (((primes N).card : ℝ)^2/(N : ℝ))*(reciprocalMass (primes N))⁻¹^2) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv,mul_zero,zero_mul,add_zero,zero_pow (by norm_num : 2 ≠ 0)] using
      (hi.const_mul 2).add (normalized_card_square_tendsto.mul (hi.pow 2))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hb
  · exact Filter.Eventually.of_forall (fun N ↦ by positivity)
  · filter_upwards [reciprocal_mass_tendsto.eventually (eventually_ge_atTop 1),
      eventually_ge_atTop 1] with N hH hN
    have hHp : 0 < reciprocalMass (primes N) := by linarith
    have hc := avoidance_card (primes N) (fun p hp ↦ (mem_filter.mp hp).2) (2*N) hHp
    have hh := div_le_div_of_nonneg_right hc (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
    have he : (((2*N : ℕ) : ℝ)/reciprocalMass (primes N)+
        ((primes N).card : ℝ)^2/(reciprocalMass (primes N))^2)/(N : ℝ) =
        2/reciprocalMass (primes N)+(((primes N).card : ℝ)^2/(N : ℝ))*
          (reciprocalMass (primes N))⁻¹^2 := by
      push_cast
      field_simp
    exact hh.trans_eq he

theorem square_tail_bound (N : ℕ) (hlower : 2 ≤ lower N) :
    (∑ p ∈ primes N, 1/(p : ℝ)^2) ≤ 2/lower N := by
  have hcut : ∀ p ∈ primes N, lower N < (p : ℝ) := by
    intro p hp
    exact (Nat.floor_lt (by linarith : 0 ≤ lower N)).mp (mem_Ioc.mp (mem_filter.mp hp).1).1
  have ht := ClippedPowerSum.finite_tail_le_power (primes N) 2 (lower N) (by norm_num) (by linarith) hcut
  convert ht using 1
  · apply sum_congr rfl
    intro p hp
    norm_num [Real.rpow_neg,Real.rpow_two,div_eq_mul_inv]
  · norm_num [PowerSeriesTail.constant,Real.rpow_neg_one,div_eq_mul_inv]

theorem square_exceptions_card_bound (N X : ℕ) (hlower : 2 ≤ lower N) :
    ((PrimeDivisorWeights.squareExceptions (primes N) X).card : ℝ) ≤ 2*(X : ℝ)/lower N := by
  calc
    _ ≤ ∑ p ∈ primes N, ((X/p^2 : ℕ) : ℝ) := by
      exact_mod_cast PrimeDivisorWeights.square_exceptions_card (primes N) X
    _ ≤ ∑ p ∈ primes N, (X : ℝ)/(p : ℝ)^2 := by
      apply sum_le_sum
      intro p hp
      have hc : ((X/p^2 : ℕ) : ℝ) ≤ (X : ℝ)/((p^2 : ℕ) : ℝ) := Nat.cast_div_le
      convert hc using 1
      norm_cast
    _ = (X : ℝ)*∑ p ∈ primes N, 1/(p : ℝ)^2 := by
      rw [mul_sum]
      apply sum_congr rfl
      intro p hp
      ring
    _ ≤ (X : ℝ)*(2/lower N) := mul_le_mul_of_nonneg_left (square_tail_bound N hlower) (Nat.cast_nonneg X)
    _ = _ := by ring

theorem square_exceptions_density_tendsto :
    Tendsto (fun N : ℕ ↦ ((PrimeDivisorWeights.squareExceptions (primes N) (2*N)).card : ℝ)/(N : ℝ))
      atTop (nhds 0) := by
  have hb : Tendsto (fun N ↦ 4/lower N) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv,mul_zero,Function.comp_def] using (tendsto_inv_atTop_zero.comp lower_tendsto).const_mul 4
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hb
  · exact Filter.Eventually.of_forall (fun N ↦ by positivity)
  · filter_upwards [geometry_eventually,eventually_ge_atTop 1] with N hg hN
    have hh := div_le_div_of_nonneg_right (square_exceptions_card_bound N (2*N) hg.1)
      (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
    have he : (2*((2*N : ℕ) : ℝ)/lower N)/(N : ℝ) = 4/lower N := by push_cast; field_simp; norm_num
    exact hh.trans_eq he

def excluded (N : ℕ) : Finset ℕ := avoiding (primes N) (2*N) ∪ PrimeDivisorWeights.squareExceptions (primes N) (2*N)

theorem excluded_density_tendsto :
    Tendsto (fun N : ℕ ↦ ((excluded N).card : ℝ)/(N : ℝ)) atTop (nhds 0) := by
  have hb := avoidance_density_tendsto.add square_exceptions_density_tendsto
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (by simpa only [add_zero] using hb)
  · exact Filter.Eventually.of_forall (fun N ↦ by positivity)
  · apply Filter.Eventually.of_forall
    intro N
    have hc : ((excluded N).card : ℝ) ≤ ((avoiding (primes N) (2*N)).card : ℝ)+
        ((PrimeDivisorWeights.squareExceptions (primes N) (2*N)).card : ℝ) := by
      exact_mod_cast card_union_le (avoiding (primes N) (2*N)) (PrimeDivisorWeights.squareExceptions (primes N) (2*N))
    simpa only [add_div] using div_le_div_of_nonneg_right hc (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
def good (N : ℕ) : Finset ℕ := Ico N (2*N) \ excluded N

theorem good_support (N : ℕ) (hN : 0 < N) (n : ℕ) (hn : n ∈ good N) :
    (0 < n ∧ n ≤ 2*N) ∧ 0 < PrimeDivisorWeights.count (primes N) n ∧
      ∀ p ∈ primes N, ¬p^2 ∣ n := by
  have hni := mem_Ico.mp (mem_sdiff.mp hn).1
  have hne := (mem_sdiff.mp hn).2
  have hn0 : 0 < n := hN.trans_le hni.1
  have hnX : n ≤ 2*N := hni.2.le
  refine ⟨⟨hn0,hnX⟩,?_,?_⟩
  · by_contra hcount
    apply hne
    apply mem_union_left
    apply mem_filter.mpr
    refine ⟨mem_Ioc.mpr ⟨hn0,hnX⟩,?_⟩
    intro p hp hpn
    have hpos := PrimeDivisorWeights.count_pos hp hpn
    omega
  · intro p hp hsq
    apply hne
    apply mem_union_right
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨hn0,hnX⟩,⟨p,hp,hsq⟩⟩

theorem missing_good_density_tendsto :
    Tendsto (fun N : ℕ ↦ ((Ico N (2*N) \ good N).card : ℝ)/(N : ℝ)) atTop (nhds 0) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds excluded_density_tendsto
  · exact Filter.Eventually.of_forall (fun N ↦ by positivity)
  · apply Filter.Eventually.of_forall
    intro N
    have hs : Ico N (2*N) \ good N ⊆ excluded N := by
      intro n hn
      by_contra hnot
      apply (mem_sdiff.mp hn).2
      exact mem_sdiff.mpr ⟨(mem_sdiff.mp hn).1,hnot⟩
    have hc : ((Ico N (2*N) \ good N).card : ℝ) ≤ (excluded N).card := by exact_mod_cast card_le_card hs
    exact div_le_div_of_nonneg_right hc (Nat.cast_nonneg N : (0 : ℝ) ≤ N)

theorem good_ramare_sum (N : ℕ) (hN : 0 < N) (f : ℕ → ℂ)
    (hf : ∀ a b, f (a*b) = f a * f b) :
    (∑ n ∈ good N, f n) =
      ∑ p ∈ primes N, ∑ m ∈ Icc 1 (2*N/p),
        if p*m ∈ good N then f p*f m/((PrimeDivisorWeights.count (primes N) m+1 : ℕ) : ℂ) else 0 := by
  exact PrimeDivisorWeights.ramare_sum (good N) (primes N) (2*N)
    (fun p hp ↦ (mem_filter.mp hp).2) (fun n hn ↦ (good_support N hN n hn).1)
    (fun n hn ↦ (good_support N hN n hn).2.1) (fun n hn ↦ (good_support N hN n hn).2.2) f hf
end SlowPrimeBandSieve
