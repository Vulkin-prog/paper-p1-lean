module

public import PaperP1.Analysis.FirstBandSmallRegion
public import PaperP1.Analysis.NarrowBandReciprocalMass
public import PaperP1.Analysis.BoundedAmplificationFactor
public import PaperP1.Analysis.ActualAnchorOrderGeometry

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.MixedRegionEnvelope
open Finset PaperP1
open scoped Classical

theorem second_prime_bounds (N : ℕ) : ∀ p ∈ TwoPrimeBandPopulation.second N,
    1 ≤ p ∧ (p : ℝ) ≤ Real.exp ((SlowPrimeBandSieve.lower N)^3) := by
  intro p hp
  refine ⟨(mem_filter.mp hp).2.one_le,?_⟩
  have hh : (p : ℝ) ≤ (⌊Real.exp ((SlowPrimeBandSieve.lower N)^3)⌋₊ : ℝ) := by
    exact_mod_cast (mem_Ioc.mp (mem_filter.mp hp).1).2
  exact hh.trans (Nat.floor_le (Real.exp_pos _).le)

theorem index_card_bounds (N H : ℕ) (hH : 0 < H) (hx : 2 ≤ SlowPrimeBandSieve.lower N)
    (hU : 1 ≤ SlowPrimeBandSieve.upper N) (hHcap : (H : ℝ) ≤ (SlowPrimeBandSieve.lower N)^3) :
    ((NarrowPrimeBands.indices H (TwoPrimeBandPopulation.first N)).card : ℝ) ≤ 2*(SlowPrimeBandSieve.lower N)^4 ∧
    ((NarrowPrimeBands.indices H (TwoPrimeBandPopulation.second N)).card : ℝ) ≤ 2*(SlowPrimeBandSieve.lower N)^6 := by
  let x := SlowPrimeBandSieve.lower N
  have hxp : 0 < x := by dsimp only [x]; linarith
  have hx1 : 1 ≤ x := by dsimp only [x]; linarith
  have hx3 : 1 ≤ x^3 := one_le_pow₀ hx1
  have hHplus : (H : ℝ)+1 ≤ 2*x^3 := by linarith only [hHcap,hx3]
  have hfirst := (FirstBandSmallRegion.indices_geometry N H hH hU (by linarith)).2
  have hsecond := NarrowPrimeBands.indices_card_bound H (TwoPrimeBandPopulation.second N)
    (Real.exp (x^3)) (second_prime_bounds N)
  simp only [Real.log_exp] at hsecond
  have hsecondR : ((NarrowPrimeBands.indices H (TwoPrimeBandPopulation.second N)).card : ℝ) ≤
      (⌊(H : ℝ)*x^3⌋₊ : ℝ)+1 := by exact_mod_cast hsecond
  have hfloor := Nat.floor_le (mul_nonneg (Nat.cast_nonneg H : (0 : ℝ) ≤ H) (pow_nonneg hxp.le 3))
  have hm1 := mul_le_mul_of_nonneg_right hHplus hxp.le
  have hm2 := mul_le_mul_of_nonneg_right hHplus (pow_nonneg hxp.le 3)
  constructor
  · nlinarith only [hfirst,hm1]
  · nlinarith only [hsecondR,hfloor,hx3,hm2]

theorem anchor_decay_bound (x q : ℝ) (hq : 0 < q) (hql : Real.exp (x^2)/2 ≤ q) :
    q^(-1/100 : ℝ) ≤ 2*Real.exp (-(x^2)/100) := by
  have hlp : 0 < Real.exp (x^2)/2 := by positivity
  have hm : q^(-1/100 : ℝ) ≤ (Real.exp (x^2)/2)^(-1/100 : ℝ) := by
    rw [Real.rpow_def_of_pos hq,Real.rpow_def_of_pos hlp]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_right (Real.log_le_log hlp hql) (by norm_num : (-1/100 : ℝ) ≤ 0))
  have he : (Real.exp (x^2)/2)^(-1/100 : ℝ)=Real.exp (-(x^2)/100)*(2 : ℝ)^(1/100 : ℝ) := by
    rw [Real.rpow_def_of_pos hlp,Real.log_div (Real.exp_pos _).ne' (by norm_num : (2 : ℝ) ≠ 0),Real.log_exp,
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),← Real.exp_add]
    congr 1
    ring
  have htwo : (2 : ℝ)^(1/100 : ℝ) ≤ 2 := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      (by norm_num : (1/100 : ℝ) ≤ 1)
  calc
    _ ≤ (Real.exp (x^2)/2)^(-1/100 : ℝ) := hm
    _ = Real.exp (-(x^2)/100)*(2 : ℝ)^(1/100 : ℝ) := he
    _ ≤ Real.exp (-(x^2)/100)*2 := mul_le_mul_of_nonneg_left htwo (Real.exp_pos _).le
    _ = _ := by ring

theorem weight_sum_bound (N H : ℕ) (hH : 2 ≤ H) (hx : 2 ≤ SlowPrimeBandSieve.lower N) :
    (∑ l ∈ NarrowPrimeBands.indices H (TwoPrimeBandPopulation.second N),
      2*BoundedAmplificationFactor.constant*(NarrowPrimeBands.anchor H l)^(-1/100 : ℝ)) ≤
    4*BoundedAmplificationFactor.constant*((NarrowPrimeBands.indices H (TwoPrimeBandPopulation.second N)).card : ℝ)*
      Real.exp (-((SlowPrimeBandSieve.lower N)^2)/100) := by
  have hpoint (l : ℕ) (hl : l ∈ NarrowPrimeBands.indices H (TwoPrimeBandPopulation.second N)) :
      2*BoundedAmplificationFactor.constant*(NarrowPrimeBands.anchor H l)^(-1/100 : ℝ) ≤
        4*BoundedAmplificationFactor.constant*Real.exp (-((SlowPrimeBandSieve.lower N)^2)/100) := by
    have hh := anchor_decay_bound (SlowPrimeBandSieve.lower N) (NarrowPrimeBands.anchor H l)
      (NarrowPrimeBands.anchor_pos H l) (ActualAnchorOrderGeometry.second_anchor_bounds N H hH hx l hl).1
    have hm := mul_le_mul_of_nonneg_left hh (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) BoundedAmplificationFactor.constant_pos.le)
    nlinarith only [hm]
  calc
    _ ≤ ∑ _l ∈ NarrowPrimeBands.indices H (TwoPrimeBandPopulation.second N),
        4*BoundedAmplificationFactor.constant*Real.exp (-((SlowPrimeBandSieve.lower N)^2)/100) := sum_le_sum hpoint
    _ = _ := by rw [sum_const,nsmul_eq_mul]; ring

theorem envelope_bound (N H : ℕ) (hH : 2 ≤ H) (hx : 2 ≤ SlowPrimeBandSieve.lower N)
    (hU : 1 ≤ SlowPrimeBandSieve.upper N) (hHcap : (H : ℝ) ≤ (SlowPrimeBandSieve.lower N)^3) :
    ((NarrowPrimeBands.indices H (TwoPrimeBandPopulation.first N)).card : ℝ)*
      ((NarrowPrimeBands.indices H (TwoPrimeBandPopulation.second N)).card : ℝ)*
      (∑ l ∈ NarrowPrimeBands.indices H (TwoPrimeBandPopulation.second N),
        2*BoundedAmplificationFactor.constant*(NarrowPrimeBands.anchor H l)^(-1/100 : ℝ)) ≤
    32*BoundedAmplificationFactor.constant*(SlowPrimeBandSieve.lower N)^16*
      Real.exp (-((SlowPrimeBandSieve.lower N)^2)/100) := by
  let x := SlowPrimeBandSieve.lower N
  let J := NarrowPrimeBands.indices H (TwoPrimeBandPopulation.first N)
  let K := NarrowPrimeBands.indices H (TwoPrimeBandPopulation.second N)
  obtain ⟨hJ,hK⟩ := index_card_bounds N H (by omega) hx hU hHcap
  have hK2 := pow_le_pow_left₀ (Nat.cast_nonneg K.card : (0 : ℝ) ≤ K.card) hK 2
  have hprod : (J.card : ℝ)*(K.card : ℝ)^2 ≤ (2*x^4)*(2*x^6)^2 :=
    mul_le_mul hJ hK2 (sq_nonneg _) (by positivity)
  have hsum := weight_sum_bound N H hH hx
  have hh := mul_le_mul_of_nonneg_left hsum (mul_nonneg (Nat.cast_nonneg J.card : (0 : ℝ) ≤ J.card)
    (Nat.cast_nonneg K.card : (0 : ℝ) ≤ K.card))
  calc
    _ ≤ (J.card : ℝ)*(K.card : ℝ)*(4*BoundedAmplificationFactor.constant*(K.card : ℝ)*Real.exp (-(x^2)/100)) := hh
    _ = 4*BoundedAmplificationFactor.constant*((J.card : ℝ)*(K.card : ℝ)^2)*Real.exp (-(x^2)/100) := by ring
    _ ≤ 4*BoundedAmplificationFactor.constant*((2*x^4)*(2*x^6)^2)*Real.exp (-(x^2)/100) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprod
        (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) BoundedAmplificationFactor.constant_pos.le)) (Real.exp_pos _).le
    _ = _ := by ring
end PaperP1.MixedRegionEnvelope
