module

public import PaperP1.Analysis.FirstBandSmallRegion
public import PaperP1.Analysis.NarrowBandReciprocalMass
public import PaperP1.Analysis.GrowingFirstGoodRegion
public import PaperP1.Analysis.TwoPrimeBandPopulation
public import PaperP1.Analysis.FloorAmplificationOrder

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.ActualAnchorOrderGeometry
open Finset Filter PaperP1
open scoped Classical

theorem logarithm_half_lower (x : ℝ) (hx : 2 ≤ x) : (1/2 : ℝ) ≤ Real.log x := by
  have hxp : 0 < x := by linarith
  have hh := Real.one_sub_inv_le_log_of_pos hxp
  have hi : 1/x ≤ (1/2 : ℝ) := one_div_le_one_div_of_le (by norm_num) hx
  rw [← one_div] at hh
  linarith only [hh,hi]

theorem first_anchor_bounds (N H : ℕ) (hH : 2 ≤ H)
    (hx : 2 ≤ SlowPrimeBandSieve.lower N) (hU : 1 ≤ SlowPrimeBandSieve.upper N)
    (hHcap : (H : ℝ) ≤ (SlowPrimeBandSieve.lower N)^3) (j : ℕ)
    (hj : j ∈ NarrowPrimeBands.indices H (TwoPrimeBandPopulation.first N)) :
    (SlowPrimeBandSieve.lower N)^999 ≤ NarrowPrimeBands.anchor H j ∧
    (H : ℝ) ≤ NarrowPrimeBands.anchor H j ∧
    NarrowPrimeBands.anchor H j ≤ Real.log (N : ℝ) ∧
    999*Real.log (SlowPrimeBandSieve.lower N) ≤ Real.log (NarrowPrimeBands.anchor H j) ∧
    1 ≤ Real.log (NarrowPrimeBands.anchor H j) := by
  let x := SlowPrimeBandSieve.lower N
  have hxp : 0 < x := by dsimp only [x]; linarith
  have hx2 : 2 ≤ x := hx
  have hP := FirstBandSmallRegion.first_prime_bounds N hU
  have hlo : ∀ p ∈ TwoPrimeBandPopulation.first N, x^1000 ≤ (p : ℝ) := by
    intro p hp
    have hh : ⌊x^1000⌋₊ < p := (mem_Ioc.mp (mem_filter.mp hp).1).1
    exact ((Nat.floor_lt (show 0 ≤ x^1000 by positivity)).mp hh).le
  have hanchor := NarrowBandReciprocalMass.anchor_lower H hH (TwoPrimeBandPopulation.first N)
    (fun p hp ↦ (hP p hp).1) (x^1000) hlo j hj
  have hp1000 : 2*x^999 ≤ x^1000 := by
    have hh := mul_le_mul_of_nonneg_left hx2 (pow_nonneg hxp.le 999)
    nlinarith only [hh]
  have hu : x^999 ≤ NarrowPrimeBands.anchor H j :=
    ((le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr (by simpa only [mul_comm] using hp1000)).trans hanchor
  have hx996 : 1 ≤ x^996 := one_le_pow₀ (by linarith : 1 ≤ x)
  have hpower : x^3 ≤ x^999 := by
    have hh := mul_le_mul_of_nonneg_left hx996 (pow_nonneg hxp.le 3)
    nlinarith only [hh]
  have hcap := (FirstBandSmallRegion.indices_geometry N H (by omega) hU (by linarith) ).1 j hj
  have hlog := Real.log_le_log (pow_pos hxp 999) hu
  rw [Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  have hhalf := logarithm_half_lower x hx2
  exact ⟨hu,hHcap.trans (hpower.trans hu),hcap,hlog,by linarith only [hlog,hhalf]⟩

theorem second_anchor_bounds (N H : ℕ) (hH : 2 ≤ H) (hx : 2 ≤ SlowPrimeBandSieve.lower N) (l : ℕ)
    (hl : l ∈ NarrowPrimeBands.indices H (TwoPrimeBandPopulation.second N)) :
    Real.exp ((SlowPrimeBandSieve.lower N)^2)/2 ≤ NarrowPrimeBands.anchor H l ∧
    1 ≤ NarrowPrimeBands.anchor H l ∧ Real.log (NarrowPrimeBands.anchor H l) ≤ (SlowPrimeBandSieve.lower N)^3 := by
  let x := SlowPrimeBandSieve.lower N
  have hx2 : 2 ≤ x := hx
  have hP : ∀ p ∈ TwoPrimeBandPopulation.second N, 1 ≤ p := fun p hp ↦ (mem_filter.mp hp).2.one_le
  have hlo : ∀ p ∈ TwoPrimeBandPopulation.second N, Real.exp (x^2) ≤ (p : ℝ) := by
    intro p hp
    have hh : ⌊Real.exp (x^2)⌋₊ < p := (mem_Ioc.mp (mem_filter.mp hp).1).1
    exact ((Nat.floor_lt (Real.exp_pos _).le).mp hh).le
  have hlow := NarrowBandReciprocalMass.anchor_lower H hH (TwoPrimeBandPopulation.second N) hP (Real.exp (x^2)) hlo l hl
  have hxSq : (4 : ℝ) ≤ x^2 := by nlinarith only [hx2]
  have he := Real.add_one_le_exp (x^2)
  have hq1 : 1 ≤ NarrowPrimeBands.anchor H l := by nlinarith only [hlow,hxSq,he]
  have hcap : NarrowPrimeBands.anchor H l ≤ Real.exp (x^3) := by
    obtain ⟨p,hp,hj⟩ := mem_image.mp hl
    have hh := (NarrowPrimeBands.index_bounds H p (by omega) (hP p hp)).1
    rw [hj] at hh
    have hpU : (p : ℝ) ≤ (⌊Real.exp (x^3)⌋₊ : ℝ) := by exact_mod_cast (mem_Ioc.mp (mem_filter.mp hp).1).2
    exact hh.trans (hpU.trans (Nat.floor_le (Real.exp_pos _).le))
  have hlog := Real.log_le_log (NarrowPrimeBands.anchor_pos H l) hcap
  rw [Real.log_exp] at hlog
  exact ⟨hlow,hq1,hlog⟩

theorem eventual_order_geometry : ∀ᶠ N : ℕ in atTop,
    2 ≤ SlowPrimeBandSieve.lower N ∧ 4 ≤ GrowingFirstGoodRegion.width N ∧
    ∀ j ∈ NarrowPrimeBands.indices (GrowingFirstGoodRegion.width N) (TwoPrimeBandPopulation.first N),
      ∀ l ∈ NarrowPrimeBands.indices (GrowingFirstGoodRegion.width N) (TwoPrimeBandPopulation.second N),
      let u := NarrowPrimeBands.anchor (GrowingFirstGoodRegion.width N) j
      let q := NarrowPrimeBands.anchor (GrowingFirstGoodRegion.width N) l
      (GrowingFirstGoodRegion.width N : ℝ) ≤ u ∧ u ≤ Real.log (N : ℝ) ∧
      999*Real.log (SlowPrimeBandSieve.lower N) ≤ Real.log u ∧ 1 ≤ Real.log u ∧
      1 ≤ q ∧ Real.log q ≤ (SlowPrimeBandSieve.lower N)^3 ∧
      Real.exp ((SlowPrimeBandSieve.lower N)^2)/2 ≤ q ∧
      FloorAmplificationOrder.order u q ≤ GrowingFirstGoodRegion.width N ∧
      (FloorAmplificationOrder.order u q : ℝ) ≤ (SlowPrimeBandSieve.lower N)^3 := by
  filter_upwards [SlowPrimeBandSieve.lower_tendsto.eventually (eventually_ge_atTop 2),
    SlowPrimeBandSieve.upper_tendsto.eventually (eventually_ge_atTop 1),
    GrowingFirstGoodRegion.width_tendsto.eventually (eventually_ge_atTop 4)] with N hx hU hH
  have hHcap : (GrowingFirstGoodRegion.width N : ℝ) ≤ (SlowPrimeBandSieve.lower N)^3 := Nat.floor_le (by positivity)
  refine ⟨hx,hH,?_⟩
  intro j hj l hl
  dsimp only
  have hf := first_anchor_bounds N (GrowingFirstGoodRegion.width N) (by omega) hx hU hHcap j hj
  have hs := second_anchor_bounds N (GrowingFirstGoodRegion.width N) (by omega) hx l hl
  have hu : 1 < NarrowPrimeBands.anchor (GrowingFirstGoodRegion.width N) j := by
    have hh := Real.exp_lt_exp.mpr (show 0 < Real.log (NarrowPrimeBands.anchor (GrowingFirstGoodRegion.width N) j) by
      linarith only [hf.2.2.2.2])
    simpa only [Real.exp_zero,Real.exp_log (NarrowPrimeBands.anchor_pos _ _)] using hh
  have ho := FloorAmplificationOrder.order_le_floor_cube (SlowPrimeBandSieve.lower N)
    (NarrowPrimeBands.anchor (GrowingFirstGoodRegion.width N) j) (NarrowPrimeBands.anchor (GrowingFirstGoodRegion.width N) l)
    hu hs.2.1 hf.2.2.2.2 hs.2.2
  have hoR : (FloorAmplificationOrder.order (NarrowPrimeBands.anchor (GrowingFirstGoodRegion.width N) j)
      (NarrowPrimeBands.anchor (GrowingFirstGoodRegion.width N) l) : ℝ) ≤ (SlowPrimeBandSieve.lower N)^3 :=
    (by exact_mod_cast ho : (_ : ℝ) ≤ GrowingFirstGoodRegion.width N).trans hHcap
  exact ⟨hf.2.1,hf.2.2.1,hf.2.2.2.1,hf.2.2.2.2,hs.2.1,hs.2.2,hs.1,ho,hoR⟩
end PaperP1.ActualAnchorOrderGeometry
