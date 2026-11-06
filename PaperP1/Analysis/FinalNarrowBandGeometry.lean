module

public import PaperP1.Analysis.FinalPrimeBandPopulation
public import PaperP1.Analysis.GrowingFirstGoodRegion
public import PaperP1.Analysis.NarrowPrimeBands

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.FinalNarrowBandGeometry
open Finset PaperP1
open scoped Classical

theorem anchor_upper (B N H j : ℕ) (hB : 32 ≤ B) (hN : 1 ≤ N) (hH : 0 < H)
    (hj : j ∈ NarrowPrimeBands.indices H (FinalPrimeBandGeometry.primes B N)) :
    NarrowPrimeBands.anchor H j ≤ (N : ℝ)^(1/16 : ℝ) := by
  obtain ⟨p,hp,hj⟩ := mem_image.mp hj
  have hBounds := FinalPrimeBandPopulation.prime_bounds B N hB hN p hp
  have hAnchor := (NarrowPrimeBands.index_bounds H p hH hBounds.1).1
  rw [hj] at hAnchor
  exact hAnchor.trans hBounds.2

theorem index_card_bound (B N H : ℕ) (hB : 32 ≤ B) (hN : 1 ≤ N)
    (hz : 1 ≤ SlowPrimeBandSieve.upper N) (hH : (H : ℝ) ≤ (SlowPrimeBandSieve.lower N)^3) :
    ((NarrowPrimeBands.indices H (FinalPrimeBandGeometry.primes B N)).card : ℝ) ≤
      2*(SlowPrimeBandSieve.upper N)^4 := by
  let z := SlowPrimeBandSieve.upper N
  let x := SlowPrimeBandSieve.lower N
  have hz1 : 1 ≤ z := hz
  have hzp : 0 < z := by linarith only [hz1]
  have hx0 : 0 ≤ x := Real.log_nonneg hz1
  have hxz : x ≤ z := by
    have hh := Real.log_le_sub_one_of_pos hzp
    change x ≤ z-1 at hh
    linarith only [hh]
  have hH3 : (H : ℝ) ≤ z^3 := hH.trans (pow_le_pow_left₀ hx0 hxz 3)
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hPrimeBounds : ∀ p ∈ FinalPrimeBandGeometry.primes B N, 1 ≤ p ∧ (p : ℝ) ≤ (N : ℝ) := by
    intro p hp
    have hh := FinalPrimeBandPopulation.prime_bounds B N hB hN p hp
    have hSelf := Real.rpow_le_rpow_of_exponent_le hNR (by norm_num : (1/16 : ℝ) ≤ 1)
    rw [Real.rpow_one] at hSelf
    exact ⟨hh.1,hh.2.trans hSelf⟩
  have hc := NarrowPrimeBands.indices_card_bound H (FinalPrimeBandGeometry.primes B N) (N : ℝ) hPrimeBounds
  have hcR : ((NarrowPrimeBands.indices H (FinalPrimeBandGeometry.primes B N)).card : ℝ) ≤
      (⌊(H : ℝ)*z⌋₊ : ℝ)+1 := by exact_mod_cast hc
  have hFloor := Nat.floor_le (show 0 ≤ (H : ℝ)*z by positivity)
  have hProd := mul_le_mul_of_nonneg_right hH3 hzp.le
  have hz4 : 1 ≤ z^4 := one_le_pow₀ hz1
  nlinarith only [hcR,hFloor,hProd,hz4]
end PaperP1.FinalNarrowBandGeometry
