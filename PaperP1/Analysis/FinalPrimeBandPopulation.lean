module

public import PaperP1.Analysis.TwoPrimeBandPopulation
public import PaperP1.Analysis.FlexiblePrimeBandSieve
public import PaperP1.Analysis.FinalPrimeBandGeometry
public import PaperP1.Analysis.FinalPrimeBandSieve

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.FinalPrimeBandPopulation
open Finset Filter PaperP1
open scoped Classical

def good (B N : ℕ) : Finset ℕ := TwoPrimeBandPopulation.good N ∩
  FlexiblePrimeBandSieve.good FinalPrimeBandGeometry.lower (FinalPrimeBandGeometry.upper B) N

theorem good_subset (B N : ℕ) : good B N ⊆ Ico N (2*N) := by
  intro n hn
  exact TwoPrimeBandPopulation.good_subset N (mem_inter.mp hn).1

theorem good_support (B N : ℕ) (hN : 0 < N) (n : ℕ) (hn : n ∈ good B N) :
    (0 < n ∧ n ≤ 2*N) ∧
      0 < PrimeDivisorWeights.count (TwoPrimeBandPopulation.first N) n ∧
      0 < PrimeDivisorWeights.count (TwoPrimeBandPopulation.second N) n ∧
      0 < PrimeDivisorWeights.count (FinalPrimeBandGeometry.primes B N) n ∧
      (∀ p ∈ TwoPrimeBandPopulation.first N, ¬p^2 ∣ n) ∧
      (∀ p ∈ TwoPrimeBandPopulation.second N, ¬p^2 ∣ n) ∧
      (∀ p ∈ FinalPrimeBandGeometry.primes B N, ¬p^2 ∣ n) := by
  obtain ⟨h1,h3⟩ := mem_inter.mp hn
  have hh1 := TwoPrimeBandPopulation.good_support N hN n h1
  have hh3 := FlexiblePrimeBandSieve.good_support FinalPrimeBandGeometry.lower
    (FinalPrimeBandGeometry.upper B) N hN n h3
  exact ⟨hh1.1,hh1.2.1,hh1.2.2.1,hh3.2.1,hh1.2.2.2.1,hh1.2.2.2.2,hh3.2.2⟩

theorem missing_good_density_tendsto (B : ℕ) (hB : 32 ≤ B) :
    Tendsto (fun N : ℕ ↦ ((Ico N (2*N) \ good B N).card : ℝ)/(N : ℝ)) atTop (nhds 0) := by
  have h1 := TwoPrimeBandPopulation.missing_good_density_tendsto
  have h3 := FinalPrimeBandSieve.missing_good_density_tendsto B hB
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (by simpa only [add_zero] using h1.add h3)
  · exact Filter.Eventually.of_forall (fun N ↦ by positivity)
  · apply Filter.Eventually.of_forall
    intro N
    have he : Ico N (2*N) \ good B N =
        (Ico N (2*N) \ TwoPrimeBandPopulation.good N) ∪
        (Ico N (2*N) \ FlexiblePrimeBandSieve.good FinalPrimeBandGeometry.lower
          (FinalPrimeBandGeometry.upper B) N) := by
      ext n
      simp only [good,Finset.mem_sdiff,mem_inter,mem_union]
      tauto
    rw [he]
    have hc : (((Ico N (2*N) \ TwoPrimeBandPopulation.good N) ∪
        (Ico N (2*N) \ FlexiblePrimeBandSieve.good FinalPrimeBandGeometry.lower
          (FinalPrimeBandGeometry.upper B) N)).card : ℝ) ≤
        ((Ico N (2*N) \ TwoPrimeBandPopulation.good N).card : ℝ)+
        ((Ico N (2*N) \ FlexiblePrimeBandSieve.good FinalPrimeBandGeometry.lower
          (FinalPrimeBandGeometry.upper B) N).card : ℝ) := by
      exact_mod_cast card_union_le _ _
    simpa only [add_div] using div_le_div_of_nonneg_right hc (Nat.cast_nonneg N : (0 : ℝ) ≤ N)

theorem disjoint_first_eventually (B : ℕ) :
    ∀ᶠ N : ℕ in atTop, Disjoint (FinalPrimeBandGeometry.primes B N) (TwoPrimeBandPopulation.first N) := by
  filter_upwards [TwoPrimeBandPopulation.separation_eventually,
    FinalPrimeBandSieve.second_separation_eventually,
    SlowPrimeBandSieve.upper_tendsto.eventually (eventually_ge_atTop 0),
    SlowPrimeBandSieve.lower_tendsto.eventually (eventually_ge_atTop 1)] with N h12 h23 hU hx
  apply Finset.disjoint_left.mpr
  intro p hp3 hp1
  have hpU : (p : ℝ) ≤ PowerLogPrimeBand.upper N := by
    have hh : (p : ℝ) ≤ (⌊PowerLogPrimeBand.upper N⌋₊ : ℝ) := by
      exact_mod_cast (mem_Ioc.mp (mem_filter.mp hp1).1).2
    exact hh.trans (Nat.floor_le hU)
  have hpL : FinalPrimeBandGeometry.lower N < (p : ℝ) :=
    (Nat.floor_lt (Real.exp_pos _).le).mp (mem_Ioc.mp (mem_filter.mp hp3).1).1
  have hsecond : ExpLogPrimeBand.lower N ≤ ExpLogPrimeBand.upper N := by
    change Real.exp ((SlowPrimeBandSieve.lower N)^2) ≤ Real.exp ((SlowPrimeBandSieve.lower N)^3)
    exact Real.exp_le_exp.mpr (pow_le_pow_right₀ hx (by norm_num : (2 : ℕ) ≤ 3))
  linarith only [hpU,hpL,h12,h23,hsecond]

theorem prime_bounds (B N : ℕ) (hB : 32 ≤ B) (hN : 1 ≤ N)
    (p : ℕ) (hp : p ∈ FinalPrimeBandGeometry.primes B N) :
    1 ≤ p ∧ (p : ℝ) ≤ (N : ℝ)^(1/16 : ℝ) := by
  have hprime := (mem_filter.mp hp).2
  have hUpper : (p : ℝ) ≤ FinalPrimeBandGeometry.upper B N := by
    have hh : (p : ℝ) ≤ (⌊FinalPrimeBandGeometry.upper B N⌋₊ : ℝ) := by
      exact_mod_cast (mem_Ioc.mp (mem_filter.mp hp).1).2
    exact hh.trans (Nat.floor_le (Real.exp_pos _).le)
  have hBR : (32 : ℝ) ≤ B := by exact_mod_cast hB
  have hBp : (0 : ℝ) < B := by linarith only [hBR]
  have hExp : 1/(B : ℝ) ≤ 1/16 := (div_le_iff₀ hBp).mpr (by linarith only [hBR])
  refine ⟨hprime.one_lt.le,?_⟩
  rw [FinalPrimeBandSieve.upper_rpow B N (by omega)] at hUpper
  exact hUpper.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) hExp)
end PaperP1.FinalPrimeBandPopulation
