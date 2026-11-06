module

public import PaperP1.Analysis.TwoPrimeBandPopulation
public import PaperP1.Analysis.PrecisionChosenPrimeBand
public import PaperP1.PNT.LogGrowth


set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.PrecisionPowerPopulation
open Finset Filter PaperP1
open scoped Classical

def good (a b : ℝ) (N : ℕ) : Finset ℕ := TwoPrimeBandPopulation.good N ∩
  FlexiblePrimeBandSieve.good (FixedPowerPrimeBand.lower a) (FixedPowerPrimeBand.lower b) N

theorem good_subset (a b : ℝ) (N : ℕ) : good a b N ⊆ Ico N (2*N) := by
  intro n hn
  exact TwoPrimeBandPopulation.good_subset N (mem_inter.mp hn).1

theorem good_support (a b : ℝ) (N : ℕ) (hN : 0 < N) (n : ℕ) (hn : n ∈ good a b N) :
    (0 < n ∧ n ≤ 2*N) ∧ 0 < PrimeDivisorWeights.count (TwoPrimeBandPopulation.first N) n ∧
      0 < PrimeDivisorWeights.count (FixedPowerPrimeBand.primes a b N) n ∧
      ∀ p ∈ FixedPowerPrimeBand.primes a b N, ¬p^2 ∣ n := by
  obtain ⟨hFirst,hFinal⟩ := mem_inter.mp hn
  have hQ := TwoPrimeBandPopulation.good_support N hN n hFirst
  have hP := FlexiblePrimeBandSieve.good_support (FixedPowerPrimeBand.lower a) (FixedPowerPrimeBand.lower b) N hN n hFinal
  exact ⟨hQ.1,hQ.2.1,hP.2.1,hP.2.2⟩

theorem missing_good_le_sum (a b : ℝ) (N : ℕ) :
    ((Ico N (2*N) \ good a b N).card : ℝ)/(N : ℝ) ≤
      ((Ico N (2*N) \ TwoPrimeBandPopulation.good N).card : ℝ)/(N : ℝ)+
      ((Ico N (2*N) \ FlexiblePrimeBandSieve.good (FixedPowerPrimeBand.lower a) (FixedPowerPrimeBand.lower b) N).card : ℝ)/(N : ℝ) := by
  have he : Ico N (2*N) \ good a b N=
      (Ico N (2*N) \ TwoPrimeBandPopulation.good N) ∪
      (Ico N (2*N) \ FlexiblePrimeBandSieve.good (FixedPowerPrimeBand.lower a) (FixedPowerPrimeBand.lower b) N) := by
    ext n
    simp only [good,Finset.mem_sdiff,Finset.mem_inter,Finset.mem_union]
    tauto
  rw [he]
  have hc : (((Ico N (2*N) \ TwoPrimeBandPopulation.good N) ∪
      (Ico N (2*N) \ FlexiblePrimeBandSieve.good (FixedPowerPrimeBand.lower a) (FixedPowerPrimeBand.lower b) N)).card : ℝ) ≤
      ((Ico N (2*N) \ TwoPrimeBandPopulation.good N).card : ℝ)+
      ((Ico N (2*N) \ FlexiblePrimeBandSieve.good (FixedPowerPrimeBand.lower a) (FixedPowerPrimeBand.lower b) N).card : ℝ) := by
    exact_mod_cast card_union_le _ _
  simpa only [add_div] using div_le_div_of_nonneg_right hc (Nat.cast_nonneg N : (0 : ℝ) ≤ N)

theorem precision_choice (ε : ℝ) (hε : 0 < ε) :
    ∃ a : ℝ, 0 < a ∧ a < 1/32 ∧ ∀ᶠ N : ℕ in atTop,
      ((Ico N (2*N) \ good a (1/32) N).card : ℝ)/(N : ℝ) ≤ ε := by
  obtain ⟨a,ha,hab,hFinal⟩ := PrecisionChosenPrimeBand.small_final_band (ε/2) (by positivity)
  refine ⟨a,ha,hab,?_⟩
  have hFirst := TwoPrimeBandPopulation.missing_good_density_tendsto.eventually
    (eventually_lt_nhds (by positivity : (0 : ℝ) < ε/2))
  filter_upwards [hFinal,hFirst] with N hP hQ
  exact (missing_good_le_sum a (1/32) N).trans (by linarith only [hP,hQ])

theorem disjoint_first_eventually (a b : ℝ) (ha : 0 < a) :
    ∀ᶠ N : ℕ in atTop, Disjoint (FixedPowerPrimeBand.primes a b N) (TwoPrimeBandPopulation.first N) := by
  have hRatio : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)/(N : ℝ)^a) atTop (nhds 0) := by
    simpa only [Function.comp_def,Real.rpow_one] using (PNT.tendsto_pow_log_div_pow_atTop a 1 ha).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [hRatio.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ)<1)),eventually_ge_atTop 1] with N hSmall hN
  have hNP : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hSeparation : Real.log (N : ℝ) < (N : ℝ)^a := (div_lt_one (Real.rpow_pos_of_pos hNP a)).mp hSmall
  apply Finset.disjoint_left.mpr
  intro p hpP hpQ
  have hpLower : (N : ℝ)^a < (p : ℝ) := (FixedPowerPrimeBand.mem_primes a b N p hpP).2.1
  have hpUpper : (p : ℝ) ≤ Real.log (N : ℝ) := by
    have hh : (p : ℝ) ≤ (⌊PowerLogPrimeBand.upper N⌋₊ : ℝ) := by
      exact_mod_cast (mem_Ioc.mp (mem_filter.mp hpQ).1).2
    exact hh.trans (Nat.floor_le (Real.log_natCast_nonneg N))
  linarith only [hpLower,hpUpper,hSeparation]
end PaperP1.PrecisionPowerPopulation
