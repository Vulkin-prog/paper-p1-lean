module

public import PaperP1.Analysis.FlexiblePrimeBandSieve
public import PaperP1.Analysis.PowerLogPrimeBand
public import PaperP1.Analysis.ExpLogPrimeBand

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.TwoPrimeBandPopulation
open Finset Filter PaperP1
open scoped Classical

def first (N : ℕ) : Finset ℕ := PowerLogPrimeBand.primes 1000 N
def second (N : ℕ) : Finset ℕ := ExpLogPrimeBand.primes N
def good (N : ℕ) : Finset ℕ :=
  FlexiblePrimeBandSieve.good (PowerLogPrimeBand.lower 1000) PowerLogPrimeBand.upper N ∩
  FlexiblePrimeBandSieve.good ExpLogPrimeBand.lower ExpLogPrimeBand.upper N

theorem good_subset (N : ℕ) : good N ⊆ Ico N (2*N) := by
  intro n hn
  exact (Finset.mem_sdiff.mp (mem_inter.mp hn).1).1

theorem good_support (N : ℕ) (hN : 0 < N) (n : ℕ) (hn : n ∈ good N) :
    (0 < n ∧ n ≤ 2*N) ∧ 0 < PrimeDivisorWeights.count (first N) n ∧
      0 < PrimeDivisorWeights.count (second N) n ∧
      (∀ p ∈ first N, ¬p^2 ∣ n) ∧ (∀ p ∈ second N, ¬p^2 ∣ n) := by
  obtain ⟨h1,h2⟩ := mem_inter.mp hn
  have hh1 := FlexiblePrimeBandSieve.good_support (PowerLogPrimeBand.lower 1000)
    PowerLogPrimeBand.upper N hN n h1
  have hh2 := FlexiblePrimeBandSieve.good_support ExpLogPrimeBand.lower
    ExpLogPrimeBand.upper N hN n h2
  exact ⟨hh1.1,hh1.2.1,hh2.2.1,hh1.2.2,hh2.2.2⟩

theorem missing_good_density_tendsto :
    Tendsto (fun N : ℕ ↦ ((Ico N (2*N) \ good N).card : ℝ)/(N : ℝ)) atTop (nhds 0) := by
  have h1 := PowerLogPrimeBand.missing_good_density_tendsto 1000 (by norm_num)
  have h2 := ExpLogPrimeBand.missing_good_density_tendsto
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (by simpa only [add_zero] using h1.add h2)
  · exact Filter.Eventually.of_forall (fun N ↦ by positivity)
  · apply Filter.Eventually.of_forall
    intro N
    have he : Ico N (2*N) \ good N =
        (Ico N (2*N) \ FlexiblePrimeBandSieve.good (PowerLogPrimeBand.lower 1000) PowerLogPrimeBand.upper N) ∪
        (Ico N (2*N) \ FlexiblePrimeBandSieve.good ExpLogPrimeBand.lower ExpLogPrimeBand.upper N) := by
      ext n
      simp only [good,Finset.mem_sdiff,mem_inter,mem_union]
      tauto
    rw [he]
    have hc : (((Ico N (2*N) \ FlexiblePrimeBandSieve.good (PowerLogPrimeBand.lower 1000) PowerLogPrimeBand.upper N) ∪
        (Ico N (2*N) \ FlexiblePrimeBandSieve.good ExpLogPrimeBand.lower ExpLogPrimeBand.upper N)).card : ℝ) ≤
        ((Ico N (2*N) \ FlexiblePrimeBandSieve.good (PowerLogPrimeBand.lower 1000) PowerLogPrimeBand.upper N).card : ℝ)+
        ((Ico N (2*N) \ FlexiblePrimeBandSieve.good ExpLogPrimeBand.lower ExpLogPrimeBand.upper N).card : ℝ) := by
      exact_mod_cast card_union_le _ _
    simpa only [add_div] using div_le_div_of_nonneg_right hc (Nat.cast_nonneg N : (0 : ℝ) ≤ N)

theorem separation_eventually :
    ∀ᶠ N in atTop, PowerLogPrimeBand.upper N < ExpLogPrimeBand.lower N := by
  filter_upwards [SlowPrimeBandSieve.lower_tendsto.eventually (eventually_ge_atTop 2),
    SlowPrimeBandSieve.upper_tendsto.eventually (eventually_ge_atTop 1)] with N hl hu
  have hUp : 0 < SlowPrimeBandSieve.upper N := by linarith
  have he : Real.exp (SlowPrimeBandSieve.lower N)=PowerLogPrimeBand.upper N := Real.exp_log hUp
  rw [← he]
  change Real.exp (SlowPrimeBandSieve.lower N) < Real.exp ((SlowPrimeBandSieve.lower N)^2)
  apply Real.exp_lt_exp.mpr
  nlinarith

theorem disjoint_eventually : ∀ᶠ N in atTop, Disjoint (first N) (second N) := by
  filter_upwards [separation_eventually,SlowPrimeBandSieve.upper_tendsto.eventually (eventually_ge_atTop 0)] with N hsep hu0
  apply Finset.disjoint_left.mpr
  intro p hp1 hp2
  have hu : (p : ℝ) ≤ PowerLogPrimeBand.upper N := by
    have hp := (mem_Ioc.mp (mem_filter.mp hp1).1).2
    exact (by exact_mod_cast hp : (p : ℝ) ≤ (⌊PowerLogPrimeBand.upper N⌋₊ : ℝ)).trans
      (Nat.floor_le hu0)
  have hl : ExpLogPrimeBand.lower N < (p : ℝ) :=
    (Nat.floor_lt (Real.exp_pos _).le).mp (mem_Ioc.mp (mem_filter.mp hp2).1).1
  linarith

theorem first_subset_slow_eventually : ∀ᶠ N in atTop, first N ⊆ SlowPrimeBandSieve.primes N := by
  filter_upwards [SlowPrimeBandSieve.lower_tendsto.eventually (eventually_ge_atTop 1)] with N hl
  have hp : SlowPrimeBandSieve.lower N ≤ PowerLogPrimeBand.lower 1000 N := by
    simpa only [PowerLogPrimeBand.lower,pow_one] using
      pow_le_pow_right₀ hl (by norm_num : (1 : ℕ) ≤ 1000)
  intro p hmem
  obtain ⟨hint,hprime⟩ := mem_filter.mp hmem
  exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨(Nat.floor_mono hp).trans_lt (mem_Ioc.mp hint).1,(mem_Ioc.mp hint).2⟩,hprime⟩

theorem first_below_polynomial_eventually (a : ℝ) (ha : 0 < a) :
    ∀ᶠ N in atTop, ∀ p ∈ first N, p ≤ ⌊(N : ℝ)^a⌋₊ := by
  filter_upwards [first_subset_slow_eventually,SlowPrimeBandSieve.primes_below_polynomial_cutoff_eventually a ha] with N hsub hcut
  exact fun p hp ↦ hcut p (hsub hp)

theorem second_below_polynomial_eventually (a : ℝ) (ha : 0 < a) :
    ∀ᶠ N in atTop, ∀ p ∈ second N, p ≤ ⌊(N : ℝ)^a⌋₊ := by
  have hr : Tendsto (fun N : ℕ ↦ (SlowPrimeBandSieve.lower N)^3/SlowPrimeBandSieve.upper N) atTop (nhds 0) := by
    simpa only [SlowPrimeBandSieve.lower,SlowPrimeBandSieve.upper,Function.comp_def,
      Real.rpow_ofNat,Real.rpow_one] using
      (PNT.tendsto_pow_log_div_pow_atTop 1 3 zero_lt_one).comp SlowPrimeBandSieve.upper_tendsto
  filter_upwards [eventually_ge_atTop 2,hr.eventually (eventually_lt_nhds ha)] with N hN hs
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 < SlowPrimeBandSieve.upper N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hupper : ExpLogPrimeBand.upper N ≤ (N : ℝ)^a := by
    rw [Real.rpow_def_of_pos hNp]
    apply Real.exp_le_exp.mpr
    have hh := (div_lt_iff₀ hlog).mp hs
    change (SlowPrimeBandSieve.lower N)^3 < a*Real.log (N : ℝ) at hh
    linarith
  intro p hp
  exact (mem_Ioc.mp (mem_filter.mp hp).1).2.trans (Nat.floor_mono hupper)

theorem first_ramare_sum (N : ℕ) (hN : 0 < N) (f : ℕ → ℂ)
    (hf : ∀ a b, f (a*b)=f a*f b) :
    (∑ n ∈ good N, f n)=∑ p ∈ first N, ∑ m ∈ Icc 1 (2*N/p),
      if p*m ∈ good N then f p*f m/((PrimeDivisorWeights.count (first N) m+1 : ℕ) : ℂ) else 0 := by
  exact PrimeDivisorWeights.ramare_sum (good N) (first N) (2*N)
    (fun p hp ↦ (mem_filter.mp hp).2) (fun n hn ↦ (good_support N hN n hn).1)
    (fun n hn ↦ (good_support N hN n hn).2.1) (fun n hn ↦ (good_support N hN n hn).2.2.2.1) f hf

theorem second_ramare_sum (N : ℕ) (hN : 0 < N) (f : ℕ → ℂ)
    (hf : ∀ a b, f (a*b)=f a*f b) :
    (∑ n ∈ good N, f n)=∑ p ∈ second N, ∑ m ∈ Icc 1 (2*N/p),
      if p*m ∈ good N then f p*f m/((PrimeDivisorWeights.count (second N) m+1 : ℕ) : ℂ) else 0 := by
  exact PrimeDivisorWeights.ramare_sum (good N) (second N) (2*N)
    (fun p hp ↦ (mem_filter.mp hp).2) (fun n hn ↦ (good_support N hN n hn).1)
    (fun n hn ↦ (good_support N hN n hn).2.2.1) (fun n hn ↦ (good_support N hN n hn).2.2.2.2) f hf
end PaperP1.TwoPrimeBandPopulation
