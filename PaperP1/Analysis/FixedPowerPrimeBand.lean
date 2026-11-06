module

public import PaperP1.Analysis.FlexiblePrimeBandSieve

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.FixedPowerPrimeBand
open Finset Filter PaperP1
open scoped Classical

def lower (a : ℝ) (N : ℕ) : ℝ := (N : ℝ)^a

def primes (a b : ℝ) (N : ℕ) : Finset ℕ := FlexiblePrimeBandSieve.band (lower a) (lower b) N

theorem lower_tendsto (a : ℝ) (ha : 0 < a) : Tendsto (lower a) atTop atTop :=
  (tendsto_rpow_atTop ha).comp (tendsto_natCast_atTop_atTop (R := ℝ))

theorem geometry_eventually (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∀ᶠ N : ℕ in atTop, 2 ≤ lower a N ∧ lower a N ≤ lower b N := by
  filter_upwards [(lower_tendsto a ha).eventually (eventually_ge_atTop 2),eventually_ge_atTop 1] with N hLower hN
  exact ⟨hLower,Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN : (1 : ℝ) ≤ N) hab⟩

theorem mem_primes (a b : ℝ) (N p : ℕ) (hp : p ∈ primes a b N) :
    p.Prime ∧ lower a N < (p : ℝ) ∧ (p : ℝ) ≤ lower b N := by
  obtain ⟨hInt,hPrime⟩ := mem_filter.mp hp
  obtain ⟨hLow,hUp⟩ := mem_Ioc.mp hInt
  have hLowerNN : 0 ≤ lower a N := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hUpperNN : 0 ≤ lower b N := Real.rpow_nonneg (Nat.cast_nonneg N) _
  exact ⟨hPrime,(Nat.floor_lt hLowerNN).mp hLow,
    (by exact_mod_cast hUp : (p : ℝ) ≤ ⌊lower b N⌋₊).trans (Nat.floor_le hUpperNN)⟩

theorem logarithmic_gap (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (N : ℕ) (hN : 1 < N) :
    Real.log (Real.log (lower b N))-Real.log (Real.log (lower a N))=Real.log (b/a) := by
  have hNP : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hLog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN)
  unfold lower
  rw [Real.log_rpow hNP,Real.log_rpow hNP,
    Real.log_mul hb.ne' hLog.ne',Real.log_mul ha.ne' hLog.ne',Real.log_div hb.ne' ha.ne']
  ring

theorem reciprocal_mass_tendsto (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    Tendsto (fun N ↦ PrimeAvoidanceSieve.reciprocalMass (primes a b N)) atTop (nhds (Real.log (b/a))) := by
  have hb : 0 < b := ha.trans_le hab
  have hLogLim := Real.tendsto_log_atTop.comp (lower_tendsto a ha)
  have hError : Tendsto (fun N ↦ 2*PrimeLogMertens.budget/Real.log (lower a N)) atTop (nhds 0) := by
    have hh := (tendsto_inv_atTop_zero.comp hLogLim).const_mul (2*PrimeLogMertens.budget)
    simpa only [Function.comp_def,div_eq_mul_inv,mul_zero] using hh
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [geometry_eventually a b ha hab,eventually_ge_atTop 2,
    hError.eventually (eventually_lt_nhds hε)] with N hGeom hN hSmall
  rw [Real.dist_eq]
  have hh := PrimeHarmonicWindow.finite_window_bound (lower a N) (lower b N) hGeom.1 hGeom.2
  rw [logarithmic_gap a b ha hb N (by omega)] at hh
  exact hh.trans_lt hSmall

theorem mass_eventually_lower (a b M : ℝ) (ha : 0 < a) (hab : a ≤ b) (hM : M < Real.log (b/a)) :
    ∀ᶠ N : ℕ in atTop, M ≤ PrimeAvoidanceSieve.reciprocalMass (primes a b N) := by
  have hh := (tendsto_order.mp (reciprocal_mass_tendsto a b ha hab)).1 M hM
  exact hh.mono (fun _ h ↦ h.le)
end PaperP1.FixedPowerPrimeBand
