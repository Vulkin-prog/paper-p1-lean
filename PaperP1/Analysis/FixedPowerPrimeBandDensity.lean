module

public import PaperP1.Analysis.FlexiblePrimeBandSieve
public import PaperP1.Analysis.BoundedPrimeMassSieve
public import PaperP1.Analysis.FixedPowerPrimeBand

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.FixedPowerPrimeBandDensity
open Finset Filter PaperP1 FixedPowerPrimeBand
open scoped Classical

theorem upper_square_identity (b : ℝ) (N : ℕ) (hN : 0 < N) :
    (lower b N)^2/(N : ℝ)=1/(N : ℝ)^(1-2*b) := by
  have hNP : (0 : ℝ) < N := by exact_mod_cast hN
  unfold lower
  rw [← Real.rpow_natCast,← Real.rpow_mul hNP.le]
  norm_num only [Nat.cast_ofNat]
  rw [Real.rpow_sub hNP,Real.rpow_one,show b*2=2*b by ring]
  field_simp [hNP.ne',(Real.rpow_pos_of_pos hNP (2*b)).ne']

theorem upper_square_tendsto (b : ℝ) (hb : b < 1/2) :
    Tendsto (fun N : ℕ ↦ (lower b N)^2/(N : ℝ)) atTop (nhds 0) := by
  have hc : 0 < 1-2*b := by linarith only [hb]
  have hh := tendsto_inv_atTop_zero.comp ((tendsto_rpow_atTop hc).comp (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hLimit : Tendsto (fun N : ℕ ↦ 1/(N : ℝ)^(1-2*b)) atTop (nhds 0) := by
    simpa only [Function.comp_def,one_div] using hh
  apply hLimit.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact (upper_square_identity b N (by omega)).symm

theorem card_square_tendsto (a b : ℝ) (hb : b < 1/2) :
    Tendsto (fun N : ℕ ↦ ((primes a b N).card : ℝ)^2/(N : ℝ)) atTop (nhds 0) := by
  exact FlexiblePrimeBandSieve.normalized_card_square_tendsto (lower a) (lower b)
    (Filter.Eventually.of_forall (fun N ↦ Real.rpow_nonneg (Nat.cast_nonneg N) b)) (upper_square_tendsto b hb)

theorem square_density_tendsto (a b : ℝ) (ha : 0 < a) :
    Tendsto (fun N : ℕ ↦ ((PrimeDivisorWeights.squareExceptions (primes a b N) (2*N)).card : ℝ)/(N : ℝ))
      atTop (nhds 0) :=
  FlexiblePrimeBandSieve.square_density_tendsto (lower a) (lower b) (lower_tendsto a ha)

theorem excluded_eventually_bound (a b M ε : ℝ) (ha : 0 < a) (hab : a ≤ b) (hb : b < 1/2)
    (hM : 0 < M) (hMass : M < Real.log (b/a)) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      ((FlexiblePrimeBandSieve.excluded (lower a) (lower b) N).card : ℝ)/(N : ℝ) ≤ 2/M+ε := by
  exact BoundedPrimeMassSieve.excluded_eventually_bound
    (primes a b) (fun N ↦ PrimeDivisorWeights.squareExceptions (primes a b N) (2*N))
    (fun N p hp ↦ (mem_primes a b N p hp).1) M hM (mass_eventually_lower a b M ha hab hMass)
    (card_square_tendsto a b hb) (square_density_tendsto a b ha) ε hε

theorem missing_good_eventually_bound (a b M ε : ℝ) (ha : 0 < a) (hab : a ≤ b) (hb : b < 1/2)
    (hM : 0 < M) (hMass : M < Real.log (b/a)) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      ((Ico N (2*N) \ FlexiblePrimeBandSieve.good (lower a) (lower b) N).card : ℝ)/(N : ℝ) ≤ 2/M+ε := by
  filter_upwards [excluded_eventually_bound a b M ε ha hab hb hM hMass hε] with N hN
  have hSub : Ico N (2*N) \ FlexiblePrimeBandSieve.good (lower a) (lower b) N ⊆
      FlexiblePrimeBandSieve.excluded (lower a) (lower b) N := by
    intro n hn
    by_contra hnot
    exact (mem_sdiff.mp hn).2 (mem_sdiff.mpr ⟨(mem_sdiff.mp hn).1,hnot⟩)
  have hCard : ((Ico N (2*N) \ FlexiblePrimeBandSieve.good (lower a) (lower b) N).card : ℝ) ≤
      (FlexiblePrimeBandSieve.excluded (lower a) (lower b) N).card := by exact_mod_cast card_le_card hSub
  exact (div_le_div_of_nonneg_right hCard (Nat.cast_nonneg N)).trans hN
end PaperP1.FixedPowerPrimeBandDensity
