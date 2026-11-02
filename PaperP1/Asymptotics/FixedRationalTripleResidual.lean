module

public import PaperP1.Arithmetic.RationalTripleUnionGeometry
public import PaperP1.Arithmetic.IntervalResidualKernel
public import PaperP1.Asymptotics.CriticalWindowGeometry
public import PaperP1.Asymptotics.CriticalPolynomialScale

/-! # The full normalized-value defect is uniformly sublinear at fixed rational slope height -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FixedRationalTripleResidual

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.PrivateNormalizedFamilies
  PaperP1.RationalTripleNormalizers PaperP1.IntervalResidualKernel PaperP1.CriticalBandScale

theorem full_kernel_rate (Q : ℕ) (hQ : 1 ≤ Q) :
    ∃ K : ℝ, 0 < K ∧ ∀ C : ℝ, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L u v w t : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      2 ≤ u → u ≤ v → v ≤ w → w ≤ Q → 1 ≤ t → u * t ∈ dyadicBlock N →
      (Module.finrank F₂ (FiniteResidualRank.valueKernel (valueUnion (scale u v w) (centres u v w t) L)) : ℝ) ≤
        K * ((L + 1 : ℕ) : ℝ) / Real.log ((L + 1 : ℕ) : ℝ) := by
  have hq : (0 : ℝ) < (Q ^ 2 : ℕ) := by exact_mod_cast (Nat.pow_pos (by omega : 0 < Q))
  obtain ⟨K, hK, ND, hd⟩ := LocalDefectWindowScale.local_defect_count_le_window_scale_eventually
    (1 / 2) (2 * (Q ^ 2 : ℕ)) lowerScale upperScale (2 * (Q ^ 2 : ℕ)) (2 * (Q ^ 2 : ℕ))
    (by norm_num) (by positivity) lowerScale_pos upperScale_pos.le (by positivity) (by positivity)
  refine ⟨K, hK, fun C ↦ ?_⟩
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NP, hp⟩ := CriticalPolynomialScale.polynomial_lt_scale C ((8 * Q ^ 2 : ℕ) : ℝ) (by positivity) 1
  refine ⟨max ND (max NG NP), ?_⟩
  intro N hN L u v w t hband hu huv hvw hwQ ht hx
  obtain ⟨_hN2, _hBmin, _hBtwo, _hthin, hBlo, hBhi⟩ := hg N (by omega) L hband
  have hthin : 8 * Q ^ 2 * (L + 1) ≤ N := by
    have hh := hp N (by omega) L hband
    norm_num only [pow_one] at hh
    exact_mod_cast hh.le
  let U := origin u v w t - Q ^ 2 * (L + 1)
  let R := 2 * Q ^ 2 * (L + 1)
  have hdata := RationalTripleUnionGeometry.interval_data hu huv hvw hwQ ht hx hthin
  change valueUnion (scale u v w) (centres u v w t) L ⊆ Icc U (U + R) ∧
    N ≤ 2 * U ∧ U ≤ 2 * Q ^ 2 * N at hdata
  have hcut : (R : ℝ) ≤ (2 * (Q ^ 2 : ℕ)) * ((L + 1 : ℕ) : ℝ) := by dsimp only [R]; push_cast; rfl
  have hlo : (1 / 2 : ℝ) * N ≤ U := by
    have hh : (N : ℝ) ≤ 2 * U := by exact_mod_cast hdata.2.1
    linarith only [hh]
  have hhi : (U : ℝ) ≤ (2 * (Q ^ 2 : ℕ)) * N := by exact_mod_cast hdata.2.2
  have hdef := hd N (by omega) ((L + 1 : ℕ) : ℝ) R U R hBlo hBhi hcut hcut hlo hhi
  have hfull := Submodule.finrank_mono
    (fullKernel_le_large (valueUnion (scale u v w) (centres u v w t) L) R)
  have hlarge := rank_le_interval_defects (le_refl R) hdata.1
  exact (by exact_mod_cast hfull.trans hlarge :
    (Module.finrank F₂ (FiniteResidualRank.valueKernel (valueUnion (scale u v w) (centres u v w t) L)) : ℝ) ≤
      (LocalDefectBound.defectsInInterval R U R).card).trans hdef

theorem full_kernel_sublinear (Q : ℕ) (hQ : 1 ≤ Q) (C η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L u v w t : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      2 ≤ u → u ≤ v → v ≤ w → w ≤ Q → 1 ≤ t → u * t ∈ dyadicBlock N →
      (Module.finrank F₂ (FiniteResidualRank.valueKernel (valueUnion (scale u v w) (centres u v w t) L)) : ℝ) ≤
        η * (L + 1) := by
  obtain ⟨K, hK, hr⟩ := full_kernel_rate Q hQ
  obtain ⟨NR, hr⟩ := hr C
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C (⌈Real.exp (K / η)⌉₊ + 2)
  refine ⟨max 10 (max NR NG), by omega, ?_⟩
  intro N hN L u v w t hband hu huv hvw hwQ ht hx
  obtain ⟨_hN2, hBmin, hBtwo, _hthin, _hBlo, _hBhi⟩ := hg N (by omega) L hband
  have hB : (0 : ℝ) < (L + 1 : ℕ) := by positivity
  have hlog : 0 < Real.log ((L + 1 : ℕ) : ℝ) := Real.log_pos (by exact_mod_cast hBtwo)
  have hlarge : Real.exp (K / η) ≤ ((L + 1 : ℕ) : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈Real.exp (K / η)⌉₊ ≤ L + 1 by omega))
  have hratio : K / η ≤ Real.log ((L + 1 : ℕ) : ℝ) := by
    have hh := Real.log_le_log (Real.exp_pos _) hlarge
    simpa only [Real.log_exp] using hh
  have hfactor : K / Real.log ((L + 1 : ℕ) : ℝ) ≤ η := by
    apply (div_le_iff₀ hlog).mpr
    have hh := (div_le_iff₀ hη).mp hratio
    nlinarith only [hh]
  calc
    _ ≤ K * ((L + 1 : ℕ) : ℝ) / Real.log ((L + 1 : ℕ) : ℝ) :=
      hr N (by omega) L u v w t hband hu huv hvw hwQ ht hx
    _ = (K / Real.log ((L + 1 : ℕ) : ℝ)) * ((L + 1 : ℕ) : ℝ) := by ring
    _ ≤ η * ((L + 1 : ℕ) : ℝ) := mul_le_mul_of_nonneg_right hfactor hB.le
    _ = _ := by push_cast; rfl

end PaperP1.FixedRationalTripleResidual
