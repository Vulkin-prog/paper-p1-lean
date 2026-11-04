module

public import PaperP1.Asymptotics.MacroscopicRootLogScale
public import PaperP1.Asymptotics.MacroscopicPolynomialScale
public import PaperP1.Arithmetic.IntervalResidualKernel
public import PaperP1.Arithmetic.EnlargedPairGeometry
public import PaperP1.Arithmetic.NormalizedPairRankLoss

/-! # Fixed-height residual rank at every actual macroscopic source

The common constant precedes the critical-band constant. The local defect
theorem is applied at the actual source x, with its own transported word
scale, and includes the full enlarged alignment with zero exact units.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MacroscopicFixedHeightResidual

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.NormalizedWindowSets
  PaperP1.EnlargedPairGeometry PaperP1.IntervalResidualKernel PaperP1.CriticalBandScale
  PaperP1.MacroscopicIntervalGeometry

theorem large_kernel_rate (Q : ℕ) (hQ : 1 ≤ Q) (δ : ℝ) (hδ : 0 < δ) (D : ℝ) (hD : 0 ≤ D) :
    ∃ K : ℝ, 0 < K ∧ ∀ C : ℝ, ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2, ∀ L a b x y H : ℕ,
      |(L : ℝ) - Real.log M / Real.log 2| ≤ C →
      0 < a → a ≤ b → b ≤ Q → x ∈ starts M δ → y ∈ starts M δ →
      Geometric a b x y L → 2 * radius b L ≤ H → (H : ℝ) ≤ D * ((L + 1 : ℕ) : ℝ) →
      (Module.finrank F₂ (largeKernel (NormalizedWindowSets.union a b x y L) H) : ℝ) ≤
        K * ((L + 1 : ℕ) : ℝ) / Real.log ((L + 1 : ℕ) : ℝ) := by
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  obtain ⟨K, hK, Ncore, hcore⟩ := LocalDefectWindowScale.local_defect_count_le_window_scale_eventually
    (1 / 2) (2 * Q) lowerScale (upperScale / δ) D (6 * Q)
    (by norm_num) (by positivity) lowerScale_pos (div_nonneg upperScale_pos.le hδ.le) hD (by positivity)
  refine ⟨K, hK, fun C ↦ ?_⟩
  obtain ⟨MB, hB⟩ := PaperP1.MacroscopicRootLogScale.root_band C δ hδ
  obtain ⟨MG, hG⟩ := uniform_geometry C δ 2 hδ
  obtain ⟨MP, hP⟩ := PaperP1.MacroscopicPolynomialScale.polynomial_lt_source C δ
    ((24 * Q + Ncore + 8 : ℕ) : ℝ) hδ (Nat.cast_nonneg _) 1
  refine ⟨max MB (max MG MP), ?_⟩
  intro M hM L a b x y H hcrit ha hab hbQ hx hy halign hRH hH
  obtain ⟨hBlo, hBhi⟩ := hB M (by omega) L hcrit x hx
  obtain ⟨hBtwo, _hbase, _hlogLarge, _hlogWidth⟩ := hG M (by omega) L hcrit x hx
  have hpolyNat : (24 * Q + Ncore + 8) * (L + 1) < x := by
    have hp := hP M (by omega) L hcrit x hx
    rw [pow_one] at hp
    exact_mod_cast hp
  have hsmall : (24 * Q + 8) * (L + 1) < x :=
    (Nat.mul_le_mul_right (L + 1) (by omega : 24 * Q + 8 ≤ 24 * Q + Ncore + 8)).trans_lt hpolyNat
  have hxCore : Ncore ≤ x := by
    have hA : Ncore ≤ 24 * Q + Ncore + 8 := by omega
    have hm := Nat.mul_le_mul_left (24 * Q + Ncore + 8) (by omega : 1 ≤ L + 1)
    rw [Nat.mul_one] at hm
    exact (hA.trans hm).trans hpolyNat.le
  have hrad : radius b L ≤ 3 * (Q * (L + 1)) := by
    unfold radius
    exact Nat.mul_le_mul_left 3 (Nat.mul_le_mul_right (L + 1) hbQ)
  have hlarge : 8 * radius b L + 8 ≤ x := by
    have hm := Nat.mul_le_mul_left 8 hrad
    nlinarith only [hsmall, hBtwo, hm]
  have hxpos : 0 < x := by have := starts_pos (by omega : 2 ≤ M) hδ hx; omega
  have hypos : 0 < y := by have := starts_pos (by omega : 2 ≤ M) hδ hy; omega
  have hb : 0 < b := ha.trans_le hab
  have hbase := base_geometry hb (le_refl x) hlarge
  let U : ℕ := base b x L
  let R : ℕ := 2 * radius b L
  have hS : NormalizedWindowSets.union a b x y L ⊆ Icc U (U + R) := by
    intro n hn
    exact mem_Icc.mpr (interval_bounds hab hxpos hypos halign hbase.1 n hn)
  have hRscale : (R : ℝ) ≤ (6 * (Q : ℝ)) * ((L + 1 : ℕ) : ℝ) := by
    have hwidth : R ≤ 6 * Q * (L + 1) := by dsimp [R]; nlinarith only [hrad]
    exact_mod_cast hwidth
  have hUlo : (1 / 2 : ℝ) * x ≤ U := by
    have hh : (x : ℝ) ≤ 2 * U := by exact_mod_cast hbase.2.1
    linarith only [hh]
  have hUhi : (U : ℝ) ≤ (2 * (Q : ℝ)) * x := by
    have hmul := Nat.mul_le_mul_right x hbQ
    have hsub : U ≤ b * x := Nat.sub_le _ _
    have hh : (U : ℝ) ≤ (Q : ℝ) * x := by exact_mod_cast hsub.trans hmul
    nlinarith only [hh, Nat.cast_nonneg (α := ℝ) (Q * x)]
  have hdef := hcore x hxCore ((L + 1 : ℕ) : ℝ) H U R hBlo hBhi hH hRscale hUlo hUhi
  have hrank : (Module.finrank F₂ (largeKernel (NormalizedWindowSets.union a b x y L) H) : ℝ) ≤
      (LocalDefectBound.defectsInInterval H U R).card := by
    exact_mod_cast rank_le_interval_defects hRH hS
  exact hrank.trans hdef

theorem full_kernel_rate (Q : ℕ) (hQ : 1 ≤ Q) (δ : ℝ) (hδ : 0 < δ) :
    ∃ K : ℝ, 0 < K ∧ ∀ C : ℝ, ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2, ∀ L a b x y : ℕ,
      |(L : ℝ) - Real.log M / Real.log 2| ≤ C →
      0 < a → a ≤ b → b ≤ Q → x ∈ starts M δ → y ∈ starts M δ → Geometric a b x y L →
      (Module.finrank F₂ (FiniteResidualRank.valueKernel (NormalizedWindowSets.union a b x y L)) : ℝ) ≤
        K * ((L + 1 : ℕ) : ℝ) / Real.log ((L + 1 : ℕ) : ℝ) := by
  obtain ⟨K, hK, hcore⟩ := large_kernel_rate Q hQ δ hδ (6 * (Q : ℝ)) (by positivity)
  refine ⟨K, hK, fun C ↦ ?_⟩
  obtain ⟨M₀, h⟩ := hcore C
  refine ⟨M₀, ?_⟩
  intro M hM L a b x y hcrit ha hab hbQ hx hy halign
  have hrad : radius b L ≤ 3 * (Q * (L + 1)) := by
    unfold radius
    exact Nat.mul_le_mul_left 3 (Nat.mul_le_mul_right (L + 1) hbQ)
  have hcut : 2 * radius b L ≤ 6 * Q * (L + 1) := by nlinarith only [hrad]
  have hheight : ((6 * Q * (L + 1) : ℕ) : ℝ) ≤ (6 * (Q : ℝ)) * ((L + 1 : ℕ) : ℝ) := by push_cast; rfl
  have hlarge := h M hM L a b x y (6 * Q * (L + 1)) hcrit ha hab hbQ hx hy halign hcut hheight
  have hle : (Module.finrank F₂ (FiniteResidualRank.valueKernel (NormalizedWindowSets.union a b x y L)) : ℝ) ≤
      Module.finrank F₂ (largeKernel (NormalizedWindowSets.union a b x y L) (6 * Q * (L + 1))) := by
    exact_mod_cast Submodule.finrank_mono (fullKernel_le_large (NormalizedWindowSets.union a b x y L) (6 * Q * (L + 1)))
  exact hle.trans hlarge

theorem pair_loss_fixed_height (Q : ℕ) (hQ : 1 ≤ Q) (δ : ℝ) (hδ : 0 < δ) :
    ∃ K : ℝ, 0 < K ∧ ∀ C : ℝ, ∃ M₀ : ℕ, ∀ M ≥ max M₀ 2, ∀ L a b x y : ℕ,
      |(L : ℝ) - Real.log M / Real.log 2| ≤ C →
      0 < a → a ≤ b → b ≤ Q → x ∈ starts M δ → y ∈ starts M δ → Geometric a b x y L →
      (PaperP1.NormalizedPairRankLoss.pairLoss x y L : ℝ) ≤
        (((PaperP1.NormalizedUnitCount.units a b x y L).card - 1 : ℕ) : ℝ) +
          K * ((L + 1 : ℕ) : ℝ) / Real.log ((L + 1 : ℕ) : ℝ) := by
  obtain ⟨K, hK, hcore⟩ := full_kernel_rate Q hQ δ hδ
  refine ⟨K, hK, fun C ↦ ?_⟩
  obtain ⟨M₀, h⟩ := hcore C
  refine ⟨M₀, ?_⟩
  intro M hM L a b x y hcrit ha hab hbQ hx hy halign
  have hx2 := starts_pos (by omega : 2 ≤ M) hδ hx
  have hy2 := starts_pos (by omega : 2 ≤ M) hδ hy
  have hres := h M hM L a b x y hcrit ha hab hbQ hx hy halign
  have hfinite : (PaperP1.NormalizedPairRankLoss.pairLoss x y L : ℝ) ≤
      (((PaperP1.NormalizedUnitCount.units a b x y L).card - 1 : ℕ) : ℝ) +
        Module.finrank F₂ (FiniteResidualRank.valueKernel (NormalizedWindowSets.union a b x y L)) := by
    exact_mod_cast PaperP1.NormalizedPairRankLoss.loss_le_units_add_residual_all ha (ha.trans_le hab) hx2 hy2
  linarith

end PaperP1.MacroscopicFixedHeightResidual
