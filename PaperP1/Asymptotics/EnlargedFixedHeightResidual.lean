module

public import PaperP1.Asymptotics.CriticalWindowGeometry
public import PaperP1.Asymptotics.CriticalPolynomialScale
public import PaperP1.Arithmetic.IntervalResidualKernel
public import PaperP1.Arithmetic.EnlargedPairGeometry
public import PaperP1.Arithmetic.NormalizedPairRankLoss

/-! # Fixed-height enlarged-alignment residuals without an exact-unit hypothesis -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.EnlargedFixedHeightResidual

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.NormalizedWindowSets
  PaperP1.EnlargedPairGeometry PaperP1.IntervalResidualKernel PaperP1.CriticalBandScale

theorem large_kernel_rate (Q : ℕ) (hQ : 1 ≤ Q) (D : ℝ) (hD : 0 ≤ D) :
    ∃ K : ℝ, 0 < K ∧ ∀ C : ℝ, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L a b x y H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      0 < a → a ≤ b → b ≤ Q → x ∈ dyadicBlock N → y ∈ dyadicBlock N →
      Geometric a b x y L → 2 * radius b L ≤ H → (H : ℝ) ≤ D * ((L + 1 : ℕ) : ℝ) →
      (Module.finrank F₂ (largeKernel (NormalizedWindowSets.union a b x y L) H) : ℝ) ≤
        K * ((L + 1 : ℕ) : ℝ) / Real.log ((L + 1 : ℕ) : ℝ) := by
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  obtain ⟨K, hK, Ncore, hcore⟩ := LocalDefectWindowScale.local_defect_count_le_window_scale_eventually
    (1 / 2) (2 * Q) lowerScale upperScale D (6 * Q)
    (by norm_num) (by positivity) lowerScale_pos upperScale_pos.le hD (by positivity)
  refine ⟨K, hK, fun C ↦ ?_⟩
  obtain ⟨Ngeom, hgeom⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨Npoly, hpoly⟩ := CriticalPolynomialScale.polynomial_lt_scale C
    ((24 * Q + 8 : ℕ) : ℝ) (by positivity) 1
  refine ⟨max Ncore (max Ngeom Npoly), ?_⟩
  intro N hN L a b x y H hcrit ha hab hbQ hx hy halign hRH hH
  obtain ⟨hNtwo, _, hBtwo, _, hBlo, hBhi⟩ :=
    hgeom N ((le_max_left Ngeom Npoly).trans ((le_max_right _ _).trans hN)) L hcrit
  have hpolyNat : (24 * Q + 8) * (L + 1) < N := by
    have h := hpoly N ((le_max_right Ngeom Npoly).trans ((le_max_right _ _).trans hN)) L hcrit
    norm_num only [pow_one] at h
    exact_mod_cast h
  have hrad : radius b L ≤ 3 * (Q * (L + 1)) := by
    unfold radius
    exact Nat.mul_le_mul_left 3 (Nat.mul_le_mul_right (L + 1) hbQ)
  have hlarge : 8 * radius b L + 8 ≤ N := by
    have h := Nat.mul_le_mul_left 8 hrad
    nlinarith only [hpolyNat, hBtwo, h]
  have hxN := (mem_Ico.mp hx).1
  have hxHi := (mem_Ico.mp hx).2
  have hyN := (mem_Ico.mp hy).1
  have hxpos : 0 < x := by omega
  have hypos : 0 < y := by omega
  have hb : 0 < b := ha.trans_le hab
  have hbase := base_geometry hb hxN hlarge
  let U : ℕ := base b x L
  let R : ℕ := 2 * radius b L
  have hS : NormalizedWindowSets.union a b x y L ⊆ Icc U (U + R) := by
    intro n hn
    exact mem_Icc.mpr (interval_bounds hab hxpos hypos halign hbase.1 n hn)
  have hRscale : (R : ℝ) ≤ (6 * (Q : ℝ)) * ((L + 1 : ℕ) : ℝ) := by
    have hwidth : R ≤ 6 * Q * (L + 1) := by dsimp [R]; nlinarith only [hrad]
    exact_mod_cast hwidth
  have hUlo : (1 / 2 : ℝ) * N ≤ U := by
    have h : (N : ℝ) ≤ 2 * U := by exact_mod_cast hbase.2.1
    linarith only [h]
  have hUhi : (U : ℝ) ≤ (2 * (Q : ℝ)) * N := by
    have hmul := Nat.mul_le_mul hbQ hxHi.le
    have hsub : U ≤ b * x := Nat.sub_le _ _
    have hbound : U ≤ 2 * Q * N := by nlinarith only [hmul, hsub]
    exact_mod_cast hbound
  have hdef := hcore N ((le_max_left _ _).trans hN) ((L + 1 : ℕ) : ℝ) H U R
    hBlo hBhi hH hRscale hUlo hUhi
  have hrank : (Module.finrank F₂ (largeKernel (NormalizedWindowSets.union a b x y L) H) : ℝ) ≤
      (LocalDefectBound.defectsInInterval H U R).card := by
    exact_mod_cast rank_le_interval_defects hRH hS
  exact hrank.trans hdef

theorem full_kernel_rate (Q : ℕ) (hQ : 1 ≤ Q) :
    ∃ K : ℝ, 0 < K ∧ ∀ C : ℝ, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L a b x y : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      0 < a → a ≤ b → b ≤ Q → x ∈ dyadicBlock N → y ∈ dyadicBlock N →
      Geometric a b x y L →
      (Module.finrank F₂ (FiniteResidualRank.valueKernel (NormalizedWindowSets.union a b x y L)) : ℝ) ≤
        K * ((L + 1 : ℕ) : ℝ) / Real.log ((L + 1 : ℕ) : ℝ) := by
  obtain ⟨K, hK, hcore⟩ := large_kernel_rate Q hQ (6 * (Q : ℝ)) (by positivity)
  refine ⟨K, hK, fun C ↦ ?_⟩
  obtain ⟨Ncore, hNcore⟩ := hcore C
  refine ⟨Ncore, ?_⟩
  intro N hN L a b x y hcrit ha hab hbQ hx hy halign
  have hrad : radius b L ≤ 3 * (Q * (L + 1)) := by
    unfold radius
    exact Nat.mul_le_mul_left 3 (Nat.mul_le_mul_right (L + 1) hbQ)
  have hcut : 2 * radius b L ≤ 6 * Q * (L + 1) := by nlinarith only [hrad]
  have hheight : ((6 * Q * (L + 1) : ℕ) : ℝ) ≤ (6 * (Q : ℝ)) * ((L + 1 : ℕ) : ℝ) := by push_cast; rfl
  have hlarge := hNcore N hN L a b x y (6 * Q * (L + 1)) hcrit ha hab hbQ hx hy halign hcut hheight
  have hle : (Module.finrank F₂ (FiniteResidualRank.valueKernel (NormalizedWindowSets.union a b x y L)) : ℝ) ≤
      Module.finrank F₂ (largeKernel (NormalizedWindowSets.union a b x y L) (6 * Q * (L + 1))) := by
    exact_mod_cast Submodule.finrank_mono (fullKernel_le_large (NormalizedWindowSets.union a b x y L) (6 * Q * (L + 1)))
  exact hle.trans hlarge

end PaperP1.EnlargedFixedHeightResidual
