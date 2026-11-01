module

public import PaperP1.Asymptotics.CriticalWindowGeometry
public import PaperP1.Arithmetic.IntervalResidualKernel
public import PaperP1.Arithmetic.NormalizedPairGeometry
public import PaperP1.Arithmetic.NormalizedPairRankLoss

/-! # The fixed-height O(B/log B) residual, including enlarged prime cutoffs -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FixedHeightResidual

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.NormalizedWindowSets
  PaperP1.NormalizedPairGeometry PaperP1.IntervalResidualKernel PaperP1.CriticalBandScale

theorem large_kernel_rate (Q : ℕ) (hQ : 1 ≤ Q) (D : ℝ) (hD : 0 ≤ D) :
    ∃ K : ℝ, 0 < K ∧ ∀ C : ℝ, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L a b x y H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      0 < a → a ≤ b → b ≤ Q → x ∈ dyadicBlock N → y ∈ dyadicBlock N →
      2 * b * L ≤ H → (H : ℝ) ≤ D * ((L + 1 : ℕ) : ℝ) →
      ∀ i j : Fin (L + 1), b * startCompleteVertexLabel x L i = a * startCompleteVertexLabel y L j →
      (Module.finrank F₂ (largeKernel (NormalizedWindowSets.union a b x y L) H) : ℝ) ≤
        K * ((L + 1 : ℕ) : ℝ) / Real.log ((L + 1 : ℕ) : ℝ) := by
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  obtain ⟨K, hK, Ncore, hcore⟩ := LocalDefectWindowScale.local_defect_count_le_window_scale_eventually
    (1 / 2) (3 * Q) lowerScale upperScale D (2 * Q)
    (by norm_num) (by positivity) lowerScale_pos upperScale_pos.le hD (by positivity)
  refine ⟨K, hK, fun C ↦ ?_⟩
  obtain ⟨Ngeom, hgeom⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨max Ncore Ngeom, ?_⟩
  intro N hN L a b x y H hcrit ha hab hbQ hx hy hRH hH i j hunit
  obtain ⟨hNtwo, _, hBtwo, hBN, hBlo, hBhi⟩ := hgeom N ((le_max_right _ _).trans hN) L hcrit
  have hxN := (mem_Ico.mp hx).1
  have hxHi := (mem_Ico.mp hx).2
  have hyN := (mem_Ico.mp hy).1
  have hxpos : 0 < x := by omega
  have hypos : 0 < y := by omega
  have hb : 0 < b := ha.trans_le hab
  let A : ℕ := b * startCompleteVertexLabel x L i
  let U : ℕ := A - b * L
  let R : ℕ := 2 * b * L
  have hanchor := anchor_geometry hBN hxN hb i
  have hA : b * L ≤ A := hanchor.1
  have hNU : N ≤ 2 * U := hanchor.2.2
  have hS : NormalizedWindowSets.union a b x y L ⊆ Icc U (U + R) := by
    intro n hn
    have hbounds := union_bounds hab hxpos hypos i j hunit n hn
    apply mem_Icc.mpr
    refine ⟨hbounds.1, ?_⟩
    have heq : A + b * L = U + R := by
      have hcancel := Nat.sub_add_cancel hA
      dsimp [U, R]
      nlinarith only [hcancel]
    rw [← heq]
    exact hbounds.2
  have hRscale : (R : ℝ) ≤ (2 * (Q : ℝ)) * ((L + 1 : ℕ) : ℝ) := by
    have hmul := Nat.mul_le_mul hbQ (show L ≤ L + 1 by omega)
    have hwidth : R ≤ 2 * Q * (L + 1) := by dsimp [R]; nlinarith only [hmul]
    exact_mod_cast hwidth
  have hUlo : (1 / 2 : ℝ) * N ≤ U := by
    have h : (N : ℝ) ≤ 2 * U := by exact_mod_cast hNU
    linarith only [h]
  have hUhi : (U : ℝ) ≤ (3 * (Q : ℝ)) * N := by
    have hlabel := mem_Ico.mp ((values_eq_interval hxpos).symm ▸ (mem_values.mpr ⟨i, rfl⟩))
    have hlabelHi : startCompleteVertexLabel x L i ≤ 3 * N := by omega
    have hmul := Nat.mul_le_mul hbQ hlabelHi
    have hsub : U ≤ A := Nat.sub_le _ _
    have hbound : U ≤ 3 * Q * N := by dsimp [A] at hsub; nlinarith only [hmul, hsub]
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
      ∀ i j : Fin (L + 1), b * startCompleteVertexLabel x L i = a * startCompleteVertexLabel y L j →
      (Module.finrank F₂ (FiniteResidualRank.valueKernel (NormalizedWindowSets.union a b x y L)) : ℝ) ≤
        K * ((L + 1 : ℕ) : ℝ) / Real.log ((L + 1 : ℕ) : ℝ) := by
  obtain ⟨K, hK, hcore⟩ := large_kernel_rate Q hQ (2 * (Q : ℝ)) (by positivity)
  refine ⟨K, hK, fun C ↦ ?_⟩
  obtain ⟨Ncore, hNcore⟩ := hcore C
  refine ⟨Ncore, ?_⟩
  intro N hN L a b x y hcrit ha hab hbQ hx hy i j hunit
  have hcut : 2 * b * L ≤ 2 * Q * (L + 1) := by nlinarith [Nat.mul_le_mul_right L hbQ]
  have hheight : ((2 * Q * (L + 1) : ℕ) : ℝ) ≤ (2 * (Q : ℝ)) * ((L + 1 : ℕ) : ℝ) := by push_cast; rfl
  have hlarge := hNcore N hN L a b x y (2 * Q * (L + 1)) hcrit ha hab hbQ hx hy hcut hheight i j hunit
  have hle : (Module.finrank F₂ (FiniteResidualRank.valueKernel (NormalizedWindowSets.union a b x y L)) : ℝ) ≤
      Module.finrank F₂ (largeKernel (NormalizedWindowSets.union a b x y L) (2 * Q * (L + 1))) := by
    exact_mod_cast Submodule.finrank_mono (fullKernel_le_large (NormalizedWindowSets.union a b x y L) (2 * Q * (L + 1)))
  exact hle.trans hlarge

end PaperP1.FixedHeightResidual
