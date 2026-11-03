module

public import PaperP1.Asymptotics.TwoTargetPrimitiveExtensions

/-! # Summing the actual one-source dense extension estimate bounds all dense primitive triples -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DensePrimitiveTripleMassUnderInputs

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.PrimitiveWindowMass

structure Parameters where
  leftSourceCutoff : ℕ
  leftSourceDegree : ℕ
  leftSourceRadicals : ℕ
  leftOrdinaryCutoff : ℕ
  leftOrdinaryRadicals : ℕ
  rightSourceCutoff : ℕ
  rightSourceDegree : ℕ
  rightSourceRadicals : ℕ
  rightOrdinaryCutoff : ℕ
  rightOrdinaryRadicals : ℕ

structure Hypotheses (p : Parameters) : Prop where
  leftSource : UniformSourceSurfaceCover.UniformCover p.leftSourceRadicals (p.leftSourceCutoff - 1) p.leftSourceDegree
  leftOrdinary : UniformOrdinarySurfaceCover.UniformCover p.leftOrdinaryRadicals (p.leftOrdinaryCutoff - 1)
  leftSourceCurves : ∀ M, UniformNormalizedCurvePointCount.UniformBound
    ((p.leftSourceDegree + 2).choose 2 + p.leftSourceRadicals) M
  leftOrdinaryCurves : ∀ M, UniformNormalizedCurvePointCount.UniformBound (p.leftOrdinaryRadicals + 3) M
  rightSource : UniformSourceSurfaceCover.UniformCover p.rightSourceRadicals (p.rightSourceCutoff - 1) p.rightSourceDegree
  rightOrdinary : UniformOrdinarySurfaceCover.UniformCover p.rightOrdinaryRadicals (p.rightOrdinaryCutoff - 1)
  rightSourceCurves : ∀ M, UniformNormalizedCurvePointCount.UniformBound
    ((p.rightSourceDegree + 2).choose 2 + p.rightSourceRadicals) M
  rightOrdinaryCurves : ∀ M, UniformNormalizedCurvePointCount.UniformBound (p.rightOrdinaryRadicals + 3) M

theorem uniform_bound (C ε : ℝ) (hε : 0 < ε) :
    ∃ p : Parameters, Hypotheses p → ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ F : Finset (Finset ℕ),
      (∀ I ∈ F, I ⊆ dyadicBlock N ∧ I.card = 3 ∧ ConnectedWindowFamilies.Primitive L I ∧
        (1 / 4 : ℝ) * L ≤ (runRelativeNullity L I : ℝ)) →
      mass F L ≤ (N : ℝ) ^ (-1 + ε) := by
  classical
  obtain ⟨t₁, D₁, k₁, t₂, k₂, t₃, D₂, k₃, t₄, k₄,
    _ht₁, _hD₁, _ht₂, _hk₂, _ht₃, _hD₂, _ht₄, _hk₄, hp⟩ :=
    TwoTargetPrimitiveExtensions.uniform_extensions 1 (by decide) C (1 / 4) (ε / 2) (by norm_num) (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption (2 * (2 : ℝ) ^ C) (-1 + ε / 2) (ε / 2) (by positivity)
  refine ⟨⟨t₁, D₁, k₁, t₂, k₂, t₃, D₂, k₃, t₄, k₄⟩, ?_⟩
  intro hgeo
  obtain ⟨NP, _hNP, hh⟩ := hp hgeo.leftSource hgeo.leftOrdinary hgeo.leftSourceCurves hgeo.leftOrdinaryCurves
    hgeo.rightSource hgeo.rightOrdinary hgeo.rightSourceCurves hgeo.rightOrdinaryCurves
  refine ⟨3 + NP + NF, by omega, ?_⟩
  intro N hN L hband F hF
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hcover := TwoTargetFamilyCover.weighted_cover (dyadicBlock N) ((dyadicBlock N).powersetCard 1) F
    (weight L) (weight_nonneg L) (fun I hI ↦ (hF I hI).1) (by
      intro E hE I hI
      have he := (mem_powersetCard.mp hE).2
      have hi := (hF I hI).2.1
      omega) (by
      intro I hI
      have hne : I.Nonempty := card_pos.mp (by have h := (hF I hI).2.1; omega)
      obtain ⟨x, hx⟩ := hne
      exact ⟨{x}, mem_powersetCard.mpr ⟨singleton_subset_iff.mpr ((hF I hI).1 hx), card_singleton _⟩,
        singleton_subset_iff.mpr hx⟩)
  calc
    _ ≤ ∑ E ∈ (dyadicBlock N).powersetCard 1,
        ∑ p ∈ TwoTargetFamilyCover.pairs (dyadicBlock N) E F, weight L (TwoTargetFamilyCover.family E p) := hcover
    _ ≤ ∑ _E ∈ (dyadicBlock N).powersetCard 1,
        (2 * (2 : ℝ) ^ C / N) ^ 1 * (N : ℝ) ^ (-1 + ε / 2) := by
      apply sum_le_sum
      intro E hE
      obtain ⟨hEG, hcard⟩ := mem_powersetCard.mp hE
      exact hh N (by omega) L hband E hcard hEG F (fun I hI ↦ ⟨(hF I hI).2.2.1, (hF I hI).2.2.2⟩)
    _ = (2 * (2 : ℝ) ^ C) * (N : ℝ) ^ (-1 + ε / 2) := by
      rw [sum_const, nsmul_eq_mul, card_powersetCard, Nat.choose_one_right,
        RegularSetFinite.card_dyadicBlock, pow_one]
      field_simp
    _ ≤ (N : ℝ) ^ ((-1 + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.DensePrimitiveTripleMassUnderInputs
