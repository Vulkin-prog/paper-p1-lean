module

public import PaperP1.Asymptotics.DensePrimitiveTripleMassUnderInputs

/-! # Actual dense primitive mass over a restricted population of source sets -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RestrictedDensePrimitiveMassUnderInputs

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.PrimitiveWindowMass PaperP1.DensePrimitiveTripleMassUnderInputs

theorem uniform_bound (s : ℕ) (hs : 1 ≤ s) (C η σ ε : ℝ)
    (hη : 0 < η) (hε : 0 < ε) :
    ∃ p : Parameters, Hypotheses p → ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ S F : Finset (Finset ℕ),
      (∀ E ∈ S, E ⊆ dyadicBlock N ∧ E.card = s) →
      (S.card : ℝ) ≤ (N : ℝ) ^ σ →
      (∀ I ∈ F, I ⊆ dyadicBlock N ∧ I.card = s + 2 ∧
        ConnectedWindowFamilies.Primitive L I ∧ η * L ≤ (runRelativeNullity L I : ℝ)) →
      (∀ I ∈ F, ∃ E ∈ S, E ⊆ I) →
      mass F L ≤ (N : ℝ) ^ (-1 - s + σ + ε) := by
  classical
  obtain ⟨t₁, D₁, k₁, t₂, k₂, t₃, D₂, k₃, t₄, k₄,
    _ht₁, _hD₁, _ht₂, _hk₂, _ht₃, _hD₂, _ht₄, _hk₄, hp⟩ :=
    TwoTargetPrimitiveExtensions.uniform_extensions s hs C η (ε / 2) hη (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption ((2 * (2 : ℝ) ^ C) ^ s)
    (-1 - s + σ + ε / 2) (ε / 2) (by positivity)
  refine ⟨⟨t₁, D₁, k₁, t₂, k₂, t₃, D₂, k₃, t₄, k₄⟩, ?_⟩
  intro hgeo
  obtain ⟨NP, _hNP, hh⟩ := hp hgeo.leftSource hgeo.leftOrdinary hgeo.leftSourceCurves hgeo.leftOrdinaryCurves
    hgeo.rightSource hgeo.rightOrdinary hgeo.rightSourceCurves hgeo.rightOrdinaryCurves
  refine ⟨3 + NP + NF, by omega, ?_⟩
  intro N hN L hband S F hS hScard hF hcover
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hfinite := TwoTargetFamilyCover.weighted_cover (dyadicBlock N) S F
    (weight L) (weight_nonneg L) (fun I hI ↦ (hF I hI).1)
    (fun E hE I hI ↦ by rw [(hF I hI).2.1, (hS E hE).2]) hcover
  have hpow : (N : ℝ) ^ s = (N : ℝ) ^ (s : ℝ) := (Real.rpow_natCast _ _).symm
  calc
    _ ≤ ∑ E ∈ S, ∑ p ∈ TwoTargetFamilyCover.pairs (dyadicBlock N) E F,
        weight L (TwoTargetFamilyCover.family E p) := hfinite
    _ ≤ ∑ _E ∈ S, (2 * (2 : ℝ) ^ C / N) ^ s * (N : ℝ) ^ (-1 + ε / 2) := by
      apply sum_le_sum
      intro E hE
      exact hh N (by omega) L hband E (hS E hE).2 (hS E hE).1 F
        (fun I hI ↦ ⟨(hF I hI).2.2.1, (hF I hI).2.2.2⟩)
    _ = (S.card : ℝ) * ((2 * (2 : ℝ) ^ C / N) ^ s * (N : ℝ) ^ (-1 + ε / 2)) := by
      rw [sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ) ^ σ * ((2 * (2 : ℝ) ^ C / N) ^ s * (N : ℝ) ^ (-1 + ε / 2)) :=
      mul_le_mul_of_nonneg_right hScard (by positivity)
    _ = (2 * (2 : ℝ) ^ C) ^ s * (N : ℝ) ^ (-1 - s + σ + ε / 2) := by
      rw [div_pow, hpow]
      have hpower : (N : ℝ) ^ σ * ((N : ℝ) ^ (-1 + ε / 2) / (N : ℝ) ^ (s : ℝ)) =
          (N : ℝ) ^ (-1 - s + σ + ε / 2) := by
        rw [← Real.rpow_sub hn, ← Real.rpow_add hn]
        congr 1
        ring
      calc
        _ = (2 * (2 : ℝ) ^ C) ^ s * ((N : ℝ) ^ σ *
          ((N : ℝ) ^ (-1 + ε / 2) / (N : ℝ) ^ (s : ℝ))) := by ring
        _ = _ := by rw [hpower]
    _ ≤ (N : ℝ) ^ ((-1 - s + σ + ε / 2) + ε / 2) := hf N (by omega)
    _ = _ := by congr 1; ring

end PaperP1.RestrictedDensePrimitiveMassUnderInputs
