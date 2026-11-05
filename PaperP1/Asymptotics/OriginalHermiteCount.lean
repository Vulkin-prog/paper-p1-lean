module

public import PaperP1.Asymptotics.PositionalFullApproximation
public import PaperP1.Asymptotics.CriticalPairNegligible
public import PaperP1.Model.PositionalCountMoments
public import PaperP1.Probability.PositionalScalarDistance
public import PaperP1.Probability.PositionalCountReference
public import PaperP1.Arithmetic.FiniteChannelHierarchy

/-! # The original scalar law and the exact good-pair Hermite parameters

The reference parameters are the source lambda=N*2^(-L), theta=2*beta.
Their admissibility is proved before constructing the probability law.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OriginalHermiteCount

open Finset MeasureTheory PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.CompletedPositionalLaw PaperP1.PositionalCountProjection
  PaperP1.CriticalPairNegligible

def HermiteNegligible (C : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
    |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
    let μ := FiniteChannelHierarchy.nominalMean N L
    let θ := 2 * RetainedReferenceTheorem.beta (8 * (L + 1) : ℕ) N L
    ∃ hθ : 0 ≤ θ, ∃ hθμ : θ ≤ μ,
      AtomicProbability.totalVariation (RetainedModifiedLaw.originalLaw (dyadicBlock N) L)
        (HermiteReference.law μ θ hθ hθμ) ≤ η * scale N L

def HermiteAtScale (C : ℝ) (a : ℕ → ℕ → ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
    |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
    let μ := FiniteChannelHierarchy.nominalMean N L
    let θ := 2 * RetainedReferenceTheorem.beta (8 * (L + 1) : ℕ) N L
    ∃ hθ : 0 ≤ θ, ∃ hθμ : θ ≤ μ,
      AtomicProbability.totalVariation (RetainedModifiedLaw.originalLaw (dyadicBlock N) L)
        (HermiteReference.law μ θ hθ hθμ) ≤ η * a N L

theorem at_scale_of_lower (C c : ℝ) (hc : 0 < c) (a : ℕ → ℕ → ℝ)
    (hscale : ∃ N₁ : ℕ, ∀ N ≥ N₁, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → c * scale N L ≤ a N L)
    (h : HermiteNegligible C) : HermiteAtScale C a := by
  obtain ⟨N₁, hscale⟩ := hscale
  intro η hη
  obtain ⟨N₂, _hN₂, hh⟩ := h (η * c) (mul_pos hη hc)
  refine ⟨10 + N₁ + N₂, by omega, ?_⟩
  intro N hN L hband
  obtain ⟨hθ, hθμ, hs⟩ := hh N (by omega) L hband
  refine ⟨hθ, hθμ, hs.trans ?_⟩
  have hb := mul_le_mul_of_nonneg_left (hscale N (by omega) L hband) hη.le
  nlinarith only [hb]

theorem uniform_bound (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
        let μ := FiniteChannelHierarchy.nominalMean N L
        let θ := 2 * RetainedReferenceTheorem.beta (8 * (L + 1) : ℕ) N L
        ∃ hθ : 0 ≤ θ, ∃ hθμ : θ ≤ μ,
          AtomicProbability.totalVariation (RetainedModifiedLaw.originalLaw (dyadicBlock N) L)
            (HermiteReference.law μ θ hθ hθμ) ≤ (N : ℝ) ^ (-4 / 5 + ε) := by
  obtain ⟨NA, _hNA, ha⟩ := PositionalFullApproximation.uniform_norm_bound C ε hε
  obtain ⟨NP, _hNP, hp0⟩ := WeakPairIncidence.full_single_rates_positive C
  refine ⟨10 + NP + NA, by omega, ?_⟩
  intro N hN L hband
  dsimp only
  let G := dyadicBlock N
  let E := GoodEdgeCompression.goodEdges (8 * (L + 1) : ℕ) N L
  let μ := FiniteChannelHierarchy.nominalMean N L
  let θ := 2 * RetainedReferenceTheorem.beta (8 * (L + 1) : ℕ) N L
  let A := ofFinite (PositionalStoppedLaw.actualLaw G L)
  let T := PositionalCompoundPoisson.target G E (fun _ ↦ (2 ^ L : ℝ)⁻¹) (infiniteJointMoment L)
  have hE : ∀ e ∈ E, e ⊆ G ∧ e.card = 2 := fun e he ↦
    ⟨(RetainedGoodEdges.good_pair_regular (by omega) e he).trans
      (RegularStarts.regularStarts_subset N L), RetainedGoodEdges.good_pair_card _ N L e he⟩
  have hθ : 0 ≤ θ := mul_nonneg (by norm_num) (sum_nonneg (fun e _he ↦ infiniteJointMoment_nonneg L e))
  have hθμ : θ ≤ μ := by
    have hh := PositionalCountReference.parameter_admissible G E (fun _ ↦ (2 ^ L : ℝ)⁻¹)
      (infiniteJointMoment L) hE (fun x _hx ↦ (hp0 N (by omega) L hband (8 * (L + 1) : ℕ) x).le)
    simpa only [sum_const, nsmul_eq_mul, G, E, μ, θ, FiniteChannelHierarchy.nominalMean,
      RetainedReferenceTheorem.beta, dyadicBlock_card] using hh
  refine ⟨hθ, hθμ, ?_⟩
  let Q := HermiteReference.law μ θ hθ hθμ
  have hproj : projection T = HermiteReference.reference μ θ := by
    have hh := PositionalCountReference.projection_target G E (fun _ ↦ (2 ^ L : ℝ)⁻¹)
      (infiniteJointMoment L) hE
    simpa only [sum_const, nsmul_eq_mul, G, E, T, μ, θ, FiniteChannelHierarchy.nominalMean,
      RetainedReferenceTheorem.beta, dyadicBlock_card] using hh
  have hP (k : ℕ) : AtomicProbability.realMass (RetainedModifiedLaw.originalLaw G L) k =
      CompletedLaw.coeff k (projection A) := (PositionalCountMoments.projection_actual_coeff G L k).symm
  have hQ (k : ℕ) : AtomicProbability.realMass Q k = CompletedLaw.coeff k (projection T) := by
    rw [hproj]
    exact (HermiteReference.coeff_law μ θ hθ hθμ k).symm
  have hs := PositionalScalarDistance.bound A T (RetainedModifiedLaw.originalLaw G L) Q hP hQ
  have hnorm := ha N (by omega) L hband
  have h0 := norm_nonneg (A - T)
  linarith only [hs, hnorm, h0]

theorem uniform_relative (C : ℝ) :
    HermiteNegligible C := by
  obtain ⟨NA, _hNA, ha⟩ := uniform_bound C (1 / 30) (by norm_num)
  intro η hη
  obtain ⟨NS, _hNS, hs⟩ := power_small C (23 / 30) η (by norm_num) hη
  refine ⟨10 + NA + NS, by omega, ?_⟩
  intro N hN L hband
  obtain ⟨hθ, hθμ, h⟩ := ha N (by omega) L hband
  refine ⟨hθ, hθμ, h.trans ?_⟩
  simpa only [show (-4 / 5 + 1 / 30 : ℝ) = -(23 / 30) by norm_num] using hs N (by omega) L hband

end PaperP1.OriginalHermiteCount
