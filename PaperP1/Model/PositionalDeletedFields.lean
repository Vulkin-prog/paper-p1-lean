module

public import PaperP1.Model.PositionalStoppedLaw
public import PaperP1.Probability.PositionalDeletionKernels
public import PaperP1.Probability.PositionalGrid

/-! # The original deleted and isolated fields, with their actual probability laws -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositionalDeletedFields

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.PositionalFiniteLaw
  PaperP1.FiniteConvolutionAlgebra PaperP1.CompletedPositionalLaw
  PaperP1.PositionalTotalMass PaperP1.PositivePositionalConvolution

def original (G : Finset ℕ) (L : ℕ) : Space ℕ := ofFinite (PositionalStoppedLaw.actualLaw G L)

theorem original_isProbability (G : Finset ℕ) (L : ℕ) : IsProbability (original G L) := by
  constructor
  · intro v
    simpa only [original, coeff_ofFinite] using PositionalStoppedLaw.actualLaw_nonneg G L v
  · rw [original, totalMass_ofFinite, PositionalStoppedLaw.actualLaw_mass]

def onceLaw (E : Finset (Finset ℕ)) (G : Finset ℕ) (L : ℕ) : Space ℕ :=
  PositionalDeletionKernels.once E (original G L)

def isolatedLaw (E : Finset (Finset ℕ)) (G : Finset ℕ) (L : ℕ) : Space ℕ :=
  PositionalDeletionKernels.isolated E (original G L)

theorem onceLaw_isProbability (E : Finset (Finset ℕ)) (G : Finset ℕ) (L : ℕ) :
    IsProbability (onceLaw E G L) :=
  PositionalDeletionKernels.once_isProbability E _ (original_isProbability G L)

theorem isolatedLaw_isProbability (E : Finset (Finset ℕ)) (G : Finset ℕ) (L : ℕ) :
    IsProbability (isolatedLaw E G L) :=
  PositionalDeletionKernels.isolated_isProbability E _ (original_isProbability G L)

theorem action_finite_law {Ω ι κ : Type*} [Fintype Ω]
    (K : Configuration ι → Space κ) (hK : ∀ v, IsProbability (K v))
    (G : Finset ι) (w : Ω → ℝ) (J : ι → Ω → Bool) :
    PositionalMarkovKernel.action K hK (ofFinite (PositionalFiniteLaw.law G w J)) =
      ∑ ω, w ω • K (configuration G J ω) := by
  classical
  rw [PositionalFiniteLaw.law, map_sum, map_sum]
  apply sum_congr rfl
  intro ω _
  have he : ofFinite (scalar (w ω) * atom (configuration G J ω)) =
      w ω • ofFinite (atom (configuration G J ω)) := by
    rw [map_mul]
    change algebraMap ℝ (Space ι) (w ω) * _ = _
    rw [Algebra.smul_def]
  rw [he, map_smul, PositionalMarkovKernel.action_atom]

theorem onceLaw_finite_mixture (E : Finset (Finset ℕ)) (G : Finset ℕ) (L : ℕ) :
    onceLaw E G L = ∑ ω,
      (cylinderProbability (G.sup fun x ↦ x + L)).weight ω •
        PositionalDeletionKernels.onceKernel E (configuration G (fun x ↦ startIndicator x L) ω) :=
  action_finite_law _ _ G _ _

theorem isolatedLaw_finite_mixture (E : Finset (Finset ℕ)) (G : Finset ℕ) (L : ℕ) :
    isolatedLaw E G L = ∑ ω,
      (cylinderProbability (G.sup fun x ↦ x + L)).weight ω •
        ofFinite (atom (PositionalPairDeletion.isolate E
          (configuration G (fun x ↦ startIndicator x L) ω))) :=
  action_finite_law (fun v ↦ ofFinite (atom (PositionalPairDeletion.isolate E v)))
    (fun v ↦ PositionalDeterministicMap.atom_isProbability (PositionalPairDeletion.isolate E v)) G _ _

theorem configuration_binary {Ω ι : Type*} (G : Finset ι) (J : ι → Ω → Bool)
    (ω : Ω) (x : ι) : configuration G J ω x ≤ 1 := by
  classical
  by_cases hx : x ∈ G
  · rw [PositionalGrid.configuration_apply_mem G J ω ⟨x, hx⟩]
    cases J x ω <;> decide
  · rw [PositionalGroundSupport.onGround_configuration G J ω x hx]
    exact Nat.zero_le _

theorem one_all_original_count_cost (E : Finset (Finset ℕ)) (G : Finset ℕ) (L : ℕ)
    (hE : ∀ e ∈ E, e.card = 2) (ω : Model.InfiniteRademacher.InfiniteSample) :
    let v := configuration G (fun x ↦ infiniteStartIndicator x L) ω
    PositionalCountProjection.totalCount (PositionalPairDeletion.isolate E v) ≤
      PositionalPairDeletion.oneCount E v ∧
      PositionalPairDeletion.oneCount E v -
        PositionalCountProjection.totalCount (PositionalPairDeletion.isolate E v) ≤
          (PositionalPairDeletion.activeEdges E v).card *
            ((PositionalPairDeletion.activeEdges E v).card - 1) :=
  PositionalPairDeletion.one_all_count_cost E _
    (configuration_binary G (fun x ↦ infiniteStartIndicator x L) ω) hE

end PaperP1.PositionalDeletedFields
