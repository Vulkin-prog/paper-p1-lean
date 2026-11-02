module

public import PaperP1.Model.InfiniteReplicaFormula
public import PaperP1.Model.ReplicaPositiveSum

/-! # Positive sums of actual conditional probabilities and their finite moment transport -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.InfiniteReplicaPositiveSum

open MeasureTheory Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteRademacher
  PaperP1.InfiniteReplicaFormula PaperP1.UniformFubini
  PaperP1.Probability.InfiniteCylinderTransfer PaperP1.Probability.CylinderExpectations

local instance infiniteReplicaPositiveSumMeasurableF2 : MeasurableSpace F₂ := ⊤

variable {κ : Type*} [Fintype κ] {r : ℕ}

def randomSum (Y L : ℕ) (color : Fin r → κ) (c : ℕ → Fin L → F₂)
    (A : Finset (Fin r → ℕ)) (w : (Fin r → ℕ) → ℝ) (ω : InfiniteSample) : ℝ :=
  ∑ x ∈ A, w x * ∏ k, conditionalBlock Y L x color (fun i ↦ c (x i)) k ω

theorem ae_eq_finite {M Y L : ℕ} (hYM : Y ≤ M) (color : Fin r → κ)
    (c : ℕ → Fin L → F₂) (A : Finset (Fin r → ℕ)) (w : (Fin r → ℕ) → ℝ)
    (hcut : ∀ x ∈ A, ∀ i, x i + L ≤ M) :
    randomSum Y L color c A w =ᵐ[infiniteRademacherMeasure]
      (fun ω ↦ ReplicaPositiveSum.randomSum Y L color c A w (restrictToFinite M ω)) := by
  classical
  have h (x : A) (k : κ) :
      (fun ω : InfiniteSample ↦ ColoredReplicaMass.blockProbability Y L x.val color
        (fun i ↦ c (x.val i)) k (restrictToFinite M ω)) =ᵐ[infiniteRademacherMeasure]
        conditionalBlock Y L x.val color (fun i ↦ c (x.val i)) k := by
    have h := SmallPrimeConditioning.block_condExp Y L x.val color (fun i ↦ c (x.val i)) k
      (hcut x.val x.property)
    rw [SmallPrimeFiltration.filtration_eq hYM] at h
    exact h
  have hall : ∀ᵐ ω ∂infiniteRademacherMeasure, ∀ x : A, ∀ k : κ,
      ColoredReplicaMass.blockProbability Y L x.val color (fun i ↦ c (x.val i)) k (restrictToFinite M ω) =
        conditionalBlock Y L x.val color (fun i ↦ c (x.val i)) k ω :=
    ae_all_iff.mpr (fun x ↦ ae_all_iff.mpr (h x))
  filter_upwards [hall] with ω hω
  unfold randomSum ReplicaPositiveSum.randomSum
  apply sum_congr rfl
  intro x hx
  congr 1
  exact prod_congr rfl (fun k _ ↦ (hω ⟨x, hx⟩ k).symm)

theorem moment_transport {M Y L : ℕ} (hYM : Y ≤ M) (color : Fin r → κ)
    (c : ℕ → Fin L → F₂) (A : Finset (Fin r → ℕ)) (w : (Fin r → ℕ) → ℝ)
    (hcut : ∀ x ∈ A, ∀ i, x i + L ≤ M) (n : ℕ) :
    (∫ ω, (randomSum Y L color c A w ω) ^ n ∂infiniteRademacherMeasure) =
      average (fun σ : SampleSpace M ↦ (ReplicaPositiveSum.randomSum Y L color c A w σ) ^ n) := by
  calc
    _ = ∫ ω, (ReplicaPositiveSum.randomSum Y L color c A w (restrictToFinite M ω)) ^ n
        ∂infiniteRademacherMeasure := by
      apply integral_congr_ae
      filter_upwards [ae_eq_finite hYM color c A w hcut] with ω hω
      rw [hω]
    _ = _ := infiniteCylinder_integral M
      (fun σ : SampleSpace M ↦ (ReplicaPositiveSum.randomSum Y L color c A w σ) ^ n)

theorem first_moment_transport {M Y L : ℕ} (hYM : Y ≤ M) (color : Fin r → κ)
    (c : ℕ → Fin L → F₂) (A : Finset (Fin r → ℕ)) (w : (Fin r → ℕ) → ℝ)
    (hcut : ∀ x ∈ A, ∀ i, x i + L ≤ M) :
    (∫ ω, randomSum Y L color c A w ω ∂infiniteRademacherMeasure) =
      average (ReplicaPositiveSum.randomSum Y L color c A w : SampleSpace M → ℝ) := by
  simpa only [pow_one] using moment_transport hYM color c A w hcut 1

end PaperP1.InfiniteReplicaPositiveSum
