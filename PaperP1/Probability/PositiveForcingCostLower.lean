module

public import PaperP1.Probability.ForcingCoordinateCost

/-! # Positive coordinate costs retain every selected clean directed pair

The source is distinguished. Source/target symmetries or signed cancellation
are not used. The diagonal is kept separately from the offsite lower bound.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositiveForcingCostLower

open Finset PaperP1.Algebra PaperP1.Probability PaperP1.ForcingCoordinateCost

variable {Ω ι : Type*} [Fintype Ω] [DecidableEq ι]

def directed (G : Finset ι) : Finset (ι × ι) :=
  (G ×ˢ G).filter fun p ↦ p.2 ≠ p.1

def weight (P : FiniteProbability Ω) (J : ι → Ω → Bool) (F : ι → Ω → Ω) (p : ι × ι) : ℝ :=
  exactMarginal P J p.1 * finiteExpectation P.weight
    (fun ω ↦ |(indicatorValue (J p.2 ω) : ℝ) - indicatorValue (J p.2 (F p.1 ω))|)

def offsite (G : Finset ι) (P : FiniteProbability Ω) (J : ι → Ω → Bool) (F : ι → Ω → Ω) : ℝ :=
  ∑ a ∈ G, exactMarginal P J a * offsiteCost G P J F a

omit [DecidableEq ι] in
theorem weight_nonneg (P : FiniteProbability Ω) (J : ι → Ω → Bool)
    (F : ι → Ω → Ω) (p : ι × ι) : 0 ≤ weight P J F p :=
  mul_nonneg (exactMarginal_nonneg P J p.1) (finiteExpectation_nonneg P (fun _ ↦ abs_nonneg _))

theorem offsite_eq_pairs (G : Finset ι) (P : FiniteProbability Ω)
    (J : ι → Ω → Bool) (F : ι → Ω → Ω) :
    offsite G P J F = ∑ p ∈ directed G, weight P J F p := by
  unfold offsite offsiteCost directed
  simp only [finiteExpectation_sum, mul_sum, sum_filter, sum_product]
  apply sum_congr rfl
  intro a _
  have he : G.erase a = G.filter (fun b ↦ b ≠ a) := by
    ext b
    simp only [mem_erase, mem_filter, and_comm]
  rw [he, sum_filter]
  rfl

theorem selected_pairs_lower (G : Finset ι) (P : FiniteProbability Ω)
    (J : ι → Ω → Bool) (F : ι → Ω → Ω) (E : Finset (ι × ι))
    (hE : E ⊆ directed G) (γ : ℝ) (hγ : ∀ p ∈ E, γ ≤ weight P J F p) :
    γ * E.card ≤ offsite G P J F := by
  rw [offsite_eq_pairs]
  calc
    _ = ∑ _p ∈ E, γ := by simp [mul_comm]
    _ ≤ ∑ p ∈ E, weight P J F p := sum_le_sum hγ
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hE (fun p _ _ ↦ weight_nonneg P J F p)

theorem offsite_le_full_cost (G : Finset ι) (P : FiniteProbability Ω)
    (J : ι → Ω → Bool) (F : ι → Ω → Ω)
    (hF : ∀ a ∈ G, ∀ ω, J a (F a ω) = true) :
    offsite G P J F ≤ cost G P J F := by
  rw [exact_diagonal_decomposition G P J F hF]
  exact le_add_of_nonneg_left (sum_nonneg fun _ _ ↦ sq_nonneg _)

theorem full_cost_selected_lower (G : Finset ι) (P : FiniteProbability Ω)
    (J : ι → Ω → Bool) (F : ι → Ω → Ω)
    (hF : ∀ a ∈ G, ∀ ω, J a (F a ω) = true) (E : Finset (ι × ι))
    (hE : E ⊆ directed G) (γ : ℝ) (hγ : ∀ p ∈ E, γ ≤ weight P J F p) :
    γ * E.card ≤ cost G P J F :=
  (selected_pairs_lower G P J F E hE γ hγ).trans (offsite_le_full_cost G P J F hF)

end PaperP1.PositiveForcingCostLower
