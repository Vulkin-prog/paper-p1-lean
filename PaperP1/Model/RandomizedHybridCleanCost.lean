module

public import PaperP1.Model.RandomizedHybridField
public import PaperP1.Model.RandomizedCleanPivotWordCost

/-! # The actual hybrid field retains every clean randomized half-rate pair

All weights are the actual original-field marginals on the prime/auxiliary
product sample. The diagonal stays separate from the offsite lower bound.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RandomizedHybridCleanCost

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.PrivateValueSystem
  PaperP1.Probability PaperP1.Algebra PaperP1.IndependentFiniteProbability
  PaperP1.RandomizedHybridField PaperP1.PositiveForcingCostLower

variable {M Y K : ℕ} {G Good : Finset ℕ} {anchor : G → Fin (K + 1)}
variable {Ξ : Type*} [Fintype Ξ]

theorem expected_change_eq (D : Data M Y K G Good anchor) (P : FiniteProbability Ξ)
    (b : Fin (K + 1) → F₂) (g : G → (Fin (K + 1) → F₂) → Ξ → F₂)
    (j k : G) (hj : j.val ∈ Good) :
    finiteExpectation (law (M := M) P).weight (fun p ↦
      |(indicatorValue (indicator b k p) : ℝ) - indicatorValue (indicator b k (force D b g j p))|) =
      PaperP1.RandomizedCleanPivotWordCost.actualUnsignedCost
        (fun i : Fin (K + 1) ↦ j.val + i.val) (fullPivots D j hj) b (g j) P k.val b := by
  unfold PaperP1.RandomizedCleanPivotWordCost.actualUnsignedCost
  change finiteExpectation (product (cylinderProbability M) P).weight
    (fun p ↦ |(indicatorValue (PaperP1.AnchoredPrivateField.indicator b k p.1) : ℝ) -
      indicatorValue (PaperP1.AnchoredPrivateField.indicator b k (primeForce D b g j p.1 p.2))|) = _
  apply congrArg (finiteExpectation (product (cylinderProbability M) P).weight)
  funext p
  rw [primeForce_good D b g j hj,
    PaperP1.AnchoredPrivateField.indicator_value b k p.1,
    PaperP1.AnchoredPrivateField.indicator_value b k
      (PaperP1.RandomizedPrivatePalmForcing.force (fun i : Fin (K + 1) ↦ j.val + i.val)
        (fullPivots D j hj) b (g j) p.1 p.2)]

theorem clean_weight_lower (D : Data M Y K G Good anchor) (P : FiniteProbability Ξ) (hK : 1 ≤ K)
    (b : Fin (K + 1) → F₂) (g : G → (Fin (K + 1) → F₂) → Ξ → F₂)
    (j k : G) (hj : j.val ∈ Good) (selected : Fin (K + 1)) {A N : ℕ}
    (hclean : k.val ∈ PaperP1.CleanPivotTargets.targets A N (fullPivots D j hj selected).val.val
      (K + 1) (PaperP1.PrivatePivotTargetFlip.otherPrimes (fullPivots D j hj) selected))
    (hjoint : Function.Surjective (PaperP1.RawWordObservation.joint M
      (fun i : Fin (K + 1) ↦ j.val + i.val) (fun i : Fin (K + 1) ↦ k.val + i.val)))
    (hquarter : (1 / 4 : ℝ) ≤ PaperP1.RandomizedSourceFlip.probability P b (g j) selected) :
    (PaperP1.AnchoredPrivateField.rate K) ^ 2 / 2 ≤
      weight (law (M := M) P) (indicator b) (force D b g) (j, k) := by
  unfold weight
  rw [indicator_marginal D, expected_change_eq D P b g j k hj]
  have hw : K + 1 ≤ (fullPivots D j hj selected).val.val :=
    (D.anchored.window j).word_width.trans (D.good j hj selected).le
  have hc := PaperP1.RandomizedCleanPivotWordCost.actual_half_rate_lower hK
    (fun i : Fin (K + 1) ↦ j.val + i.val) (fullPivots D j hj) b (g j) P selected
    hw hclean hjoint b hquarter
  calc
    _ = PaperP1.AnchoredPrivateField.rate K * ((2 ^ K : ℝ)⁻¹ / 2) := by
      unfold PaperP1.AnchoredPrivateField.rate
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hc (PaperP1.AnchoredPrivateField.rate_pos K).le

theorem selected_pairs_offsite_lower (D : Data M Y K G Good anchor) (P : FiniteProbability Ξ) (hK : 1 ≤ K)
    (b : Fin (K + 1) → F₂) (g : G → (Fin (K + 1) → F₂) → Ξ → F₂)
    (E : Finset (G × G)) (hE : E ⊆ directed univ)
    (hactive : ∀ p ∈ E, p.1.val ∈ Good) {A N : ℕ}
    (hclean : ∀ p : G × G, ∀ hp : p ∈ E, ∃ selected : Fin (K + 1),
      p.2.val ∈ PaperP1.CleanPivotTargets.targets A N
        (fullPivots D p.1 (hactive p hp) selected).val.val (K + 1)
        (PaperP1.PrivatePivotTargetFlip.otherPrimes (fullPivots D p.1 (hactive p hp)) selected) ∧
      (1 / 4 : ℝ) ≤ PaperP1.RandomizedSourceFlip.probability P b (g p.1) selected)
    (hjoint : ∀ p ∈ E, Function.Surjective (PaperP1.RawWordObservation.joint M
      (fun i : Fin (K + 1) ↦ p.1.val + i.val) (fun i : Fin (K + 1) ↦ p.2.val + i.val))) :
    ((PaperP1.AnchoredPrivateField.rate K) ^ 2 / 2) * E.card ≤ offsite D P b g := by
  apply PaperP1.PositiveForcingCostLower.selected_pairs_lower univ (law (M := M) P)
    (indicator b) (force D b g) E hE
  intro p hp
  obtain ⟨i, hi, hq⟩ := hclean p hp
  exact clean_weight_lower D P hK b g p.1 p.2 (hactive p hp) i hi (hjoint p hp) hq

theorem selected_pairs_full_cost_lower (D : Data M Y K G Good anchor) (P : FiniteProbability Ξ) (hK : 1 ≤ K)
    (b : Fin (K + 1) → F₂) (g : G → (Fin (K + 1) → F₂) → Ξ → F₂)
    (E : Finset (G × G)) (hE : E ⊆ directed univ)
    (hactive : ∀ p ∈ E, p.1.val ∈ Good) {A N : ℕ}
    (hclean : ∀ p : G × G, ∀ hp : p ∈ E, ∃ selected : Fin (K + 1),
      p.2.val ∈ PaperP1.CleanPivotTargets.targets A N
        (fullPivots D p.1 (hactive p hp) selected).val.val (K + 1)
        (PaperP1.PrivatePivotTargetFlip.otherPrimes (fullPivots D p.1 (hactive p hp)) selected) ∧
      (1 / 4 : ℝ) ≤ PaperP1.RandomizedSourceFlip.probability P b (g p.1) selected)
    (hjoint : ∀ p ∈ E, Function.Surjective (PaperP1.RawWordObservation.joint M
      (fun i : Fin (K + 1) ↦ p.1.val + i.val) (fun i : Fin (K + 1) ↦ p.2.val + i.val))) :
    ((PaperP1.AnchoredPrivateField.rate K) ^ 2 / 2) * E.card ≤ cost D P b g :=
  (selected_pairs_offsite_lower D P hK b g E hE hactive hclean hjoint).trans
    (PaperP1.PositiveForcingCostLower.offsite_le_full_cost univ (law (M := M) P)
      (indicator b) (force D b g) (fun j _ p ↦ force_hits D b g j p))

end PaperP1.RandomizedHybridCleanCost
