module

public import PaperP1.Model.PrivatePrimeForcingUniqueness
public import PaperP1.Model.RandomizedHybridCleanCost

/-! # Every allowed private forcing retains the same good-source half-factor pairs

The behavior outside the deterministic full-good source set is arbitrary.
Only the original prime output is compared; the auxiliary output is free.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RandomizedPrivateForcingClass

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Probability PaperP1.Algebra
  PaperP1.RandomizedHybridField PaperP1.PositiveForcingCostLower

variable {M Y K : ℕ} {G Good : Finset ℕ} {anchor : G → Fin (K + 1)} {Ξ : Type*}

def AgreesOnGood (D : Data M Y K G Good anchor) (b : Fin (K + 1) → F₂)
    (g : G → (Fin (K + 1) → F₂) → Ξ → F₂)
    (F : G → SampleSpace M × Ξ → SampleSpace M × Ξ) : Prop :=
  ∀ j : G, j.val ∈ Good → ∀ p, (F j p).1 = primeForce D b g j p.1 p.2

theorem agrees_of_private_prescription (D : Data M Y K G Good anchor) (b : Fin (K + 1) → F₂)
    (g : G → (Fin (K + 1) → F₂) → Ξ → F₂) (F : G → SampleSpace M × Ξ → SampleSpace M × Ξ)
    (hhit : ∀ j : G, ∀ _hj : j.val ∈ Good, ∀ p,
      PaperP1.PrivateValueSystem.valueSystem M (fun i : Fin (K + 1) ↦ j.val + i.val) (F j p).1 =
        PaperP1.RandomizedPrivatePalmForcing.orientedWord b
          (g j (PaperP1.PrivateValueSystem.valueSystem M (fun i : Fin (K + 1) ↦ j.val + i.val) p.1) p.2))
    (hout : ∀ j : G, ∀ hj : j.val ∈ Good, ∀ p, ∀ r : PrimeUpTo M,
      (∀ i, r ≠ fullPivots D j hj i) → (F j p).1 r = p.1 r) : AgreesOnGood D b g F := by
  intro j hj p
  rw [primeForce_good D b g j hj]
  exact PaperP1.PrivatePrimeForcingUniqueness.randomized_unique
    (fun i : Fin (K + 1) ↦ j.val + i.val) (fullPivots D j hj) (full_basis D j hj) b (g j)
    (fun ω ξ ↦ (F j (ω, ξ)).1) (fun ω ξ ↦ hhit j hj (ω, ξ))
    (fun ω ξ r hr ↦ hout j hj (ω, ξ) r hr) p.1 p.2

variable [Fintype Ξ]

theorem weight_eq_good (D : Data M Y K G Good anchor) (P : FiniteProbability Ξ)
    (b : Fin (K + 1) → F₂) (g : G → (Fin (K + 1) → F₂) → Ξ → F₂)
    (F : G → SampleSpace M × Ξ → SampleSpace M × Ξ) (hF : AgreesOnGood D b g F)
    (j k : G) (hj : j.val ∈ Good) :
    weight (law (M := M) P) (indicator b) F (j, k) =
      weight (law (M := M) P) (indicator b) (force D b g) (j, k) := by
  unfold weight
  congr 1
  apply congrArg (finiteExpectation (law (M := M) P).weight)
  funext p
  change |(indicatorValue (PaperP1.AnchoredPrivateField.indicator b k p.1) : ℝ) -
      indicatorValue (PaperP1.AnchoredPrivateField.indicator b k (F j p).1)| = _
  rw [hF j hj p]
  rfl

theorem selected_pairs_offsite_lower (D : Data M Y K G Good anchor) (P : FiniteProbability Ξ) (hK : 1 ≤ K)
    (b : Fin (K + 1) → F₂) (g : G → (Fin (K + 1) → F₂) → Ξ → F₂)
    (F : G → SampleSpace M × Ξ → SampleSpace M × Ξ) (hF : AgreesOnGood D b g F)
    (E : Finset (G × G)) (hE : E ⊆ directed univ)
    (hactive : ∀ p ∈ E, p.1.val ∈ Good) {A N : ℕ}
    (hclean : ∀ p : G × G, ∀ hp : p ∈ E, ∃ selected : Fin (K + 1),
      p.2.val ∈ PaperP1.CleanPivotTargets.targets A N
        (fullPivots D p.1 (hactive p hp) selected).val.val (K + 1)
        (PaperP1.PrivatePivotTargetFlip.otherPrimes (fullPivots D p.1 (hactive p hp)) selected) ∧
      (1 / 4 : ℝ) ≤ PaperP1.RandomizedSourceFlip.probability P b (g p.1) selected)
    (hjoint : ∀ p ∈ E, Function.Surjective (PaperP1.RawWordObservation.joint M
      (fun i : Fin (K + 1) ↦ p.1.val + i.val) (fun i : Fin (K + 1) ↦ p.2.val + i.val))) :
    ((PaperP1.AnchoredPrivateField.rate K) ^ 2 / 2) * E.card ≤
      PaperP1.PositiveForcingCostLower.offsite univ (law (M := M) P) (indicator b) F := by
  apply PaperP1.PositiveForcingCostLower.selected_pairs_lower univ (law (M := M) P) (indicator b) F E hE
  intro p hp
  rw [weight_eq_good D P b g F hF p.1 p.2 (hactive p hp)]
  obtain ⟨i, hi, hq⟩ := hclean p hp
  exact PaperP1.RandomizedHybridCleanCost.clean_weight_lower D P hK b g p.1 p.2 (hactive p hp)
    i hi (hjoint p hp) hq

end PaperP1.RandomizedPrivateForcingClass
