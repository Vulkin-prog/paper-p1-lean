module

public import PaperP1.Model.RandomizedPrivateForcingBoundaryPairs
public import PaperP1.Model.RandomizedHybridSourceSelection
public import PaperP1.Model.RandomizedDyadicHybridField
public import PaperP1.Asymptotics.ForcingExceptionLedger
public import PaperP1.Analysis.CleanPairReciprocalLower

/-! # Actual offsite cost of every private forcing from the literal ordinary source census

The half-factor comes from proved actual pair weights. Quarter-flip
source selection and the reciprocal lower bound are constructed here,
with all raw-dependence and bad-target counts discharged internally.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RandomizedPrivateClassCostFromCensus

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.ForcingExceptionalSets
  PaperP1.RandomizedHybridField PaperP1.RandomizedHybridBoundaryPairs
  PaperP1.RandomizedHybridSourceData PaperP1.OrdinarySmoothSourcePopulation
  PaperP1.CleanPivotPairs

theorem uniform_ordinary_candidates_lower (D : ℝ) (hD : 0 ≤ D) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ B Y Z K M : ℕ, ∀ Q : ℝ,
      1 ≤ K → K + 1 ≤ B → B ≤ Y → (B : ℝ) ≤ D * Real.log N →
      Y ≤ Z → (Z : ℝ) ≤ (Real.log N) ^ 5 → 2 * N + B ≤ M →
      ((K : ℝ) * (K + 1 : ℕ) + 1) ≤ Z →
      ∀ anchor : PaperP1.AnchoredDyadicField.retainedBoundaries N B Y → Fin (K + 1),
      ∀ A : Data M Y K (PaperP1.AnchoredDyadicField.retainedBoundaries N B Y)
        (PaperP1.RandomizedDyadicHybridField.fullGood N B Z) anchor,
      ∀ (Ξ : Type*) [Fintype Ξ], ∀ P : PaperP1.Probability.FiniteProbability Ξ,
      ∀ b : Fin (K + 1) → F₂,
      ∀ g : PaperP1.AnchoredDyadicField.retainedBoundaries N B Y → (Fin (K + 1) → F₂) → Ξ → F₂,
      ∀ F : PaperP1.AnchoredDyadicField.retainedBoundaries N B Y →
        SampleSpace M × Ξ → SampleSpace M × Ξ,
      PaperP1.RandomizedPrivateForcingClass.AgreesOnGood A b g F →
      ((PaperP1.AnchoredPrivateField.rate K) ^ 2 / 2) *
        ((1 - ((K : ℝ) * (K + 1 : ℕ) + 1) / Z) * N *
            ((goodSources N K B Z Q).card / Q) -
          (((K : ℝ) * (K + 1 : ℕ) + 1) + 1) * (goodSources N K B Z Q).card -
          (N : ℝ) ^ (19 / 10 + ε : ℝ) - (N : ℝ) ^ (3 / 2 + ε : ℝ)) ≤
      PaperP1.PositiveForcingCostLower.offsite univ (law (M := M) P) (indicator b) F := by
  obtain ⟨NE, hE⟩ := PaperP1.ForcingExceptionLedger.uniform_surviving_lower D hD ε hε
  refine ⟨NE, ?_⟩
  intro N hN B Y Z K M Q hK hKB hBY hB hYZ hZ hM hcollision anchor A Ξ _ P b g F hF
  have hn : 2 ≤ N := by omega
  let J := goodSources N K B Z Q
  have hG := PaperP1.AnchoredDyadicField.retained_subset N B Y
  have hactive : J ⊆ PaperP1.RandomizedDyadicHybridField.fullGood N B Z :=
    PaperP1.RandomizedDyadicHybridField.ordinary_sources_subset N K B Z Q
  have hJ : J ⊆ PaperP1.AnchoredDyadicField.retainedBoundaries N B Y :=
    hactive.trans (PaperP1.RandomizedDyadicHybridField.fullGood_subset_retained hn hYZ)
  have hgood : ∀ j ∈ J, j ∉ badBoundaries N B Z := fun _ hj ↦ (mem_goodSources.mp hj).2.2
  have hOrd : ∀ j ∈ J, 2 ≤ (PaperP1.NonanchorPivotSelection.ordinaryIndices j (K + 1) Q).card :=
    fun _ hj ↦ (mem_goodSources.mp hj).2.1
  obtain ⟨selected, hQ, hquarter⟩ := PaperP1.RandomizedHybridSourceSelection.exists_selector A P b g J Q hJ hactive hOrd
  have hq : ∀ j ∈ J, Z ≤ selectedPrime A selected j := by
    intro j hj
    exact (source_conditions A selected hn hKB hG ⟨j, hJ hj⟩ (hactive hj) (hgood j hj)).1
  have hr : ∀ j ∈ J, ∀ r ∈ otherPrimes A selected j, Z ≤ r := by
    intro j hj
    exact (source_conditions A selected hn hKB hG ⟨j, hJ hj⟩ (hactive hj) (hgood j hj)).2.1
  have hcop : ∀ j ∈ J, ∀ r ∈ otherPrimes A selected j, (selectedPrime A selected j).Coprime r := by
    intro j hj
    exact (source_conditions A selected hn hKB hG ⟨j, hJ hj⟩ (hactive hj) (hgood j hj)).2.2.1
  have hsize : ∀ j ∈ J, (otherPrimes A selected j).card ≤ K := by
    intro j hj
    exact (source_conditions A selected hn hKB hG ⟨j, hJ hj⟩ (hactive hj) (hgood j hj)).2.2.2
  have hl := hE N (by omega) B Z M (K + 1) (K + 1) K (by omega) hB (by omega) hZ
    hM hKB hKB J (hJ.trans hG) (selectedPrime A selected) (otherPrimes A selected) hq hr hcop hsize
  have hrec := reciprocal_lower A selected J Q hQ
  have hz : (0 : ℝ) < Z := by exact_mod_cast (show 0 < Z by omega)
  have hf := PaperP1.CleanPairReciprocalLower.substitute_lower
    (n := (N : ℝ)) (s := reciprocalSum J (selectedPrime A selected)) (j := (J.card : ℝ))
    (c := (K : ℝ) * (K + 1 : ℕ) + 1) (z := (Z : ℝ)) (Q := Q)
    (Nat.cast_nonneg N) hz hcollision hrec
  have herr := sub_le_sub_right (sub_le_sub_right hf ((N : ℝ) ^ (19 / 10 + ε : ℝ)))
    ((N : ℝ) ^ (3 / 2 + ε : ℝ))
  have hcount := herr.trans hl
  have hretain : ∀ n ∈ boundaryBlock N, n ∉ badBoundaries N B Z →
      n ∈ PaperP1.AnchoredDyadicField.retainedBoundaries N B Y :=
    fun _ hnB hbad ↦ PaperP1.AnchoredDyadicField.retained_of_not_bad hn hYZ hnB hbad
  have hc := PaperP1.RandomizedPrivateForcingBoundaryPairs.actual_offsite_lower A P hK b g selected F hF hn hG hretain hJ hactive hquarter
  exact (mul_le_mul_of_nonneg_left hcount (by positivity :
    (0 : ℝ) ≤ (PaperP1.AnchoredPrivateField.rate K) ^ 2 / 2)).trans hc

end PaperP1.RandomizedPrivateClassCostFromCensus
