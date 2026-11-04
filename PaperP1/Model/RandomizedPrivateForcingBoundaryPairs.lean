module

public import PaperP1.Model.RandomizedPrivateForcingClass
public import PaperP1.Model.RandomizedHybridBoundaryPairs

/-! # The exact surviving arithmetic pairs for every allowed private prime forcing -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RandomizedPrivateForcingBoundaryPairs

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.ForcingExceptionalSets
  PaperP1.RandomizedHybridField PaperP1.RandomizedHybridBoundaryPairs

variable {M Y K : ℕ} {G Good : Finset ℕ} {anchor : G → Fin (K + 1)}

theorem actual_offsite_lower {Ξ : Type*} [Fintype Ξ]
    (D : Data M Y K G Good anchor) (P : PaperP1.Probability.FiniteProbability Ξ) (hK : 1 ≤ K)
    (b : Fin (K + 1) → F₂) (g : G → (Fin (K + 1) → F₂) → Ξ → F₂) (selected : G → Fin (K + 1))
    (F : G → SampleSpace M × Ξ → SampleSpace M × Ξ)
    (hF : PaperP1.RandomizedPrivateForcingClass.AgreesOnGood D b g F)
    {N B Z : ℕ} {J : Finset ℕ} (hN : 2 ≤ N) (hG : G ⊆ boundaryBlock N)
    (hretain : ∀ n ∈ boundaryBlock N, n ∉ badBoundaries N B Z → n ∈ G)
    (hJ : J ⊆ G) (hactive : J ⊆ Good)
    (hquarter : ∀ j : ℕ, ∀ hj : j ∈ J, (1 / 4 : ℝ) ≤
      PaperP1.RandomizedSourceFlip.probability P b (g ⟨j, hJ hj⟩) (selected ⟨j, hJ hj⟩)) :
    ((PaperP1.AnchoredPrivateField.rate K) ^ 2 / 2) * (survivingPairs D selected N B Z J).card ≤
      PaperP1.PositiveForcingCostLower.offsite univ (law (M := M) P) (indicator b) F := by
  let V := survivingPairs D selected N B Z J
  have hm := fun p hp ↦ surviving_metadata D selected hN hG hretain hJ hactive (p := p) hp
  have hmeta : ∀ p ∈ V, p.1 ∈ G ∧ p.2 ∈ G := fun p hp ↦ ⟨(hm p hp).1, (hm p hp).2.1⟩
  let E := PaperP1.AnchoredCleanBoundaryPairs.liftedPairs V hmeta
  have hE : E ⊆ PaperP1.PositiveForcingCostLower.directed univ := by
    intro a ha
    obtain ⟨p, _, rfl⟩ := mem_image.mp ha
    apply mem_filter.mpr
    refine ⟨mem_product.mpr ⟨mem_univ _, mem_univ _⟩, ?_⟩
    intro he
    exact PaperP1.AnchoredCleanBoundaryPairs.joint_surjective_ne (hm p.val p.property).2.2.2
      (congrArg Subtype.val he).symm
  have hactiveE : ∀ a ∈ E, a.1.val ∈ Good := by
    intro a ha
    obtain ⟨p, _, rfl⟩ := mem_image.mp ha
    exact (hm p.val p.property).2.2.1
  have hcleanE : ∀ a : G × G, ∀ ha : a ∈ E, ∃ i : Fin (K + 1),
      a.2.val ∈ PaperP1.CleanPivotTargets.targets (N - 2) N
        (fullPivots D a.1 (hactiveE a ha) i).val.val (K + 1)
        (PaperP1.PrivatePivotTargetFlip.otherPrimes (fullPivots D a.1 (hactiveE a ha)) i) ∧
      (1 / 4 : ℝ) ≤ PaperP1.RandomizedSourceFlip.probability P b (g a.1) i := by
    intro a ha
    obtain ⟨p, _, rfl⟩ := mem_image.mp ha
    have hjJ := (PaperP1.CleanPivotPairs.mem_pairs.mp (mem_sdiff.mp p.property).1).1
    have hjGood := hactive hjJ
    let j : G := ⟨p.val.1, (hmeta p.val p.property).1⟩
    refine ⟨selected j, ?_, hquarter p.val.1 hjJ⟩
    have ht := (PaperP1.CleanPivotPairs.mem_pairs.mp (mem_sdiff.mp p.property).1).2
    rw [selectedPrime_apply D selected j hjGood, otherPrimes_apply D selected j hjGood] at ht
    exact ht
  have hjointE : ∀ a ∈ E, Function.Surjective (PaperP1.RawWordObservation.joint M
      (fun i : Fin (K + 1) ↦ a.1.val + i.val) (fun i : Fin (K + 1) ↦ a.2.val + i.val)) := by
    intro a ha
    obtain ⟨p, _, rfl⟩ := mem_image.mp ha
    exact (hm p.val p.property).2.2.2
  have hl := PaperP1.RandomizedPrivateForcingClass.selected_pairs_offsite_lower D P hK b g F hF E hE hactiveE hcleanE hjointE
  rw [PaperP1.AnchoredCleanBoundaryPairs.liftedPairs_card] at hl
  exact hl


end PaperP1.RandomizedPrivateForcingBoundaryPairs
