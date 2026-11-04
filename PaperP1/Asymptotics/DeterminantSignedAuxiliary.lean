module

public import PaperP1.Arithmetic.DeterminantReversedClusters
public import PaperP1.Asymptotics.DeterminantBoxAuxiliary

/-! # Actual bounded auxiliary curves uniformly for both nonzero signs of the shift -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DeterminantSignedAuxiliary

open Finset PaperP1.DeterminantSourceBox PaperP1.TwoKernelDeterminantBoxes
  PaperP1.DeterminantIntegerRows PaperP1.DeterminantRelativeIntervals
  PaperP1.DeterminantIntervalPartition PaperP1.DeterminantHorizontalScale
  PaperP1.DeterminantAuxiliaryBiform PaperP1.DeterminantSignedBoxes
  PaperP1.DeterminantCoordinateFlip PaperP1.DeterminantReversedClusters

def signedCluster (h : ℤ) (M : ℕ) (D E : ℝ) (k : ℕ) (S : Finset Quad) : Finset Quad :=
  if h < 0 then reversedCluster M D E k S else cluster M D E k S

theorem uniform_biforms (δ C ρ Kshift A₀ ζ : ℝ)
    (hδ : 0 < δ) (hC : 0 < C) (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1)
    (hζ : 0 < ζ) (hζsmall : ζ < 7 / 16) :
    ∃ B Amax κ N₀ : ℕ, 0 < B ∧ ∀ N ≥ N₀, ∀ h : ℤ,
      h ≠ 0 → (h.natAbs : ℝ) ≤ Kshift * (Real.log N) ^ A₀ →
      ∀ X : Box N ρ C δ, ∀ S : Finset Quad, SignedPopulation X h S →
      let M := horizontalScale N X.D X.E X.U X.V ζ
      4 ≤ M ∧ S.card = ∑ k ∈ intervalIndices M, (signedCluster h M X.D X.E k S).card ∧
      ∀ k ∈ intervalIndices M, (signedCluster h M X.D X.E k S).Nonempty →
        ∃ A : ℕ, 0 < A ∧ A ≤ Amax ∧ ∃ w : Exponent A B → ℤ,
          biform A B w ≠ 0 ∧ (biform A B w).IsHomogeneous A ∧
          (∀ a, (forms A B w a).IsHomogeneous B) ∧
          (∀ m n, |((biform A B w).coeff m).coeff n| ≤ ((N ^ κ : ℕ) : ℤ)) ∧
          ∀ p ∈ signedCluster h M X.D X.E k S,
            MvPolynomial.eval₂ (MvPolynomial.eval ![(p.2.2 : ℤ), p.2.1])
              ![(p.1.1 : ℤ), p.1.2] (biform A B w) = 0 := by
  obtain ⟨B, Amax, κ, N₀, hB, haux⟩ :=
    DeterminantBoxAuxiliary.uniform_biforms δ C ρ Kshift A₀ ζ hδ hC hρ hρ₁ hζ hζsmall
  refine ⟨B, Amax, κ, N₀, hB, ?_⟩
  intro N hN h hh hshift X S hS
  have hhpos : 0 < h.natAbs := Int.natAbs_pos.mpr hh
  by_cases hneg : h < 0
  · have hp := haux N hN h.natAbs hhpos hshift (swappedBox X) (S.image coordinateFlip)
      (negative_population X h hneg S hS)
    simp only [horizontalScale_swap] at hp
    obtain ⟨hM₄, hpartition, hcurves⟩ := hp
    refine ⟨hM₄, ?_, ?_⟩
    · simp only [signedCluster, ite_eq_left hneg]
      exact reversed_partition _ X.D X.E S hpartition
    · intro k hk hnonempty
      have hn : (reversedCluster (horizontalScale N X.D X.E X.U X.V ζ) X.D X.E k S).Nonempty := by
        simpa only [signedCluster, ite_eq_left hneg] using hnonempty
      obtain ⟨A, hA₀, hA, w, hw₀, _, _, hheight, hzero⟩ := hcurves k hk (flipped_cluster_nonempty _ _ _ k S hn)
      refine ⟨A, hA₀, hA, reverseCoefficients A B w, reverse_biform_nonzero A B w hw₀,
        biform_homogeneous A B _, forms_homogeneous A B _, reverse_biform_height A B (N ^ κ) w hheight, ?_⟩
      intro p hp
      have hp' : p ∈ reversedCluster (horizontalScale N X.D X.E X.U X.V ζ) X.D X.E k S := by
        simpa only [signedCluster, ite_eq_left hneg] using hp
      rw [biform_evaluation_flip]
      exact hzero (coordinateFlip p) (flipped_mem_cluster _ _ _ k S p hp')
  · have hp := haux N hN h.natAbs hhpos hshift X S (positive_population X h (by omega) S hS)
    simpa only [signedCluster, ite_eq_right hneg] using hp

end PaperP1.DeterminantSignedAuxiliary
