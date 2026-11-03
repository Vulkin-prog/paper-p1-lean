module

public import PaperP1.Algebra.GradedVeroneseChartEquiv
public import PaperP1.Algebra.StandardVeroneseCoordinates
public import PaperP1.Algebra.SourceVeroneseGradedBaseMap

/-! # Literal coordinate-chart equivalences for the native base and the actual source -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.VeroneseCoordinateCharts

open HomogeneousLocalization PaperP1.SourceVeroneseGrading
  PaperP1.HomogeneousSplitRadicalRelations PaperP1.HomogeneousSplitRadicalGrading
  PaperP1.HomogeneousSplitRadicalVeronese PaperP1.HomogeneousSplitRadicalFiniteVeronese
  PaperP1.StandardVeroneseCoordinates

attribute [local instance] MvPolynomial.gradedAlgebra

def nativeEquiv (F : Type*) [Field F] (D : ℕ) (hD : 0 < D) (j : Fin 3) :
    letI := nativeGrading F D hD
    Away (nativePiece F D) (coordinatePower F D j) ≃+*
      Away (MvPolynomial.homogeneousSubmodule (Fin 3) F) (MvPolynomial.X j) := by
  let := nativeGrading F D hD
  exact GradedVeroneseChartEquiv.equiv (MvPolynomial.homogeneousSubmodule (Fin 3) F) D hD
    (MvPolynomial.isHomogeneous_X F j)

def baseVariable {F ι : Type*} [Field F] (c : ι → F) (D : ℕ) (I J : ι → Finset ℤ) (j : Fin 3) :
    CoordinateRing c D I J := Ideal.Quotient.mk (relationIdeal c D I J) (MvPolynomial.X (Sum.inl j))

def sourceCoordinate {F ι : Type*} [Field F] (c : ι → F) (D : ℕ) (I J : ι → Finset ℤ)
    (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D) (j : Fin 3) :
    HomogeneousSplitRadicalVeronese.veronese c D I J := by
  let := grading c D I J hdeg
  exact GradedVeroneseChart.coordinate (piece c D I J) D (base_variable_mem c D I J j)

theorem sourceCoordinate_val {F ι : Type*} [Field F] (c : ι → F) (D : ℕ) (I J : ι → Finset ℤ)
    (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D) (j : Fin 3) :
    (sourceCoordinate c D I J hdeg j : CoordinateRing c D I J) = baseVariable c D I J j ^ D := rfl

theorem sourceCoordinate_mem {F ι : Type*} [Field F] (c : ι → F) (D : ℕ) (I J : ι → Finset ℤ)
    (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D) (j : Fin 3) :
    sourceCoordinate c D I J hdeg j ∈ sourcePiece c D I J 1 := by
  let := grading c D I J hdeg
  exact GradedVeroneseChart.coordinate_mem (piece c D I J) D (base_variable_mem c D I J j)

def sourceEquiv {F ι : Type*} [Field F] (c : ι → F) (D : ℕ) (I J : ι → Finset ℤ)
    (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D) (hD : 0 < D) (j : Fin 3) :
    letI := grading c D I J hdeg
    letI := sourceGrading c D I J hdeg hD
    Away (sourcePiece c D I J) (sourceCoordinate c D I J hdeg j) ≃+*
      Away (piece c D I J) (baseVariable c D I J j) := by
  let := grading c D I J hdeg
  let := sourceGrading c D I J hdeg hD
  exact GradedVeroneseChartEquiv.equiv (piece c D I J) D hD (base_variable_mem c D I J j)

theorem sourceCoordinate_eq_image {F : Type*} [Field F]
    (s : List (HomogeneousSplitRadicalData.PolynomialRing F)) (c : Fin s.length → F) (D : ℕ)
    (I J : Fin s.length → Finset ℤ) (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D)
    (hD : 0 < D)
    (hs : ∀ i, s.get i = HomogeneousSplitRadicalData.radicand
      (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i)) (j : Fin 3) :
    sourceCoordinate c D I J hdeg j =
      SourceVeroneseGradedBaseMap.gradedBaseMap s c D hD I J hs (coordinatePower F D j) := by
  apply Subtype.ext
  change baseVariable c D I J j ^ D =
    HomogeneousSplitRadicalBaseInjection.basePolynomialMap c D I J (MvPolynomial.X j ^ D)
  rw [map_pow]
  change baseVariable c D I J j ^ D =
    quotientMap c D I J (MvPolynomial.rename Sum.inl (MvPolynomial.X j)) ^ D
  rw [MvPolynomial.rename_X]
  rfl

end PaperP1.VeroneseCoordinateCharts
