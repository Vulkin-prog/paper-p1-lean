module

public import PaperP1.Algebra.SourceVeroneseHilbert
public import PaperP1.Algebra.WeightedVeroneseHilbertPolynomial
public import PaperP1.Algebra.GradedHilbertPolynomial
public import Mathlib.Tactic.Positivity

/-! # The actual source Hilbert polynomial and its multiplicity 2^k D² -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SourceVeroneseHilbertPolynomial

open Polynomial PaperP1.HomogeneousSplitRadicalData PaperP1.HomogeneousSplitRadicalRelations
  PaperP1.QuadraticTowerHomogeneousBasis PaperP1.FiniteQuadraticTower

local instance polynomialRing (F : Type*) [Field F] : CommRing (PolynomialRing F) := inferInstance
local instance nativeRing (F : Type*) [Field F] : CommRing (MvPolynomial (Fin 3) F) := inferInstance
local instance weightedRing (F ι : Type*) [Field F] : CommRing (WeightedPolynomial F ι) := inferInstance
local instance targetRing (F : Type*) [Field F] (k : ℕ) :
    CommRing (MvPolynomial (Fin k) (PolynomialRing F)) := inferInstance

variable {F : Type*} [Field F] (s : List (PolynomialRing F)) (c : Fin s.length → F) (D : ℕ)
  (I J : Fin s.length → Finset ℤ) (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D)

def polynomial : ℚ[X] := WeightedVeroneseHilbertPolynomial.polynomial D
  (indexWeight (RelativeVeroneseMap.radicands s c D I J hdeg))

theorem coeff_two : (polynomial s c D I J hdeg).coeff 2 = (2 : ℚ) ^ s.length * (D : ℚ) ^ 2 / 2 := by
  rw [polynomial, WeightedVeroneseHilbertPolynomial.polynomial_coeff_two, index_card,
    RelativeVeroneseMap.radicands_length]
  push_cast
  rfl

theorem natDegree_le : (polynomial s c D I J hdeg).natDegree ≤ 2 :=
  WeightedVeroneseHilbertPolynomial.polynomial_natDegree_le D _

theorem natDegree (hD : 0 < D) : (polynomial s c D I J hdeg).natDegree = 2 := by
  apply natDegree_eq_of_le_of_coeff_ne_zero (natDegree_le s c D I J hdeg)
  rw [coeff_two]
  have : (0 : ℚ) < D := Nat.cast_pos.mpr hD
  positivity

theorem leadingCoeff (hD : 0 < D) :
    (polynomial s c D I J hdeg).leadingCoeff = (2 : ℚ) ^ s.length * (D : ℚ) ^ 2 / 2 := by
  rw [Polynomial.leadingCoeff, natDegree s c D I J hdeg hD, coeff_two]

variable (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i)) (hD : 0 < D)

include hs hD in
theorem isHilbertPolynomial : GradedHilbertPolynomial.IsHilbertPolynomial
    (SourceVeroneseGrading.sourcePiece c D I J) (polynomial s c D I J hdeg) := by
  refine ⟨s.length, fun n hn ↦ ?_⟩
  rw [polynomial, WeightedVeroneseHilbertPolynomial.polynomial_eval D _ n (fun j ↦
    (SourceVeroneseHomogeneousBasis.sourceBasis_degree_bound s c D I J hdeg j).trans hn),
    SourceVeroneseHilbert.piece_finrank s c D I J hdeg hs hD n hn]

include hdeg hs hD in
theorem exists_polynomial : ∃ p, GradedHilbertPolynomial.IsHilbertPolynomial
    (SourceVeroneseGrading.sourcePiece c D I J) p :=
  ⟨polynomial s c D I J hdeg, isHilbertPolynomial s c D I J hdeg hs hD⟩

theorem canonical_polynomial : GradedHilbertPolynomial.polynomial
    (SourceVeroneseGrading.sourcePiece c D I J) (exists_polynomial s c D I J hdeg hs hD) =
      polynomial s c D I J hdeg :=
  GradedHilbertPolynomial.polynomial_eq _ _ _ (isHilbertPolynomial s c D I J hdeg hs hD)

theorem multiplicity : GradedHilbertPolynomial.multiplicity
    (SourceVeroneseGrading.sourcePiece c D I J) (exists_polynomial s c D I J hdeg hs hD) =
      ((2 ^ s.length * D ^ 2 : ℕ) : ℚ) := by
  rw [GradedHilbertPolynomial.multiplicity_eq _ _ _ (isHilbertPolynomial s c D I J hdeg hs hD),
    natDegree s c D I J hdeg hD, leadingCoeff s c D I J hdeg hD]
  norm_num
  ring

end PaperP1.SourceVeroneseHilbertPolynomial
