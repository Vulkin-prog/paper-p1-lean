module

public import PaperP1.Algebra.GradedFreePieceBasis
public import PaperP1.Algebra.StandardVeronesePieceBasis
public import PaperP1.Algebra.SourceVeroneseScalars
public import PaperP1.Algebra.SourceVeroneseHomogeneousBasis

/-! # Explicit coefficient-field bases of the actual source and all its homogeneous pieces -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SourceVeroneseVectorBasis

open Module PaperP1.HomogeneousSplitRadicalData PaperP1.HomogeneousSplitRadicalRelations
  PaperP1.HomogeneousSplitRadicalGrading PaperP1.HomogeneousSplitRadicalVeroneseTowerData
  PaperP1.SourceVeroneseGrading PaperP1.SourceVeroneseGradedBaseMap
  PaperP1.QuadraticTowerHomogeneousBasis PaperP1.FiniteQuadraticTower

local instance polynomialRing (F : Type*) [Field F] : CommRing (PolynomialRing F) := inferInstance
local instance nativeRing (F : Type*) [Field F] : CommRing (MvPolynomial (Fin 3) F) := inferInstance
local instance weightedRing (F ι : Type*) [Field F] : CommRing (WeightedPolynomial F ι) := inferInstance
local instance targetRing (F : Type*) [Field F] (k : ℕ) :
    CommRing (MvPolynomial (Fin k) (PolynomialRing F)) := inferInstance

abbrev BaseIndex (D : ℕ) := Σ n : ℕ, {d : Fin 3 →₀ ℕ // d.degree = n * D}

variable {F : Type*} [Field F] (s : List (PolynomialRing F)) (c : Fin s.length → F) (D : ℕ)
  (I J : Fin s.length → Finset ℤ) (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D)
  (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i)) (hD : 0 < D)

def basis : Basis (BaseIndex D × Index (RelativeVeroneseMap.radicands s c D I J hdeg)) F
    (HomogeneousSplitRadicalVeronese.veronese c D I J) := by
  let := nativeGrading F D hD
  let := sourceGrading c D I J hdeg hD
  exact GradedFreePieceBasis.basis (gradedBaseMap s c D hD I J hs)
    (SourceVeroneseScalars.standardBaseMap_commutes s c D hD I J hs)
    (StandardVeronesePieceBasis.basis F D hD) (RelativeVeroneseBasis.sourceBasis s c D I J hdeg hs hD)

theorem basis_mem (i : BaseIndex D × Index (RelativeVeroneseMap.radicands s c D I J hdeg)) :
    basis s c D I J hdeg hs hD i ∈
      sourcePiece c D I J (i.1.1 + indexWeight (RelativeVeroneseMap.radicands s c D I J hdeg) i.2) := by
  let := nativeGrading F D hD
  let := sourceGrading c D I J hdeg hD
  exact GradedFreePieceBasis.basis_mem (gradedBaseMap s c D hD I J hs)
    (SourceVeroneseScalars.standardBaseMap_commutes s c D hD I J hs)
    (StandardVeronesePieceBasis.basis F D hD) (RelativeVeroneseBasis.sourceBasis s c D I J hdeg hs hD)
    (fun j ↦ j.1) (indexWeight (RelativeVeroneseMap.radicands s c D I J hdeg))
    (StandardVeronesePieceBasis.basis_mem F D hD)
    (SourceVeroneseHomogeneousBasis.sourceBasis_mem s c D I J hdeg hs hD) i

set_option backward.isDefEq.respectTransparency false in
theorem basis_val (i : BaseIndex D × Index (RelativeVeroneseMap.radicands s c D I J hdeg)) :
    (basis s c D I J hdeg hs hD i : CoordinateRing c D I J) =
      HomogeneousSplitRadicalBaseInjection.basePolynomialMap c D I J (MvPolynomial.monomial i.1.2.1 1) *
        RelativeVeroneseMap.toQuotient s c D I J hdeg hs
          (FiniteQuadraticTower.basis (Base F D) (RelativeVeroneseMap.radicands s c D I J hdeg) i.2) := by
  let := nativeGrading F D hD
  let := sourceGrading c D I J hdeg hD
  let : Algebra (Base F D) (HomogeneousSplitRadicalVeronese.veronese c D I J) :=
    (HomogeneousSplitRadicalBaseInjection.standardBaseMap s c D hD I J hs).toAlgebra
  rw [basis, GradedFreePieceBasis.basis_apply]
  change HomogeneousSplitRadicalBaseInjection.basePolynomialMap c D I J
      (StandardVeronesePieceBasis.basis F D hD i.1 : MvPolynomial (Fin 3) F) *
        (RelativeVeroneseBasis.sourceBasis s c D I J hdeg hs hD i.2 : CoordinateRing c D I J) = _
  rw [StandardVeronesePieceBasis.basis_val, RelativeVeroneseBasis.sourceBasis_apply]

def pieceBasis (n : ℕ) :
    Basis {i : BaseIndex D × Index (RelativeVeroneseMap.radicands s c D I J hdeg) //
      i.1.1 + indexWeight (RelativeVeroneseMap.radicands s c D I J hdeg) i.2 = n} F
      (sourcePiece c D I J n) := by
  let := sourceGrading c D I J hdeg hD
  exact HomogeneousPieceBasis.pieceBasis (sourcePiece c D I J) (basis s c D I J hdeg hs hD)
    (fun i ↦ i.1.1 + indexWeight (RelativeVeroneseMap.radicands s c D I J hdeg) i.2)
    (basis_mem s c D I J hdeg hs hD) n

theorem pieceBasis_apply (n : ℕ)
    (i : {i : BaseIndex D × Index (RelativeVeroneseMap.radicands s c D I J hdeg) //
      i.1.1 + indexWeight (RelativeVeroneseMap.radicands s c D I J hdeg) i.2 = n}) :
    (pieceBasis s c D I J hdeg hs hD n i : HomogeneousSplitRadicalVeronese.veronese c D I J) =
      basis s c D I J hdeg hs hD i.1 := by
  let := sourceGrading c D I J hdeg hD
  exact HomogeneousPieceBasis.pieceBasis_apply (sourcePiece c D I J) (basis s c D I J hdeg hs hD)
    (fun i ↦ i.1.1 + indexWeight (RelativeVeroneseMap.radicands s c D I J hdeg) i.2)
    (basis_mem s c D I J hdeg hs hD) n i

end PaperP1.SourceVeroneseVectorBasis
