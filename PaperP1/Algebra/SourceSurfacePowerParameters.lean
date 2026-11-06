module

public import PaperP1.Algebra.NativeSurfacePowerParameters
public import PaperP1.Algebra.SourceVeroneseScalars
public import PaperP1.Algebra.SourceVeroneseGradedBaseMap
public import PaperP1.Algebra.SourceVeroneseHilbertPolynomial
public import PaperP1.Algebra.FiniteSurfaceParameterRank

/-! # The actual source surface has three finite injective linear power parameters of rank 2^k D² -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SourceSurfacePowerParameters

open MvPolynomial HomogeneousSplitRadicalData HomogeneousSplitRadicalVeronese
  HomogeneousSplitRadicalBaseInjection SourceVeroneseGrading SourceVeroneseGradedBaseMap
  StandardVeroneseCoordinates SourceVeroneseScalars

local instance polynomialRing (F : Type*) [Field F] : CommRing (PolynomialRing F) := inferInstance
local instance nativeRing (F : Type*) [Field F] : CommRing (MvPolynomial (Fin 3) F) := inferInstance
local instance weightedRing (F ι : Type*) [Field F] : CommRing (HomogeneousSplitRadicalRelations.WeightedPolynomial F ι) := inferInstance

variable {F : Type*} [Field F]
  (s : List (PolynomialRing F)) (c : Fin s.length → F) (D : ℕ) (hD : 0 < D)
  (I J : Fin s.length → Finset ℤ)
  (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i))

def parameters (j : Fin 3) : veronese c D I J :=
  standardBaseMap s c D hD I J hs (coordinatePower F D j)

def map : MvPolynomial (Fin 3) F →ₐ[F] veronese c D I J :=
  aeval (parameters s c D hD I J hs)

theorem parameter_mem (j : Fin 3) : parameters s c D hD I J hs j ∈ sourcePiece c D I J 1 :=
  standardBaseMap_mem s c D hD I J hs 1 _ (coordinatePower_mem F D j)

theorem factor : map s c D hD I J hs =
    (standardBaseAlgHom s c D hD I J hs).comp (NativeSurfacePowerParameters.map F D) := by
  apply MvPolynomial.algHom_ext
  intro j
  change aeval (parameters s c D hD I J hs) (X j) =
    standardBaseAlgHom s c D hD I J hs (NativeSurfacePowerParameters.map F D (X j))
  rw [aeval_X, NativeSurfacePowerParameters.map_X]
  rfl

theorem injective : Function.Injective (map s c D hD I J hs) := by
  rw [factor]
  exact (standardBaseMap_injective s c D hD I J hs).comp
    (NativeSurfacePowerParameters.injective F D hD)

theorem finite (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D) :
    (map s c D hD I J hs).Finite := by
  rw [factor]
  exact (standardBaseMap_finite s c D hD I J hs hdeg).comp
    (NativeSurfacePowerParameters.finite F D hD)

theorem rank [CharZero F] (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D)
    (hc : ∀ i, c i ≠ 0) (hne : ∀ i, (I i).Nonempty ∨ (J i).Nonempty)
    (hI : Pairwise fun i j ↦ Disjoint (I i) (I j))
    (hJ : Pairwise fun i j ↦ Disjoint (J i) (J j)) :
    letI : Algebra (MvPolynomial (Fin 3) F) (veronese c D I J) :=
      (map s c D hD I J hs).toRingHom.toAlgebra
    Module.finrank (MvPolynomial (Fin 3) F) (veronese c D I J) = 2 ^ s.length * D ^ 2 := by
  let := sourceGrading c D I J hdeg hD
  let := source_isDomain s c D I J hs hc hne hI hJ
  let (n : ℕ) : Module.Finite F (sourcePiece c D I J n) :=
    SourceVeroneseHilbert.piece_finite_all s c D I J hdeg hs hD n
  have hh := FiniteSurfaceParameterRank.rank_eq_twice_coefficient (sourcePiece c D I J)
    (parameters s c D hD I J hs) (parameter_mem s c D hD I J hs)
    (finite s c D hD I J hs hdeg) (injective s c D hD I J hs)
    (SourceVeroneseHilbertPolynomial.polynomial s c D I J hdeg)
    (SourceVeroneseHilbertPolynomial.natDegree_le s c D I J hdeg)
    (SourceVeroneseHilbertPolynomial.isHilbertPolynomial s c D I J hdeg hs hD)
  let : Algebra (MvPolynomial (Fin 3) F) (veronese c D I J) :=
    (map s c D hD I J hs).toRingHom.toAlgebra
  change (Module.finrank (MvPolynomial (Fin 3) F) (veronese c D I J) : ℚ) = _ at hh
  rw [SourceVeroneseHilbertPolynomial.coeff_two] at hh
  have he : (Module.finrank (MvPolynomial (Fin 3) F) (veronese c D I J) : ℚ) =
      ((2 ^ s.length * D ^ 2 : ℕ) : ℚ) := by
    push_cast
    linarith
  exact_mod_cast he

end PaperP1.SourceSurfacePowerParameters
