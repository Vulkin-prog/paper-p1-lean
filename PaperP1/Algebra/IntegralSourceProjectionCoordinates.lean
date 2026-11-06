module

public import PaperP1.Algebra.NativeAffineMonomialCoordinates
public import PaperP1.Algebra.IntegralSplitRadicalReduction
public import PaperP1.Algebra.SourceAffineChartCoordinates
public import PaperP1.Geometry.SourceSurfaceBoundedProjection

/-! # Every original chosen projection coordinate has one literal integral lift compatible with all fields

This includes all monomials and radicals, the chosen primitive combination,
the power parameters and the normalized coordinate. The generator-index
transport is an actual equivalence. No projection-compatibility premise is used.
-/

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.IntegralSourceProjectionCoordinates
open Polynomial Finset
open PaperP1.IntegralSplitRadicalModel PaperP1.FiniteQuadraticTower
open PaperP1.SourceProjectiveEmbedding PaperP1.SplitWeightedGeneratorIndex
open PaperP1.SourceVeroneseGrading PaperP1.HomogeneousSplitRadicalBaseInjection
open scoped Classical

local instance indexFinite (F : Type*) [Field F] (k D : ℕ) : Finite (GeneratorIndex F (Fin k) D) :=
  PaperP1.SourceProjectiveEmbedding.index_finite F (Fin k) D
local instance indexFintype (F : Type*) [Field F] (k D : ℕ) : Fintype (GeneratorIndex F (Fin k) D) :=
  Fintype.ofFinite _

def fieldIndex (F : Type*) [Field F] (k D : ℕ) : GeneratorIndex ℚ (Fin k) D ≃ GeneratorIndex F (Fin k) D :=
  (indexEquiv ℚ (Fin k) D).symm.trans (indexEquiv F (Fin k) D)

theorem fieldIndex_self (k D : ℕ) : fieldIndex ℚ k D = Equiv.refl (GeneratorIndex ℚ (Fin k) D) := by
  apply Equiv.ext
  intro g
  exact (indexEquiv ℚ (Fin k) D).apply_symm_apply g

theorem fieldIndex_generator (F : Type*) [Field F] (k D : ℕ)
    (t : {e : Fin 3 →₀ ℕ // e.degree = D} ⊕ Fin k) :
    fieldIndex F k D (indexEquiv ℚ (Fin k) D t) = indexEquiv F (Fin k) D t := by
  exact congrArg (indexEquiv F (Fin k) D) ((indexEquiv ℚ (Fin k) D).symm_apply_apply t)

def integralGenerator (k D : ℕ) (c : Fin k → ℤ) (I J : Fin k → Finset ℤ)
    (g : GeneratorIndex ℚ (Fin k) D) : Source (List.finRange k) c I J :=
  match (indexEquiv ℚ (Fin k) D).symm g with
  | .inl e => (algebraMap ℤ[X][X] (Source (List.finRange k) c I J) (C X))^(e.val 1) *
      (algebraMap ℤ[X][X] (Source (List.finRange k) c I J) X)^(e.val 0)
  | .inr i => root ℤ[X][X] (equations (List.finRange k) c I J)
      ⟨i.val, by simpa only [equations, List.length_map, List.length_finRange] using i.isLt⟩

theorem integralGenerator_base (k D : ℕ) (c : Fin k → ℤ) (I J : Fin k → Finset ℤ)
    (e : {e : Fin 3 →₀ ℕ // e.degree = D}) :
    integralGenerator k D c I J (indexEquiv ℚ (Fin k) D (.inl e)) =
      (algebraMap ℤ[X][X] (Source (List.finRange k) c I J) (C X))^(e.val 1) *
      (algebraMap ℤ[X][X] (Source (List.finRange k) c I J) X)^(e.val 0) := by
  rw [integralGenerator, Equiv.symm_apply_apply]

theorem integralGenerator_radical (k D : ℕ) (c : Fin k → ℤ) (I J : Fin k → Finset ℤ) (i : Fin k) :
    integralGenerator k D c I J (indexEquiv ℚ (Fin k) D (.inr i)) =
      root ℤ[X][X] (equations (List.finRange k) c I J)
        ⟨i.val, by simpa only [equations, List.length_map, List.length_finRange] using i.isLt⟩ := by
  rw [integralGenerator, Equiv.symm_apply_apply]

theorem coefficientMap_X (F : Type*) [Field F] : coefficientMap F (X : ℤ[X][X]) = X := Polynomial.map_X _

theorem coefficientMap_C_X (F : Type*) [Field F] : coefficientMap F (C (X : ℤ[X])) = C (X : F[X]) := by
  change (C (X : ℤ[X])).map (Polynomial.mapRingHom (Int.castRingHom F)) = _
  rw [Polynomial.map_C]
  exact congrArg C (Polynomial.map_X (Int.castRingHom F))

theorem generator_compatibility {F : Type*} [Field F]
    (s : List (PaperP1.HomogeneousSplitRadicalData.PolynomialRing F))
    (c : Fin s.length → ℤ) (D : ℕ) (I J : Fin s.length → Finset ℤ)
    (hs : ∀ i, s.get i = PaperP1.HomogeneousSplitRadicalData.radicand (c i : F)
      (2*D-((I i).card+(J i).card)) (I i) (J i)) (g : GeneratorIndex ℚ (Fin s.length) D) :
    sourceMap F (List.finRange s.length) c I J (integralGenerator s.length D c I J g) =
      PaperP1.SourceAffineChartCoordinates.specialization s (fun i ↦ (c i : F)) D I J hs
        (sourceGenerator (fun i ↦ (c i : F)) D I J (fieldIndex F s.length D g) :
          PaperP1.HomogeneousSplitRadicalGrading.CoordinateRing (fun i ↦ (c i : F)) D I J) := by
  obtain ⟨t, rfl⟩ := (indexEquiv ℚ (Fin s.length) D).surjective g
  cases t with
  | inl e =>
    rw [fieldIndex_generator, integralGenerator_base]
    change sourceMap F (List.finRange s.length) c I J _ =
      PaperP1.SourceAffineChartCoordinates.specialization s (fun i ↦ (c i : F)) D I J hs
        (basePolynomialMap (fun i ↦ (c i : F)) D I J (MvPolynomial.monomial e.val 1))
    rw [map_mul, map_pow, map_pow, sourceMap_base, sourceMap_base, coefficientMap_C_X, coefficientMap_X,
      PaperP1.SourceAffineChartCoordinates.specialization_base, NativeAffineMonomialCoordinates.specialization_monomial]
    rw [map_mul, map_pow, map_pow]
  | inr i =>
    rw [fieldIndex_generator, integralGenerator_radical, sourceMap_root]
    change _ = PaperP1.SourceAffineChartCoordinates.specialization s (fun i ↦ (c i : F)) D I J hs
      (PaperP1.HomogeneousSplitRadicalFiniteVeronese.quotientMap (fun i ↦ (c i : F)) D I J (MvPolynomial.X (.inr i)))
    rw [PaperP1.SourceAffineChartCoordinates.specialization_radical]

def integralPrimitive (k D : ℕ) (c : Fin k → ℤ) (I J : Fin k → Finset ℤ)
    (u : GeneratorIndex ℚ (Fin k) D → ℕ) : Source (List.finRange k) c I J :=
  ∑ g, (u g : Source (List.finRange k) c I J) * integralGenerator k D c I J g

theorem primitive_expansion {F : Type*} [Field F] (k D : ℕ) (c : Fin k → F)
    (I J : Fin k → Finset ℤ) (u : GeneratorIndex F (Fin k) D → ℕ) :
    PaperP1.SourceSurfaceBoundedProjection.primitive c D I J u =
      ∑ g, (u g : PaperP1.HomogeneousSplitRadicalVeronese.veronese c D I J) * sourceGenerator c D I J g := by
  simp only [PaperP1.SourceSurfaceBoundedProjection.primitive, PaperP1.CommonLinearNormalization.form,
    map_sum, map_mul, MvPolynomial.aeval_X, map_natCast]

theorem primitive_compatibility {F : Type*} [Field F]
    (s : List (PaperP1.HomogeneousSplitRadicalData.PolynomialRing F))
    (c : Fin s.length → ℤ) (D : ℕ) (I J : Fin s.length → Finset ℤ)
    (hs : ∀ i, s.get i = PaperP1.HomogeneousSplitRadicalData.radicand (c i : F)
      (2*D-((I i).card+(J i).card)) (I i) (J i))
    (u : GeneratorIndex ℚ (Fin s.length) D → ℕ) :
    sourceMap F (List.finRange s.length) c I J (integralPrimitive s.length D c I J u) =
      PaperP1.SourceAffineChartCoordinates.specialization s (fun i ↦ (c i : F)) D I J hs
        (PaperP1.SourceSurfaceBoundedProjection.primitive (fun i ↦ (c i : F)) D I J
          (fun g ↦ u ((fieldIndex F s.length D).symm g)) :
            PaperP1.HomogeneousSplitRadicalGrading.CoordinateRing (fun i ↦ (c i : F)) D I J) := by
  let Φ := (PaperP1.SourceAffineChartCoordinates.specialization s (fun i ↦ (c i : F)) D I J hs).comp
    (PaperP1.HomogeneousSplitRadicalVeronese.veronese (fun i ↦ (c i : F)) D I J).val.toRingHom
  change sourceMap F (List.finRange s.length) c I J (integralPrimitive s.length D c I J u) =
    Φ (PaperP1.SourceSurfaceBoundedProjection.primitive (fun i ↦ (c i : F)) D I J
      (fun g ↦ u ((fieldIndex F s.length D).symm g)))
  have hΦsum : Φ (∑ g : GeneratorIndex F (Fin s.length) D,
      (u ((fieldIndex F s.length D).symm g) : PaperP1.HomogeneousSplitRadicalVeronese.veronese (fun i ↦ (c i : F)) D I J) *
        sourceGenerator (fun i ↦ (c i : F)) D I J g) =
      ∑ g : GeneratorIndex F (Fin s.length) D, Φ
        ((u ((fieldIndex F s.length D).symm g) : PaperP1.HomogeneousSplitRadicalVeronese.veronese (fun i ↦ (c i : F)) D I J) *
          sourceGenerator (fun i ↦ (c i : F)) D I J g) := by
    exact map_sum Φ.toAddMonoidHom _ _
  rw [integralPrimitive, map_sum (sourceMap F (List.finRange s.length) c I J), primitive_expansion, hΦsum]
  simp only [map_mul, map_natCast]
  apply Fintype.sum_equiv (fieldIndex F s.length D)
  intro g
  rw [Equiv.symm_apply_apply]
  change (u g : PaperP1.SplitRadicalCoordinateAlgebra.CoordinateAlgebra (List.finRange s.length)
      (fun i ↦ (c i : F)) I J) * sourceMap F (List.finRange s.length) c I J (integralGenerator s.length D c I J g) =
    (u g : PaperP1.SplitRadicalCoordinateAlgebra.CoordinateAlgebra (List.finRange s.length)
      (fun i ↦ (c i : F)) I J) *
      PaperP1.SourceAffineChartCoordinates.specialization s (fun i ↦ (c i : F)) D I J hs
        (sourceGenerator (fun i ↦ (c i : F)) D I J (fieldIndex F s.length D g))
  rw [generator_compatibility s c D I J hs g]

def integralParameters (k D : ℕ) (c : Fin k → ℤ) (I J : Fin k → Finset ℤ) :
    Fin 3 → Source (List.finRange k) c I J :=
  ![(algebraMap ℤ[X][X] (Source (List.finRange k) c I J) X)^D,
    (algebraMap ℤ[X][X] (Source (List.finRange k) c I J) (C X))^D, 1]

theorem parameter_compatibility {F : Type*} [Field F]
    (s : List (PaperP1.HomogeneousSplitRadicalData.PolynomialRing F))
    (c : Fin s.length → ℤ) (D : ℕ) (hD : 0 < D) (I J : Fin s.length → Finset ℤ)
    (hs : ∀ i, s.get i = PaperP1.HomogeneousSplitRadicalData.radicand (c i : F)
      (2*D-((I i).card+(J i).card)) (I i) (J i)) (j : Fin 3) :
    sourceMap F (List.finRange s.length) c I J (integralParameters s.length D c I J j) =
      PaperP1.SourceAffineChartCoordinates.specialization s (fun i ↦ (c i : F)) D I J hs
        (PaperP1.SourceSurfacePowerParameters.parameters s (fun i ↦ (c i : F)) D hD I J hs j :
          PaperP1.HomogeneousSplitRadicalGrading.CoordinateRing (fun i ↦ (c i : F)) D I J) := by
  change sourceMap F (List.finRange s.length) c I J (integralParameters s.length D c I J j) =
    PaperP1.SourceAffineChartCoordinates.specialization s (fun i ↦ (c i : F)) D I J hs
      (basePolynomialMap (fun i ↦ (c i : F)) D I J
        ((PaperP1.StandardVeroneseCoordinates.coordinatePower F D j) : MvPolynomial (Fin 3) F))
  rw [PaperP1.SourceAffineChartCoordinates.specialization_base,
    PaperP1.StandardVeroneseCoordinates.coordinatePower_val, map_pow, NativeAffineMonomialCoordinates.specialization_X]
  fin_cases j
  · change sourceMap F (List.finRange s.length) c I J
      ((algebraMap ℤ[X][X] (Source (List.finRange s.length) c I J) X)^D) =
      algebraMap F[X][X] (PaperP1.SplitRadicalCoordinateAlgebra.CoordinateAlgebra (List.finRange s.length) (fun i ↦ (c i : F)) I J) (X^D)
    rw [map_pow, sourceMap_base, coefficientMap_X, map_pow]
  · change sourceMap F (List.finRange s.length) c I J
      ((algebraMap ℤ[X][X] (Source (List.finRange s.length) c I J) (C X))^D) =
      algebraMap F[X][X] (PaperP1.SplitRadicalCoordinateAlgebra.CoordinateAlgebra (List.finRange s.length) (fun i ↦ (c i : F)) I J) ((C X)^D)
    rw [map_pow, sourceMap_base, coefficientMap_C_X, map_pow]
  · change sourceMap F (List.finRange s.length) c I J 1 =
      algebraMap F[X][X] (PaperP1.SplitRadicalCoordinateAlgebra.CoordinateAlgebra (List.finRange s.length) (fun i ↦ (c i : F)) I J) (1^D)
    rw [map_one, one_pow, map_one]

def integralCoordinates (k D : ℕ) (c : Fin k → ℤ) (I J : Fin k → Finset ℤ)
    (u : GeneratorIndex ℚ (Fin k) D → ℕ) : Fin 4 → Source (List.finRange k) c I J :=
  Fin.cons (integralPrimitive k D c I J u) (integralParameters k D c I J)

theorem coordinates_compatibility {F : Type*} [Field F]
    (s : List (PaperP1.HomogeneousSplitRadicalData.PolynomialRing F))
    (c : Fin s.length → ℤ) (D : ℕ) (hD : 0 < D) (I J : Fin s.length → Finset ℤ)
    (hs : ∀ i, s.get i = PaperP1.HomogeneousSplitRadicalData.radicand (c i : F)
      (2*D-((I i).card+(J i).card)) (I i) (J i))
    (u : GeneratorIndex ℚ (Fin s.length) D → ℕ) (i : Fin 4) :
    sourceMap F (List.finRange s.length) c I J (integralCoordinates s.length D c I J u i) =
      PaperP1.SourceAffineChartCoordinates.specialization s (fun i ↦ (c i : F)) D I J hs
        (PaperP1.LinearHypersurfaceImage.coordinates
          (A := PaperP1.HomogeneousSplitRadicalVeronese.veronese (fun i ↦ (c i : F)) D I J)
          (PaperP1.SourceSurfacePowerParameters.parameters s (fun i ↦ (c i : F)) D hD I J hs)
          (PaperP1.SourceSurfaceBoundedProjection.primitive (fun i ↦ (c i : F)) D I J
            (fun g ↦ u ((fieldIndex F s.length D).symm g))) i :
            PaperP1.HomogeneousSplitRadicalGrading.CoordinateRing (fun i ↦ (c i : F)) D I J) := by
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · exact primitive_compatibility s c D I J hs u
  · exact parameter_compatibility s c D hD I J hs j

end PaperP1.IntegralSourceProjectionCoordinates
