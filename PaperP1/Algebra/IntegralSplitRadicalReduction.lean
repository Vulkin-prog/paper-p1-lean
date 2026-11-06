module

public import PaperP1.Algebra.IntegralSplitRadicalModel
public import PaperP1.Algebra.QuadraticTowerQuotient
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.Algebra.Field.ZMod

/-! # Faithful rational source specialization and exact literal source reduction modulo p

The reduction kernel is exactly (p). Every integral source relation detected
by the faithful rational source already holds integrally and in every field.
-/

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.IntegralSplitRadicalReduction
open Polynomial Finset FiniteQuadraticTower IntegralSplitRadicalModel
open scoped Classical

theorem coefficientMap_injective (F : Type*) [Field F] [CharZero F] :
    Function.Injective (coefficientMap F) :=
  Polynomial.map_injective (Polynomial.mapRingHom (Int.castRingHom F))
    (Polynomial.map_injective (Int.castRingHom F) Int.cast_injective)

theorem sourceMap_injective {ι : Type*} (F : Type*) [Field F] [CharZero F]
    (l : List ι) (c : ι → ℤ) (I J : ι → Finset ℤ) : Function.Injective (sourceMap F l c I J) :=
  (PaperP1.QuadraticTowerListCongr.congr F[X][X] (equations_map F l c I J)).injective.comp
    (PaperP1.QuadraticTowerBaseChange.map_injective (coefficientMap F) (coefficientMap_injective F) _)

theorem coefficientMap_surjective_zmod (p : ℕ) [Fact p.Prime] :
    Function.Surjective (coefficientMap (ZMod p)) :=
  Polynomial.map_surjective (Polynomial.mapRingHom (Int.castRingHom (ZMod p)))
    (Polynomial.map_surjective (Int.castRingHom (ZMod p)) ZMod.intCast_surjective)

theorem sourceMap_surjective_zmod {ι : Type*} (p : ℕ) [Fact p.Prime]
    (l : List ι) (c : ι → ℤ) (I J : ι → Finset ℤ) : Function.Surjective (sourceMap (ZMod p) l c I J) :=
  (PaperP1.QuadraticTowerListCongr.congr (ZMod p)[X][X] (equations_map (ZMod p) l c I J)).surjective.comp
    (PaperP1.QuadraticTowerQuotient.map_surjective (coefficientMap (ZMod p)) (coefficientMap_surjective_zmod p) _)

theorem coefficient_kernel_zmod (p : ℕ) [Fact p.Prime] :
    RingHom.ker (coefficientMap (ZMod p)) = Ideal.span {(p : ℤ[X][X])} := by
  have hker : RingHom.ker (Int.castRingHom (ZMod p)) = Ideal.span {(p : ℤ)} := by
    ext a
    change (a : ZMod p) = 0 ↔ a ∈ Ideal.span {(p : ℤ)}
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd, Ideal.mem_span_singleton]
  rw [coefficientMap, Polynomial.ker_mapRingHom, Polynomial.ker_mapRingHom, hker,
    Ideal.map_span, Ideal.map_span]
  simp only [Set.image_singleton, map_natCast]

theorem sourceMap_kernel {ι : Type*} (F : Type*) [Field F]
    (l : List ι) (c : ι → ℤ) (I J : ι → Finset ℤ) :
    RingHom.ker (sourceMap F l c I J) =
      (RingHom.ker (coefficientMap F)).map (algebraMap ℤ[X][X] (Source l c I J)) := by
  rw [← PaperP1.QuadraticTowerQuotient.map_ker (coefficientMap F) (equations l c I J)]
  ext a
  change sourceMap F l c I J a = 0 ↔
    (PaperP1.QuadraticTowerBaseChange.mapData (coefficientMap F) (equations l c I J)).hom a = 0
  exact map_eq_zero_iff
    (PaperP1.QuadraticTowerListCongr.congr F[X][X] (equations_map F l c I J)).toRingHom
    (PaperP1.QuadraticTowerListCongr.congr F[X][X] (equations_map F l c I J)).injective

theorem sourceMap_kernel_zmod {ι : Type*} (p : ℕ) [Fact p.Prime]
    (l : List ι) (c : ι → ℤ) (I J : ι → Finset ℤ) :
    RingHom.ker (sourceMap (ZMod p) l c I J) = Ideal.span {(p : Source l c I J)} := by
  rw [sourceMap_kernel, coefficient_kernel_zmod, Ideal.map_span]
  simp only [Set.image_singleton, map_natCast]

def reductionEquiv {ι : Type*} (p : ℕ) [Fact p.Prime]
    (l : List ι) (c : ι → ℤ) (I J : ι → Finset ℤ) :
    (Source l c I J) ⧸ Ideal.span {(p : Source l c I J)} ≃+*
      PaperP1.SplitRadicalCoordinateAlgebra.CoordinateAlgebra l (fun i ↦ (c i : ZMod p)) I J :=
  (Ideal.quotEquivOfEq (sourceMap_kernel_zmod p l c I J).symm).trans
    ((sourceMap (ZMod p) l c I J).quotientKerEquivOfSurjective (sourceMap_surjective_zmod p l c I J))

theorem reductionEquiv_mk {ι : Type*} (p : ℕ) [Fact p.Prime]
    (l : List ι) (c : ι → ℤ) (I J : ι → Finset ℤ) (a : Source l c I J) :
    reductionEquiv p l c I J (Ideal.Quotient.mk _ a) = sourceMap (ZMod p) l c I J a := by
  rw [reductionEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]

theorem relation_reduces {ι : Type*} (l : List ι) (c : ι → ℤ) (I J : ι → Finset ℤ)
    (a : Source l c I J) (ha : sourceMap ℚ l c I J a = 0) (F : Type*) [Field F] :
    sourceMap F l c I J a = 0 := by
  have hz : a = 0 := (sourceMap_injective ℚ l c I J) (ha.trans (map_zero _).symm)
  rw [hz, map_zero]

end PaperP1.IntegralSplitRadicalReduction
