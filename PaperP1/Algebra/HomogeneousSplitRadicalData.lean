module

public import PaperP1.Algebra.FiniteRootWordField
public import PaperP1.Algebra.QuadraticTowerBaseChange

/-! # The literal homogenized split radicands and their faithful generic coefficient map -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HomogeneousSplitRadicalData

open Finset Polynomial

abbrev CoefficientField (F : Type*) [Field F] := FractionRing F[X]
abbrev PolynomialRing (F : Type*) [Field F] := F[X][X][X]

local instance coefficientRing (F : Type*) [Field F] : CommRing (CoefficientField F) :=
  (inferInstance : Field (CoefficientField F)).toCommRing

local instance sourceRing (F : Type*) [Field F] : CommRing (PolynomialRing F) := inferInstance
local instance targetRing (F : Type*) [Field F] : CommRing (CoefficientField F)[X][X] := inferInstance

def z (F : Type*) [Field F] : CoefficientField F := algebraMap F[X] (CoefficientField F) X

def scalar {F : Type*} [Field F] (c : F) (e : ℕ) : CoefficientField F :=
  algebraMap F[X] (CoefficientField F) (C c) * z F ^ e

def roots (F : Type*) [Field F] (I : Finset ℤ) : Finset (CoefficientField F) := by
  classical
  exact I.image fun i : ℤ ↦ (i : CoefficientField F) * z F

def linear (F : Type*) [Field F] (I : Finset ℤ) : F[X][X] :=
  ∏ i ∈ I, (X + C ((i : F[X]) * (X : F[X])))

def word (F : Type*) [Field F] (I J : Finset ℤ) : PolynomialRing F :=
  C (linear F I) * (linear F J).map C

def radicand {F : Type*} [Field F] (c : F) (e : ℕ) (I J : Finset ℤ) : PolynomialRing F :=
  C (C (C c * (X : F[X]) ^ e)) * word F I J

def baseMap (F : Type*) [Field F] : PolynomialRing F →+* (CoefficientField F)[X][X] :=
  Polynomial.mapRingHom (Polynomial.mapRingHom (algebraMap F[X] (CoefficientField F)))

theorem z_ne_zero (F : Type*) [Field F] : z F ≠ 0 := by
  intro hz
  exact Polynomial.X_ne_zero (IsFractionRing.injective F[X] (CoefficientField F) (hz.trans (map_zero _).symm))

theorem scalar_ne_zero {F : Type*} [Field F] (c : F) (hc : c ≠ 0) (e : ℕ) : scalar c e ≠ 0 := by
  apply mul_ne_zero
  · intro hh
    exact C_ne_zero.mpr hc (IsFractionRing.injective F[X] (CoefficientField F) (hh.trans (map_zero _).symm))
  · exact pow_ne_zero _ (z_ne_zero F)

theorem root_injective (F : Type*) [Field F] [CharZero F] :
    Function.Injective (fun i : ℤ ↦ (i : CoefficientField F) * z F) := by
  intro i j hij
  exact Int.cast_injective (mul_right_cancel₀ (z_ne_zero F) hij)

theorem roots_nonempty (F : Type*) [Field F] (I : Finset ℤ) (hI : I.Nonempty) : (roots F I).Nonempty := by
  classical
  obtain ⟨i, hi⟩ := hI
  exact ⟨(i : CoefficientField F) * z F, mem_image.mpr ⟨i, hi, rfl⟩⟩

theorem roots_disjoint (F : Type*) [Field F] [CharZero F] (I J : Finset ℤ) (hIJ : Disjoint I J) :
    Disjoint (roots F I) (roots F J) := by
  classical
  apply disjoint_left.mpr
  intro a haI haJ
  obtain ⟨i, hi, hia⟩ := mem_image.mp haI
  obtain ⟨j, hj, hja⟩ := mem_image.mp haJ
  have hij := root_injective F (hia.trans hja.symm)
  exact disjoint_left.mp hIJ hi (hij ▸ hj)

theorem baseMap_injective (F : Type*) [Field F] : Function.Injective (baseMap F) :=
  Polynomial.map_injective _ (Polynomial.map_injective _ (IsFractionRing.injective F[X] (CoefficientField F)))

theorem linear_map (F : Type*) [Field F] [CharZero F] (I : Finset ℤ) :
    (linear F I).map (algebraMap F[X] (CoefficientField F)) = FiniteRootWordSquares.linear (roots F I) := by
  classical
  rw [FiniteRootWordSquares.linear, roots, prod_image (root_injective F).injOn]
  simp only [linear, Polynomial.map_prod, Polynomial.map_add, Polynomial.map_X, Polynomial.map_C]
  simp only [map_mul, map_intCast, z]

theorem word_map (F : Type*) [Field F] [CharZero F] (I J : Finset ℤ) :
    baseMap F (word F I J) = FiniteRootWordSquares.word (roots F I) (roots F J) := by
  change (word F I J).map (Polynomial.mapRingHom (algebraMap F[X] (CoefficientField F))) = _
  rw [word, Polynomial.map_mul, Polynomial.map_C]
  change C ((linear F I).map (algebraMap F[X] (CoefficientField F))) *
    ((linear F J).map C).map (Polynomial.mapRingHom (algebraMap F[X] (CoefficientField F))) = _
  rw [linear_map, Polynomial.map_map]
  have he : (Polynomial.mapRingHom (algebraMap F[X] (CoefficientField F))).comp (C (R := F[X])) =
      (C (R := CoefficientField F)).comp (algebraMap F[X] (CoefficientField F)) := by
    apply RingHom.ext
    intro p
    change (C p).map (algebraMap F[X] (CoefficientField F)) = C (algebraMap F[X] (CoefficientField F) p)
    rw [Polynomial.map_C]
  rw [he, ← Polynomial.map_map, linear_map]
  rfl

theorem radicand_map {F : Type*} [Field F] [CharZero F] (c : F) (e : ℕ) (I J : Finset ℤ) :
    baseMap F (radicand c e I J) =
      FiniteRootWordSquares.scaledPolynomial (scalar c e) (roots F I) (roots F J) := by
  change (C (C (C c * (X : F[X]) ^ e)) * word F I J).map
    (Polynomial.mapRingHom (algebraMap F[X] (CoefficientField F))) = _
  rw [Polynomial.map_mul, Polynomial.map_C]
  change C ((C (C c * (X : F[X]) ^ e)).map (algebraMap F[X] (CoefficientField F))) * baseMap F (word F I J) = _
  rw [Polynomial.map_C, word_map]
  simp only [map_mul, map_pow, scalar, z, FiniteRootWordSquares.scaledPolynomial]

end PaperP1.HomogeneousSplitRadicalData
