module

public import PaperP1.Algebra.RadicalProjectionPolynomialBaseChange
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Data.List.OfFn

/-! # One fixed integer polynomial specializes to every independent radical-sum equation -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UniversalRadicalProjection

open Polynomial PaperP1.FiniteQuadraticTower PaperP1.FiniteRadicalProjection
  PaperP1.RadicalProjectionPolynomial

abbrev ParameterRing (k : ℕ) := MvPolynomial (Fin k) ℤ

def universalRadicands (k : ℕ) : List (ParameterRing k) := List.ofFn (fun i : Fin k ↦ MvPolynomial.X i)

def universalEquation (k : ℕ) : (ParameterRing k)[X] := equation (ParameterRing k) (universalRadicands k)

def universalPolynomial (k : ℕ) : MvPolynomial (Option (Fin k)) ℤ :=
  (MvPolynomial.optionEquivLeft ℤ (Fin k)).symm (universalEquation k)

def degreeConstant (k : ℕ) : ℕ := (universalPolynomial k).totalDegree

def specialization (S : Type*) [CommRing S] (s : List S) : ParameterRing s.length →+* S :=
  MvPolynomial.eval₂Hom (Int.castRingHom S) (fun i ↦ s.get i)

theorem universal_monic (k : ℕ) : (universalEquation k).Monic := equation_monic _ _

theorem universal_degree_upper (k : ℕ) : (universalEquation k).natDegree ≤ 2 ^ k := by
  have hh := minpoly.natDegree_le (A := ParameterRing k) (radicalSum (ParameterRing k) (universalRadicands k))
  rw [FiniteQuadraticTower.finrank] at hh
  simpa only [universalEquation, equation, universalRadicands, List.length_ofFn] using hh

theorem specialization_X (S : Type*) [CommRing S] (s : List S) (i : Fin s.length) :
    specialization S s (MvPolynomial.X i) = s.get i := MvPolynomial.eval₂Hom_X' _ _ i

theorem universalRadicands_map (S : Type*) [CommRing S] (s : List S) :
    (universalRadicands s.length).map (specialization S s) = s := by
  simp only [universalRadicands, List.map_ofFn, Function.comp_def, specialization_X]
  exact List.ofFn_get s

theorem equation_specializes (S K : Type*) [CommRing S] [IsDomain S] [Field K] [CharZero K]
    [Algebra S K] [IsFractionRing S K] (s : List S)
    (hs : IndependentQuadraticTower.Independent (s.map (algebraMap S K))) :
    (universalEquation s.length).map (specialization S s) = equation S s := by
  have hs' : IndependentQuadraticTower.Independent
      (((universalRadicands s.length).map (specialization S s)).map (algebraMap S K)) := by
    rw [universalRadicands_map]
    exact hs
  have hh := RadicalProjectionPolynomialBaseChange.map_equation (ParameterRing s.length) S K
    (specialization S s) (universalRadicands s.length) hs'
  simpa only [universalEquation, universalRadicands_map] using hh

end PaperP1.UniversalRadicalProjection
