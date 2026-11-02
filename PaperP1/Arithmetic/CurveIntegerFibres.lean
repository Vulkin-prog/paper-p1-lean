module

public import PaperP1.Arithmetic.CurveSquareMatching
public import PaperP1.Algebra.BivariateLargeRoot
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.Data.Int.Interval

/-! # Actual integer grid fibres forced by the functional-square matching theorem -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CurveIntegerFibres

open Polynomial Finset PaperP1.BivariateDegrees PaperP1.CurveCriticalFibres PaperP1.CurveFibreRegularity
  PaperP1.CurveFunctionField PaperP1.FormalWordPolynomials

local instance : CommRing ℤ[X][X] := inferInstance

def offsetBox (B : ℕ) : Finset ℤ := Finset.Icc (-(B : ℤ)) B

def integerFibre (P : ℤ[X][X]) (B : ℕ) (u : ℤ) : Finset ℤ :=
  (offsetBox B).filter (fun v ↦ P.evalEval (-u) (-v) = 0)

def integerGrid (P : ℤ[X][X]) (B : ℕ) : Finset (ℤ × ℤ) :=
  ((offsetBox B) ×ˢ (offsetBox B)).filter (fun p ↦ P.evalEval (-p.1) (-p.2) = 0)

theorem mem_offsetBox (B : ℕ) (u : ℤ) : u ∈ offsetBox B ↔ |u| ≤ (B : ℤ) := by
  rw [offsetBox, mem_Icc, abs_le]

theorem mem_integerFibre (P : ℤ[X][X]) (B : ℕ) (u v : ℤ) :
    v ∈ integerFibre P B u ↔ |v| ≤ (B : ℤ) ∧ P.evalEval (-u) (-v) = 0 := by
  simp only [integerFibre, mem_filter, mem_offsetBox]

theorem mem_integerGrid (P : ℤ[X][X]) (B : ℕ) (p : ℤ × ℤ) :
    p ∈ integerGrid P B ↔ |p.1| ≤ (B : ℤ) ∧ |p.2| ≤ (B : ℤ) ∧ P.evalEval (-p.1) (-p.2) = 0 := by
  simp only [integerGrid, mem_filter, Finset.mem_product, mem_offsetBox, and_assoc]

theorem grid_card_eq_sum_fibres (P : ℤ[X][X]) (B : ℕ) :
    (integerGrid P B).card = ∑ u ∈ offsetBox B, (integerFibre P B u).card := by
  simp only [integerGrid, integerFibre, card_eq_sum_ones, sum_filter, Finset.sum_product]

theorem grid_card_swap (P : ℤ[X][X]) (B : ℕ) :
    (integerGrid (Bivariate.swap P) B).card = (integerGrid P B).card := by
  simp only [integerGrid, card_eq_sum_ones, sum_filter, Finset.sum_product, BivariateLargeRoot.eval_swap]
  exact Finset.sum_comm

theorem degree_le_fibre (C₀ : ℤ[X][X]) [hC : Fact (Irreducible C₀)] (hy : 0 < degreeY C₀)
    (I J : Finset ℤ) (hsquare : IsSquare (specialize C₀ (wordOver ℤ I J)))
    (B : ℕ) (hJ : ∀ v ∈ J, |v| ≤ (B : ℤ)) (u : ℤ) (hu : u ∈ I) (hregular : u ∉ badOffsets C₀) :
    degreeY C₀ ≤ (integerFibre C₀ B u).card := by
  classical
  let roots : Finset ℂ := (fibre (K := ℂ) C₀ u).roots.toFinset
  have hsubset : roots ⊆ (integerFibre C₀ B u).image (fun v : ℤ ↦ -(v : ℂ)) := by
    intro z hz
    have hr : (fibre (K := ℂ) C₀ u).eval z = 0 :=
      (Polynomial.mem_roots (fibre_nonzero (K := ℂ) C₀ hC.out hy u hregular)).mp (Multiset.mem_toFinset.mp hz)
    obtain ⟨v, hv, he⟩ := CurveSquareMatching.root_matches_offset C₀ hy I J hsquare u hu hregular z hr
    have hzv : (fibre (K := ℂ) C₀ u).eval (-(v : ℂ)) = 0 := by simpa only [he] using hr
    have hcast : ((C₀.evalEval (-u) (-v) : ℤ) : ℂ) = 0 :=
      (fibre_integer_evaluation (K := ℂ) C₀ u v).symm.trans hzv
    have hpoint : C₀.evalEval (-u) (-v) = 0 := by exact_mod_cast hcast
    exact mem_image.mpr ⟨v, (mem_integerFibre C₀ B u v).mpr ⟨hJ v hv, hpoint⟩, he.symm⟩
  have hcard : roots.card ≤ (integerFibre C₀ B u).card := (card_le_card hsubset).trans card_image_le
  have hr : roots.card = degreeY C₀ := fibre_roots_card (K := ℂ) C₀ hC.out hy u hregular
  rwa [hr] at hcard

theorem mul_card_le_grid (P : ℤ[X][X]) (B : ℕ) (U : Finset ℤ) (d : ℕ)
    (hU : U ⊆ offsetBox B) (hfibre : ∀ u ∈ U, d ≤ (integerFibre P B u).card) :
    d * U.card ≤ (integerGrid P B).card := by
  calc
    _ = ∑ _u ∈ U, d := by simp only [sum_const, nsmul_eq_mul, Nat.cast_id]; exact Nat.mul_comm _ _
    _ ≤ ∑ u ∈ U, (integerFibre P B u).card := sum_le_sum hfibre
    _ ≤ ∑ u ∈ offsetBox B, (integerFibre P B u).card := sum_le_sum_of_subset_of_nonneg hU (fun _ _ _ ↦ Nat.zero_le _)
    _ = _ := (grid_card_eq_sum_fibres P B).symm

end PaperP1.CurveIntegerFibres
