module

public import PaperP1.Arithmetic.ScaledCurveSquareMatching
public import PaperP1.Algebra.SquareClassKernelDegree
public import PaperP1.Coding.BinaryFormSeparation
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # The actual equation square-class kernel loses only logarithmically many coordinate labels -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ScaledCurveEquationClasses

open Polynomial Finset PaperP1.BivariateDegrees PaperP1.CurveFunctionField
  PaperP1.FormalWordPolynomials PaperP1.ScaledCurveSquareMatching

variable {ι : Type*}

theorem linear_biUnion (A : Finset ι) (I : ι → Finset ℤ) (hI : (A : Set ι).PairwiseDisjoint I) :
    linearOver ℤ (A.biUnion I) = ∏ ν ∈ A, linearOver ℤ (I ν) := Finset.prod_biUnion hI

theorem word_biUnion (A : Finset ι) (I J : ι → Finset ℤ)
    (hI : (A : Set ι).PairwiseDisjoint I) (hJ : (A : Set ι).PairwiseDisjoint J) :
    wordOver ℤ (A.biUnion I) (A.biUnion J) = ∏ ν ∈ A, wordOver ℤ (I ν) (J ν) := by
  rw [wordOver, linear_biUnion A I hI, linear_biUnion A J hJ]
  simp only [map_prod, Polynomial.map_prod, wordOver, Finset.prod_mul_distrib]

theorem scaled_product (A : Finset ι) (d : ι → ℤ) (I J : ι → Finset ℤ)
    (hI : (A : Set ι).PairwiseDisjoint I) (hJ : (A : Set ι).PairwiseDisjoint J) :
    (∏ ν ∈ A, word (d ν) (I ν) (J ν)) = word (∏ ν ∈ A, d ν) (A.biUnion I) (A.biUnion J) := by
  change (∏ ν ∈ A, (d ν : ℤ[X][X]) * wordOver ℤ (I ν) (J ν)) =
    ((∏ ν ∈ A, d ν : ℤ) : ℤ[X][X]) * wordOver ℤ (A.biUnion I) (A.biUnion J)
  rw [Finset.prod_mul_distrib, word_biUnion A I J hI hJ]
  congr 1
  exact (map_prod (Int.castRingHom ℤ[X][X]) (fun ν ↦ d ν) A).symm

variable [Fintype ι] (C₀ : ℤ[X][X]) [Fact (Irreducible C₀)]
  (hx : 0 < degreeX C₀) (hy : 0 < degreeY C₀) (d : ι → ℤ) (hd : ∀ ν, d ν ≠ 0)
  (I J : ι → Finset ℤ)

def value (ν : ι) : FunctionField C₀ := specialize C₀ (word (d ν) (I ν) (J ν))

include hx hy hd in
omit [Fintype ι] in
theorem value_ne_zero (ν : ι) : value C₀ d I J ν ≠ 0 := by
  let : CharZero (FunctionField C₀) := functionField_charZero C₀ hy
  change specialize C₀ ((d ν : ℤ[X][X]) * wordOver ℤ (I ν) (J ν)) ≠ 0
  rw [map_mul, map_intCast]
  exact mul_ne_zero (Int.cast_ne_zero.mpr (hd ν)) (word_ne_zero C₀ hx hy (I ν) (J ν))

def squareClass (ν : ι) : FieldSquareClasses.Classes (FunctionField C₀) :=
  FieldSquareClasses.ofNonzero (value C₀ d I J ν) (value_ne_zero C₀ hx hy d hd I J ν)

def classMap : (ι → ZMod 2) →ₗ[ZMod 2] FieldSquareClasses.Classes (FunctionField C₀) :=
  Fintype.linearCombination (ZMod 2) (squareClass C₀ hx hy d hd I J)

def selected (w : ι → ZMod 2) : Finset ι := by
  classical
  exact univ.filter fun ν ↦ w ν ≠ 0

theorem classMap_selected (w : ι → ZMod 2) :
    classMap C₀ hx hy d hd I J w = ∑ ν ∈ selected w, squareClass C₀ hx hy d hd I J ν := by
  classical
  simp only [classMap, Fintype.linearCombination_apply, selected, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro ν _
  have hbit : w ν = 0 ∨ w ν = 1 := by generalize w ν = z; revert z; decide
  rcases hbit with hz | ho
  · simp only [hz, ne_eq, not_true_eq_false, ite_false, zero_smul]
  · simp only [ho, one_smul]
    norm_num

include hx hy hd in
theorem kernel_literal_square (w : ι → ZMod 2) (hw : w ∈ LinearMap.ker (classMap C₀ hx hy d hd I J))
    (hI : Pairwise fun ν μ ↦ Disjoint (I ν) (I μ)) (hJ : Pairwise fun ν μ ↦ Disjoint (J ν) (J μ)) :
    IsSquare (specialize C₀ (word (∏ ν ∈ selected w, d ν) ((selected w).biUnion I) ((selected w).biUnion J))) := by
  classical
  have hsum := (classMap_selected C₀ hx hy d hd I J w).symm.trans (LinearMap.mem_ker.mp hw)
  have hsquare : IsSquare (∏ ν ∈ selected w, value C₀ d I J ν) :=
    (FieldSquareClasses.ofNonzero_zero_iff _ _).mp
      ((FieldSquareClasses.ofNonzero_prod (selected w) (value C₀ d I J)
        (value_ne_zero C₀ hx hy d hd I J)).trans hsum)
  have heq : (∏ ν ∈ selected w, value C₀ d I J ν) =
      specialize C₀ (word (∏ ν ∈ selected w, d ν) ((selected w).biUnion I) ((selected w).biUnion J)) := by
    simp only [value, ← map_prod, scaled_product _ d I J (fun _ _ _ _ h ↦ hI h) (fun _ _ _ _ h ↦ hJ h)]
  exact heq ▸ hsquare

variable {E : Type*} [Field E] [Algebra (FunctionField C₀) E]

theorem range_le_kernel (r : ι → E) (hr : ∀ ν, r ν ^ 2 = algebraMap (FunctionField C₀) E (value C₀ d I J ν)) :
    LinearMap.range (classMap C₀ hx hy d hd I J) ≤
      LinearMap.ker (FieldSquareClassMap.map (algebraMap (FunctionField C₀) E)) := by
  have hkill (ν) : FieldSquareClassMap.map (algebraMap (FunctionField C₀) E)
      (squareClass C₀ hx hy d hd I J ν) = 0 := by
    rw [squareClass, FieldSquareClassMap.map_ofNonzero]
    exact (FieldSquareClasses.ofNonzero_zero_iff _ _).mpr ⟨r ν, by simpa only [pow_two] using (hr ν).symm⟩
  rintro z ⟨w, rfl⟩
  rw [LinearMap.mem_ker]
  simp only [classMap, Fintype.linearCombination_apply, map_sum, map_smul, hkill, smul_zero, Finset.sum_const_zero]

theorem image_rank_le_log [Module.Finite (FunctionField C₀) E]
    (r : ι → E) (hr : ∀ ν, r ν ^ 2 = algebraMap (FunctionField C₀) E (value C₀ d I J ν)) :
    Module.finrank (ZMod 2) (LinearMap.range (classMap C₀ hx hy d hd I J)) ≤
      Nat.log 2 (Module.finrank (FunctionField C₀) E) := by
  let : CharZero (FunctionField C₀) := functionField_charZero C₀ hy
  let : Module.Finite (ZMod 2) (LinearMap.ker (FieldSquareClassMap.map (algebraMap (FunctionField C₀) E))) :=
    SquareClassKernelDegree.kernel_finite
  exact (Submodule.finrank_mono (range_le_kernel C₀ hx hy d hd I J r hr)).trans SquareClassKernelDegree.kernel_finrank_le_log

theorem bad_card_le_twice_log [DecidableEq ι] [Module.Finite (FunctionField C₀) E]
    (r : ι → E) (hr : ∀ ν, r ν ^ 2 = algebraMap (FunctionField C₀) E (value C₀ d I J ν)) :
    (UniqueCoordinateBudget.bad (LinearMap.ker (classMap C₀ hx hy d hd I J))).card ≤
      2 * Nat.log 2 (Module.finrank (FunctionField C₀) E) := by
  have hcost := UniqueCoordinateBudget.bad_card_le_twice_codim (LinearMap.ker (classMap C₀ hx hy d hd I J))
  have hdim := (classMap C₀ hx hy d hd I J).finrank_range_add_finrank_ker
  rw [Module.finrank_fintype_fun_eq_card] at hdim
  have hlog := image_rank_le_log C₀ hx hy d hd I J r hr
  omega

end PaperP1.ScaledCurveEquationClasses
