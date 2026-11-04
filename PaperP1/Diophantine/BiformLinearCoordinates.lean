module

public import PaperP1.Algebra.BinarySubstitutionHeight
public import PaperP1.Arithmetic.BiformCoefficientRecovery

/-! # Exact simultaneous coordinate changes on both projective pairs -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BiformLinearCoordinates

open Finset MvPolynomial PaperP1.HomogeneousCharts PaperP1.BihomogeneousSwap
open PaperP1.BinaryLinearSubstitution PaperP1.BinarySubstitutionHeight
open PaperP1.BivariateDegrees PaperP1.PolynomialHeightArithmetic

variable {a b : ℕ}

theorem swapped_chart_coefficient {R : Type*} [CommRing R]
    (F : Fin (a + 1) → MvPolynomial (Fin 2) R) (j : Fin (b + 1)) (i : Fin (a + 1)) :
    (chart (coefficients F j)).coeff i.val = (chart (F i)).coeff j.val := by
  classical
  simp [coefficients, chart, Fin.val_inj]

theorem swapped_twice {R : Type*} [CommRing R]
    (F : Fin (a + 1) → MvPolynomial (Fin 2) R) (hF : ∀ i, (F i).IsHomogeneous b) :
    coefficients (coefficients (k := b) F) = F := by
  funext i
  change (∑ j : Fin (b + 1), MvPolynomial.C ((chart (coefficients F j)).coeff i.val) *
    MvPolynomial.X 0 ^ j.val * MvPolynomial.X 1 ^ (b - j.val)) = F i
  simp_rw [swapped_chart_coefficient]
  exact (binary_expansion (F i) (hF i)).symm

theorem swapped_nonzero {R : Type*} [CommRing R]
    (F : Fin (a + 1) → MvPolynomial (Fin 2) R) (hF : ∀ i, (F i).IsHomogeneous b)
    (hF0 : F ≠ 0) : coefficients (k := b) F ≠ 0 := by
  intro hz
  apply hF0
  rw [← swapped_twice F hF, hz]
  funext i
  simp [coefficients, chart]

theorem swapped_height (F : Fin (a + 1) → MvPolynomial (Fin 2) ℤ)
    (hF : ∀ i, (F i).IsHomogeneous b) (H : ℕ)
    (hH : ∀ i m, ((F i).coeff m).natAbs ≤ H) :
    ∀ j : Fin (b + 1), ∀ m, ((coefficients F j).coeff m).natAbs ≤ H := by
  intro j
  apply coefficient_of_chart_height _ a H (coefficients_homogeneous F j)
  apply integer_height_le
  intro n
  by_cases hn : n ≤ a
  · let i : Fin (a + 1) := ⟨n, by omega⟩
    change (((chart (coefficients F j)).coeff i.val).natAbs) ≤ H
    rw [swapped_chart_coefficient, chart_coeff (F i) (hF i) j.val (by have := j.isLt; omega)]
    exact hH _ _
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt
      ((chart_degree _ (coefficients_homogeneous F j)).trans_lt (by omega))]
    simp

def transform (A B : Matrix (Fin 2) (Fin 2) ℤ)
    (F : Fin (a + 1) → MvPolynomial (Fin 2) ℤ) : Fin (a + 1) → MvPolynomial (Fin 2) ℤ :=
  fun i ↦ substitute B (coefficients (fun j : Fin (b + 1) ↦ substitute A (coefficients F j)) i)

theorem transform_homogeneous (A B : Matrix (Fin 2) (Fin 2) ℤ)
    (F : Fin (a + 1) → MvPolynomial (Fin 2) ℤ) (i : Fin (a + 1)) :
    (transform (b := b) A B F i).IsHomogeneous b :=
  substitute_homogeneous B _ b (coefficients_homogeneous _ i)

theorem original_substitute (B : Matrix (Fin 2) (Fin 2) ℤ)
    (F : Fin (a + 1) → MvPolynomial (Fin 2) ℤ) (x y : Fin 2 → ℤ) :
    BidegreeOneElimination.original (fun i ↦ substitute B (F i)) x y =
      BidegreeOneElimination.original F x (B.mulVec y) := by
  unfold BidegreeOneElimination.original
  simp_rw [evaluation]

theorem transform_evaluation (A B : Matrix (Fin 2) (Fin 2) ℤ)
    (F : Fin (a + 1) → MvPolynomial (Fin 2) ℤ) (hF : ∀ i, (F i).IsHomogeneous b)
    (x y : Fin 2 → ℤ) :
    BidegreeOneElimination.original (transform (b := b) A B F) x y =
      BidegreeOneElimination.original F (A.mulVec x) (B.mulVec y) := by
  change BidegreeOneElimination.original
    (fun i ↦ substitute B (coefficients (fun j : Fin (b + 1) ↦ substitute A (coefficients F j)) i)) x y = _
  rw [original_substitute]
  rw [original_swap _ (fun j ↦ substitute_homogeneous A _ a (coefficients_homogeneous F j))]
  rw [original_substitute]
  exact original_swap F hF _ _

theorem transform_nonzero (A A' B B' : Matrix (Fin 2) (Fin 2) ℤ)
    (hAA' : A * A' = 1) (hA'A : A' * A = 1) (hBB' : B * B' = 1) (hB'B : B' * B = 1)
    (F : Fin (a + 1) → MvPolynomial (Fin 2) ℤ)
    (hF : ∀ i, (F i).IsHomogeneous b) (hF0 : F ≠ 0) : transform (b := b) A B F ≠ 0 := by
  have hs := swapped_nonzero F hF hF0
  have ht : (fun j : Fin (b + 1) ↦ substitute A (coefficients F j)) ≠ 0 := by
    intro hz
    apply hs
    funext j
    have hj := congrFun hz j
    exact (equiv A A' hAA' hA'A).injective (by
      change substitute A (coefficients F j) = substitute A 0
      simpa only [map_zero, Pi.zero_apply] using hj)
  have hu := swapped_nonzero _ (fun j ↦ substitute_homogeneous A _ a (coefficients_homogeneous F j)) ht
  intro hz
  apply hu
  funext i
  have hi := congrFun hz i
  exact (equiv B B' hBB' hB'B).injective (by
    change substitute B _ = substitute B 0
    simpa only [transform, map_zero, Pi.zero_apply] using hi)

theorem transform_height (A B : Matrix (Fin 2) (Fin 2) ℤ)
    (F : Fin (a + 1) → MvPolynomial (Fin 2) ℤ) (hF : ∀ i, (F i).IsHomogeneous b)
    (H M T : ℕ) (hH : ∀ i m, ((F i).coeff m).natAbs ≤ H)
    (hM : ∀ i j, (A i j).natAbs ≤ M) (hT : ∀ i j, (B i j).natAbs ≤ T) :
    ∀ i m, ((transform (b := b) A B F i).coeff m).natAbs ≤
      (b + 1) * ((a + 1) * H * (2 * M) ^ a) * (2 * T) ^ b := by
  have hs := swapped_height F hF H hH
  have ht := fun j : Fin (b + 1) ↦ coefficient_height A (coefficients F j) a H M
    (coefficients_homogeneous F j) (hs j) hM
  have hu := swapped_height _ (fun j ↦ substitute_homogeneous A _ a (coefficients_homogeneous F j))
    ((a + 1) * H * (2 * M) ^ a) ht
  intro i m
  exact coefficient_height B _ b _ T (coefficients_homogeneous _ i) (hu i) hT m

end PaperP1.BiformLinearCoordinates
