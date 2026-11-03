module

public import PaperP1.Algebra.ScaledSplitWordSquares
public import PaperP1.Algebra.FieldSquareClasses
public import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-! # Independent square classes of scaled disjoint univariate split products -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UnivariateSplitSquareClasses

open Finset Polynomial PaperP1.FormalWordPolynomials

variable {R ι : Type*} [CommRing R] [IsDomain R]

abbrev FunctionField (R : Type*) [CommRing R] [IsDomain R] := FractionRing R[X]

def value (c : R) (I : Finset ℤ) : FunctionField R :=
  algebraMap R[X] (FunctionField R) (C c * linearOver R I)

omit [IsDomain R] in
theorem linear_monic (I : Finset ℤ) : (linearOver R I).Monic :=
  monic_prod_of_monic _ _ (fun _ _ ↦ monic_X_add_C _)

theorem value_ne_zero (c : R) (hc : c ≠ 0) (I : Finset ℤ) : value c I ≠ 0 := by
  intro hz
  exact mul_ne_zero (C_ne_zero.mpr hc) (linear_monic I).ne_zero
    (IsFractionRing.injective R[X] (FunctionField R) (hz.trans (map_zero _).symm))

theorem polynomial_not_square [CharZero R] (c : R) (hc : c ≠ 0)
    (I : Finset ℤ) (hI : I.Nonempty) : ¬ IsSquare (C c * linearOver R I) := by
  let K := FractionRing R
  let : CharZero K := charZero_of_injective_algebraMap (IsFractionRing.injective R K)
  let φ : R →+* K := algebraMap R K
  have hcK : φ c ≠ 0 := by
    intro hz
    exact hc (IsFractionRing.injective R K (hz.trans (map_zero φ).symm))
  have heq : (C c * linearOver R I).map φ = C (φ c) * linearOver K I := by
    simp only [linearOver, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_prod,
      Polynomial.map_add, Polynomial.map_X, Polynomial.map_intCast, map_intCast]
  have hsep : ((C c * linearOver R I).map φ).Separable := by
    rw [heq]
    exact Polynomial.Separable.unit_mul (isUnit_C.mpr (isUnit_iff_ne_zero.mpr hcK))
      (ScaledSplitWordSquares.linear_separable I)
  have hn : ¬ IsUnit ((C c * linearOver R I).map φ) := by
    intro hu
    rw [heq] at hu
    have hd := natDegree_eq_zero_of_isUnit (isUnit_of_mul_isUnit_right hu)
    rw [ScaledSplitWordSquares.linear_degree] at hd
    exact hI.card_pos.ne' hd
  intro hs
  exact BivariateWordSquares.separable_not_square _ hsep hn (hs.map (Polynomial.mapRingHom φ))

theorem value_not_square [CharZero R] [IsIntegrallyClosed R] (c : R) (hc : c ≠ 0)
    (I : Finset ℤ) (hI : I.Nonempty) : ¬ IsSquare (value c I) := by
  intro hs
  exact polynomial_not_square c hc I hI
    ((SquareInFractionField.square_reflect (K := FunctionField R) _).mp hs)

theorem value_product (A : Finset ι) (c : ι → R) (I : ι → Finset ℤ)
    (hI : (↑A : Set ι).PairwiseDisjoint I) :
    (∏ i ∈ A, value (c i) (I i)) = value (∏ i ∈ A, c i) (A.biUnion I) := by
  have hlinear : linearOver R (A.biUnion I) = ∏ i ∈ A, linearOver R (I i) := prod_biUnion hI
  simp only [value, hlinear, ← map_prod, prod_mul_distrib]

theorem product_not_square [CharZero R] [IsIntegrallyClosed R]
    (A : Finset ι) (hA : A.Nonempty) (c : ι → R) (I : ι → Finset ℤ)
    (hc : ∀ i ∈ A, c i ≠ 0) (hne : ∀ i ∈ A, (I i).Nonempty)
    (hI : (↑A : Set ι).PairwiseDisjoint I) : ¬ IsSquare (∏ i ∈ A, value (c i) (I i)) := by
  rw [value_product A c I hI]
  apply value_not_square _ (prod_ne_zero_iff.mpr hc)
  obtain ⟨i, hi⟩ := hA
  obtain ⟨u, hu⟩ := hne i hi
  exact ⟨u, mem_biUnion.mpr ⟨i, hi, hu⟩⟩

def squareClass (c : R) (hc : c ≠ 0) (I : Finset ℤ) : FieldSquareClasses.Classes (FunctionField R) :=
  FieldSquareClasses.ofNonzero (value c I) (value_ne_zero c hc I)

theorem nonempty_sum_ne_zero [CharZero R] [IsIntegrallyClosed R]
    (A : Finset ι) (hA : A.Nonempty) (c : ι → R) (hc : ∀ i, c i ≠ 0) (I : ι → Finset ℤ)
    (hne : ∀ i, (I i).Nonempty) (hI : (↑A : Set ι).PairwiseDisjoint I) :
    (∑ i ∈ A, squareClass (c i) (hc i) (I i)) ≠ 0 := by
  simp only [squareClass]
  rw [← FieldSquareClasses.ofNonzero_prod A (fun i ↦ value (c i) (I i))
    (fun i ↦ value_ne_zero (c i) (hc i) (I i))]
  intro hz
  exact product_not_square A hA c I (fun i _ ↦ hc i) (fun i _ ↦ hne i) hI
    ((FieldSquareClasses.ofNonzero_zero_iff _ _).mp hz)

theorem linearIndependent [CharZero R] [IsIntegrallyClosed R]
    (c : ι → R) (hc : ∀ i, c i ≠ 0) (I : ι → Finset ℤ)
    (hne : ∀ i, (I i).Nonempty) (hI : Pairwise fun i j ↦ Disjoint (I i) (I j)) :
    LinearIndependent (ZMod 2) (fun i ↦ squareClass (c i) (hc i) (I i)) := by
  classical
  have hbinary : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
  rw [linearIndependent_iff']
  intro A g hsum i hi
  let B := A.filter fun j ↦ g j ≠ 0
  have hBsum : (∑ j ∈ B, squareClass (c j) (hc j) (I j)) = 0 := by
    have heq : (∑ j ∈ B, squareClass (c j) (hc j) (I j)) =
        ∑ j ∈ A, g j • squareClass (c j) (hc j) (I j) := by
      rw [sum_filter]
      apply sum_congr rfl
      intro j _
      rcases hbinary (g j) with hz | ho
      · simp only [hz, ne_self_iff_false, ite_false, zero_smul]
      · simp only [ho, one_smul]
        norm_num
    exact heq.trans hsum
  by_contra hgi
  have hB : B.Nonempty := ⟨i, mem_filter.mpr ⟨hi, hgi⟩⟩
  exact nonempty_sum_ne_zero B hB c hc I hne (fun a _ b _ hab ↦ hI hab) hBsum

end PaperP1.UnivariateSplitSquareClasses
