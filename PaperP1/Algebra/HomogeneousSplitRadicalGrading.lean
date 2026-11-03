module

public import PaperP1.Algebra.HomogeneousSplitRadicalRelations
public import PaperP1.Algebra.WeightedPolynomialQuotientGrading

/-! # The source quotient has the actual weighted grading and the stated generator degrees -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HomogeneousSplitRadicalGrading

open Finset PaperP1.HomogeneousSplitRadicalRelations

attribute [local instance] MvPolynomial.weightedGradedAlgebra

abbrev CoordinateRing {F ι : Type*} [Field F] (c : ι → F) (D : ℕ) (I J : ι → Finset ℤ) :=
  WeightedPolynomial F ι ⧸ relationIdeal c D I J

def piece {F ι : Type*} [Field F] (c : ι → F) (D : ℕ) (I J : ι → Finset ℤ) (n : ℕ) :
    Submodule F (CoordinateRing c D I J) :=
  WeightedPolynomialQuotientGrading.piece (weight ι D) (relationIdeal c D I J) n

@[instance_reducible] def grading {F ι : Type*} [Field F]
    (c : ι → F) (D : ℕ) (I J : ι → Finset ℤ) (hD : ∀ i, (I i).card + (J i).card ≤ 2 * D) :
    GradedAlgebra (piece c D I J) :=
  WeightedPolynomialQuotientGrading.gradedAlgebra (weight ι D) (relationIdeal c D I J)
    (relationIdeal_homogeneous c D I J hD)

theorem base_variable_mem {F ι : Type*} [Field F]
    (c : ι → F) (D : ℕ) (I J : ι → Finset ℤ) (j : Fin 3) :
    Ideal.Quotient.mk (relationIdeal c D I J) (MvPolynomial.X (Sum.inl j)) ∈ piece c D I J 1 :=
  Submodule.mem_map.mpr ⟨MvPolynomial.X (Sum.inl j), base_variable_homogeneous F ι D j, rfl⟩

theorem radical_variable_mem {F ι : Type*} [Field F]
    (c : ι → F) (D : ℕ) (I J : ι → Finset ℤ) (i : ι) :
    Ideal.Quotient.mk (relationIdeal c D I J) (MvPolynomial.X (Sum.inr i)) ∈ piece c D I J D :=
  Submodule.mem_map.mpr ⟨MvPolynomial.X (Sum.inr i), radical_variable_homogeneous F ι D i, rfl⟩

theorem base_variable_component {F ι : Type*} [Field F]
    (c : ι → F) (D : ℕ) (I J : ι → Finset ℤ) (hD : ∀ i, (I i).card + (J i).card ≤ 2 * D)
    (n : ℕ) (j : Fin 3) :
    WeightedPolynomialQuotientGrading.component (weight ι D) (relationIdeal c D I J)
        (relationIdeal_homogeneous c D I J hD) n
        (Ideal.Quotient.mk (relationIdeal c D I J) (MvPolynomial.X (Sum.inl j))) =
      if n = 1 then Ideal.Quotient.mk (relationIdeal c D I J) (MvPolynomial.X (Sum.inl j)) else 0 :=
  WeightedPolynomialQuotientGrading.component_piece _ _ _ n 1 (base_variable_mem c D I J j)

theorem radical_variable_component {F ι : Type*} [Field F]
    (c : ι → F) (D : ℕ) (I J : ι → Finset ℤ) (hD : ∀ i, (I i).card + (J i).card ≤ 2 * D)
    (n : ℕ) (i : ι) :
    WeightedPolynomialQuotientGrading.component (weight ι D) (relationIdeal c D I J)
        (relationIdeal_homogeneous c D I J hD) n
        (Ideal.Quotient.mk (relationIdeal c D I J) (MvPolynomial.X (Sum.inr i))) =
      if n = D then Ideal.Quotient.mk (relationIdeal c D I J) (MvPolynomial.X (Sum.inr i)) else 0 :=
  WeightedPolynomialQuotientGrading.component_piece _ _ _ n D (radical_variable_mem c D I J i)

theorem weight_ne_zero (ι : Type*) (D : ℕ) (hD : 0 < D) (i : Fin 3 ⊕ ι) : weight ι D i ≠ 0 := by
  cases i with
  | inl j => exact one_ne_zero
  | inr i => exact Nat.ne_of_gt hD

theorem piece_zero_iff {F ι : Type*} [Field F]
    (c : ι → F) (D : ℕ) (hD : 0 < D) (I J : ι → Finset ℤ) (x : CoordinateRing c D I J) :
    x ∈ piece c D I J 0 ↔ ∃ a : F, algebraMap F (CoordinateRing c D I J) a = x :=
  WeightedPolynomialQuotientGrading.piece_zero_iff (weight ι D) (relationIdeal c D I J)
    (weight_ne_zero ι D hD) x

end PaperP1.HomogeneousSplitRadicalGrading
