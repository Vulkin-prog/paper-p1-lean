module

public import PaperP1.Algebra.HomogeneousSplitRadicalPolynomials

/-! # The actual weighted homogeneous radical relations and their homogeneous ideal -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HomogeneousSplitRadicalRelations

open Finset PaperP1.HomogeneousSplitRadicalPolynomials

def weight (ι : Type*) (D : ℕ) : Fin 3 ⊕ ι → ℕ := Sum.elim (fun _ ↦ 1) (fun _ ↦ D)

abbrev WeightedPolynomial (F ι : Type*) [Field F] := MvPolynomial (Fin 3 ⊕ ι) F

def relation {F ι : Type*} [Field F] (c : F) (D : ℕ) (I J : Finset ℤ) (i : ι) :
    WeightedPolynomial F ι :=
  MvPolynomial.X (Sum.inr i) ^ 2 -
    MvPolynomial.rename Sum.inl (nativeRadicand c (2 * D - (I.card + J.card)) I J)

def relationIdeal {F ι : Type*} [Field F] (c : ι → F) (D : ℕ) (I J : ι → Finset ℤ) :
    Ideal (WeightedPolynomial F ι) := Ideal.span (Set.range fun i ↦ relation (c i) D (I i) (J i) i)

theorem base_variable_homogeneous (F ι : Type*) [Field F] (D : ℕ) (j : Fin 3) :
    MvPolynomial.IsWeightedHomogeneous (weight ι D)
      (MvPolynomial.X (Sum.inl j) : WeightedPolynomial F ι) 1 :=
  MvPolynomial.isWeightedHomogeneous_X F _ _

theorem radical_variable_homogeneous (F ι : Type*) [Field F] (D : ℕ) (i : ι) :
    MvPolynomial.IsWeightedHomogeneous (weight ι D)
      (MvPolynomial.X (Sum.inr i) : WeightedPolynomial F ι) D :=
  MvPolynomial.isWeightedHomogeneous_X F _ _

theorem rename_linear_homogeneous (F ι : Type*) [Field F] (D : ℕ) (j : Fin 3) (I : Finset ℤ) :
    MvPolynomial.IsWeightedHomogeneous (weight ι D)
      (MvPolynomial.rename Sum.inl (nativeLinear F j I)) I.card := by
  have h := MvPolynomial.IsWeightedHomogeneous.prod I
    (fun i : ℤ ↦ (MvPolynomial.X (Sum.inl j) + MvPolynomial.C (i : F) *
      MvPolynomial.X (Sum.inl (2 : Fin 3)) : WeightedPolynomial F ι)) (fun _ ↦ 1)
    (fun i _ ↦ (base_variable_homogeneous F ι D j).add
      ((base_variable_homogeneous F ι D 2).C_mul (i : F)))
  simpa only [nativeLinear, map_prod, map_add, map_mul, MvPolynomial.rename_X, MvPolynomial.rename_C,
    sum_const, smul_eq_mul, mul_one] using h

theorem rename_radicand_homogeneous {F ι : Type*} [Field F]
    (c : F) (e D : ℕ) (I J : Finset ℤ) :
    MvPolynomial.IsWeightedHomogeneous (weight ι D)
      (MvPolynomial.rename Sum.inl (nativeRadicand c e I J)) (e + I.card + J.card) := by
  have hpow : MvPolynomial.IsWeightedHomogeneous (weight ι D)
      ((MvPolynomial.X (Sum.inl (2 : Fin 3)) : WeightedPolynomial F ι) ^ e) e := by
    simpa only [smul_eq_mul, mul_one] using (base_variable_homogeneous F ι D 2).pow e
  simpa only [nativeRadicand, map_mul, map_pow, MvPolynomial.rename_X, MvPolynomial.rename_C] using
    ((hpow.C_mul c).mul (rename_linear_homogeneous F ι D 1 I)).mul
      (rename_linear_homogeneous F ι D 0 J)

theorem relation_homogeneous {F ι : Type*} [Field F]
    (c : F) (D : ℕ) (I J : Finset ℤ) (hD : I.card + J.card ≤ 2 * D) (i : ι) :
    MvPolynomial.IsWeightedHomogeneous (weight ι D) (relation c D I J i) (2 * D) := by
  have hw : MvPolynomial.IsWeightedHomogeneous (weight ι D)
      ((MvPolynomial.X (Sum.inr i) : WeightedPolynomial F ι) ^ 2) (2 * D) := by
    simpa only [smul_eq_mul] using (radical_variable_homogeneous F ι D i).pow 2
  have hr : MvPolynomial.IsWeightedHomogeneous (weight ι D)
      (MvPolynomial.rename Sum.inl (nativeRadicand c (2 * D - (I.card + J.card)) I J)) (2 * D) := by
    convert rename_radicand_homogeneous (ι := ι) c (2 * D - (I.card + J.card)) D I J using 1; omega
  exact hw.sub hr

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem relationIdeal_homogeneous {F ι : Type*} [Field F]
    (c : ι → F) (D : ℕ) (I J : ι → Finset ℤ) (hD : ∀ i, (I i).card + (J i).card ≤ 2 * D) :
    (relationIdeal c D I J).IsHomogeneous
      (MvPolynomial.weightedHomogeneousSubmodule F (weight ι D)) := by
  apply Ideal.homogeneous_span
  rintro _ ⟨i, rfl⟩
  exact ⟨2 * D, relation_homogeneous (c i) D (I i) (J i) (hD i) i⟩

end PaperP1.HomogeneousSplitRadicalRelations
