module

public import PaperP1.Algebra.HomogeneousSplitRadicalRelations
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.Tactic.Linarith

/-! # The literal weighted-to-ordinary homogenization w ↦ Z^(D-1)w -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.WeightedOrdinarySubstitution

open Finset MvPolynomial PaperP1.HomogeneousSplitRadicalRelations
  PaperP1.HomogeneousSplitRadicalPolynomials

variable {F ι : Type*} [Field F]

def generator (D : ℕ) : Fin 3 ⊕ ι → WeightedPolynomial F ι :=
  Sum.elim (fun j ↦ X (Sum.inl j)) (fun i ↦ X (Sum.inl (2 : Fin 3)) ^ (D - 1) * X (Sum.inr i))

def map (D : ℕ) : WeightedPolynomial F ι →ₐ[F] WeightedPolynomial F ι := aeval (generator D)

theorem map_base (D : ℕ) (j : Fin 3) : map (F := F) (ι := ι) D (X (Sum.inl j)) = X (Sum.inl j) :=
  aeval_X _ _

theorem map_radical (D : ℕ) (i : ι) : map (F := F) D (X (Sum.inr i)) =
    X (Sum.inl (2 : Fin 3)) ^ (D - 1) * X (Sum.inr i) := aeval_X _ _

theorem map_rename (D : ℕ) (p : MvPolynomial (Fin 3) F) :
    map (F := F) (ι := ι) D (rename Sum.inl p) = rename Sum.inl p := by
  have heq : (map (F := F) (ι := ι) D).comp (rename Sum.inl) = rename Sum.inl := by
    ext j
    simp only [AlgHom.comp_apply, rename_X, map_base]
  exact AlgHom.congr_fun heq p

theorem generator_homogeneous (D : ℕ) (hD : 0 < D) (i : Fin 3 ⊕ ι) :
    (generator (F := F) D i).IsHomogeneous (weight ι D i) := by
  cases i with
  | inl j => exact isHomogeneous_X F _
  | inr i =>
    have h := ((isHomogeneous_X F (Sum.inl (2 : Fin 3))).pow (D - 1)).mul
      (isHomogeneous_X F (Sum.inr i))
    simpa only [generator, Sum.elim_inr, weight, one_mul, Nat.sub_add_cancel hD] using h

theorem map_homogeneous (D : ℕ) (hD : 0 < D) (n : ℕ) (p : WeightedPolynomial F ι)
    (hp : p.IsWeightedHomogeneous (weight ι D) n) : (map D p).IsHomogeneous n := by
  classical
  induction hp using IsWeightedHomogeneous.induction_on with
  | zero => simpa only [map_zero] using (isHomogeneous_zero (Fin 3 ⊕ ι) F n)
  | add p q _ _ ihp ihq => simpa only [map_add] using ihp.add ihq
  | monomial d c hd =>
    rw [map, aeval_monomial]
    have hprod : (d.prod fun i k ↦ generator (F := F) D i ^ k).IsHomogeneous (d.weight (weight ι D)) := by
      simpa only [Finsupp.prod, Finsupp.weight_apply, Finsupp.sum, smul_eq_mul, Nat.mul_comm] using
        IsHomogeneous.prod d.support (fun i ↦ generator (F := F) D i ^ d i)
          (fun i ↦ weight ι D i * d i) (fun i _ ↦ (generator_homogeneous D hD i).pow (d i))
    simpa only [hd, MvPolynomial.algebraMap_eq] using hprod.C_mul c

def ordinaryRelation (c : F) (I J : Finset ℤ) (i : ι) : WeightedPolynomial F ι :=
  X (Sum.inr i) ^ 2 * X (Sum.inl (2 : Fin 3)) ^ (I.card + J.card - 2) -
    rename Sum.inl (C c * nativeLinear F 1 I * nativeLinear F 0 J)

theorem ordinaryRelation_homogeneous (c : F) (I J : Finset ℤ) (i : ι)
    (hcard : 2 ≤ I.card + J.card) : (ordinaryRelation c I J i).IsHomogeneous (I.card + J.card) := by
  have hleft := ((isHomogeneous_X F (Sum.inr i)).pow 2).mul
    ((isHomogeneous_X F (Sum.inl (2 : Fin 3))).pow (I.card + J.card - 2))
  have hright := (((nativeLinear_homogeneous F 1 I).C_mul c).mul
    (nativeLinear_homogeneous F 0 J))
  apply IsHomogeneous.sub _ hright.rename_isHomogeneous
  convert hleft using 1
  simp only [one_mul]
  omega

theorem map_relation (c : F) (D : ℕ) (I J : Finset ℤ) (i : ι)
    (hD : 0 < D) (hcard : 2 ≤ I.card + J.card) (hdegree : I.card + J.card ≤ 2 * D) :
    map D (relation c D I J i) = X (Sum.inl (2 : Fin 3)) ^ (2 * D - (I.card + J.card)) *
      ordinaryRelation c I J i := by
  have hexponent : 2 * D - (I.card + J.card) + (I.card + J.card - 2) = 2 * (D - 1) := by omega
  simp only [relation, ordinaryRelation, map_sub, map_pow, map_radical, map_rename,
    nativeRadicand, map_mul, rename_C, rename_X, map_base]
  have hC : map (F := F) (ι := ι) D (C c) = C c := aeval_C _ _
  rw [hC]
  rw [mul_pow]
  rw [mul_sub]
  have hz : X (Sum.inl (2 : Fin 3)) ^ (2 * D - (I.card + J.card)) *
      X (Sum.inl (2 : Fin 3)) ^ (I.card + J.card - 2) =
      (X (Sum.inl (2 : Fin 3)) : WeightedPolynomial F ι) ^ ((D - 1) * 2) := by
    rw [← pow_add, hexponent, Nat.mul_comm 2]
  rw [← pow_mul]
  calc
    X (Sum.inl (2 : Fin 3)) ^ ((D - 1) * 2) * X (Sum.inr i) ^ 2 -
        (C c * X (Sum.inl (2 : Fin 3)) ^ (2 * D - (I.card + J.card))) *
          rename Sum.inl (nativeLinear F 1 I) * rename Sum.inl (nativeLinear F 0 J) =
      (X (Sum.inl (2 : Fin 3)) ^ (2 * D - (I.card + J.card)) *
        X (Sum.inl (2 : Fin 3)) ^ (I.card + J.card - 2)) * X (Sum.inr i) ^ 2 -
        X (Sum.inl (2 : Fin 3)) ^ (2 * D - (I.card + J.card)) *
          ((C c * rename Sum.inl (nativeLinear F 1 I)) * rename Sum.inl (nativeLinear F 0 J)) := by rw [hz]; ring
    _ = _ := by ring

end PaperP1.WeightedOrdinarySubstitution
