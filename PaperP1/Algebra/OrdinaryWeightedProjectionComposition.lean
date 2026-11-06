module

public import PaperP1.Algebra.OrdinaryWeightedProjection

/-! # The actual weighted and ordinary substitutions compose to homogeneous powers of the chart coordinate -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OrdinaryWeightedProjectionComposition

open MvPolynomial HomogeneousSplitRadicalRelations

variable {F ι : Type*} [Field F]

theorem ordinary_composition (D : ℕ) :
    (WeightedOrdinarySubstitution.map (F := F) (ι := ι) D).comp (OrdinaryWeightedProjection.map D) =
      aeval (R := F) (fun i ↦ X (Sum.inl (2 : Fin 3)) ^ (D - 1) * X i) := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i with
  | inl j =>
    simp only [AlgHom.comp_apply, aeval_X, OrdinaryWeightedProjection.map_base, map_mul, map_pow,
      WeightedOrdinarySubstitution.map_base]
    ring
  | inr i =>
    simp only [AlgHom.comp_apply, aeval_X, OrdinaryWeightedProjection.map_radical,
      WeightedOrdinarySubstitution.map_radical]

theorem weighted_composition (D : ℕ) (hD : 0 < D) :
    (OrdinaryWeightedProjection.map (F := F) (ι := ι) D).comp (WeightedOrdinarySubstitution.map D) =
      aeval (R := F) (fun i ↦ (X (Sum.inl (2 : Fin 3)) ^ (D - 1)) ^ (weight ι D i) * X i) := by
  apply MvPolynomial.algHom_ext
  intro i
  cases i with
  | inl j =>
    simp only [AlgHom.comp_apply, aeval_X, WeightedOrdinarySubstitution.map_base,
      OrdinaryWeightedProjection.map_base, weight, Sum.elim_inl, pow_one]
    ring
  | inr i =>
    simp only [AlgHom.comp_apply, aeval_X, WeightedOrdinarySubstitution.map_radical, map_mul, map_pow,
      OrdinaryWeightedProjection.map_Z D hD, OrdinaryWeightedProjection.map_radical, weight, Sum.elim_inr]
    rw [← pow_mul, ← pow_mul, Nat.mul_comm D (D - 1)]

theorem ordinary_homogeneous (D : ℕ) {n : ℕ} (p : WeightedPolynomial F ι) (hp : p.IsHomogeneous n) :
    WeightedOrdinarySubstitution.map D (OrdinaryWeightedProjection.map D p) =
      X (Sum.inl (2 : Fin 3)) ^ ((D - 1) * n) * p := by
  have he := DFunLike.congr_fun (ordinary_composition (F := F) (ι := ι) D) p
  change WeightedOrdinarySubstitution.map D (OrdinaryWeightedProjection.map D p) = _ at he
  rw [he, WeightedHomogeneousEvaluation.aeval_homogeneous_scale p hp, aeval_X_left,
    AlgHom.id_apply, ← pow_mul]

theorem weighted_homogeneous (D : ℕ) (hD : 0 < D) {n : ℕ} (p : WeightedPolynomial F ι)
    (hp : p.IsWeightedHomogeneous (weight ι D) n) :
    OrdinaryWeightedProjection.map D (WeightedOrdinarySubstitution.map D p) =
      X (Sum.inl (2 : Fin 3)) ^ ((D - 1) * n) * p := by
  have he := DFunLike.congr_fun (weighted_composition (F := F) (ι := ι) D hD) p
  change OrdinaryWeightedProjection.map D (WeightedOrdinarySubstitution.map D p) = _ at he
  rw [he, WeightedHomogeneousEvaluation.aeval_scale (weight ι D) p hp, aeval_X_left,
    AlgHom.id_apply, ← pow_mul]

theorem map_relation (c : F) (D : ℕ) (I J : Finset ℤ) (i : ι)
    (hD : 0 < D) (hmin : 2 ≤ I.card + J.card) (hdeg : I.card + J.card ≤ 2 * D) :
    OrdinaryWeightedProjection.map D (WeightedOrdinarySubstitution.ordinaryRelation c I J i) =
      X (Sum.inl (2 : Fin 3)) ^ (D * (I.card + J.card - 2)) * relation c D I J i := by
  have hh := congrArg (OrdinaryWeightedProjection.map (F := F) (ι := ι) D)
    (WeightedOrdinarySubstitution.map_relation c D I J i hD hmin hdeg)
  rw [weighted_homogeneous D hD _ (relation_homogeneous c D I J hdeg i), map_mul, map_pow,
    OrdinaryWeightedProjection.map_Z D hD, ← pow_mul] at hh
  have he : D * (2 * D - (I.card + J.card)) + D * (I.card + J.card - 2) = (D - 1) * (2 * D) := by
    rw [← Nat.mul_add]
    have ht : 2 * D - (I.card + J.card) + (I.card + J.card - 2) = 2 * (D - 1) := by omega
    rw [ht]
    ring
  have hz : (X (Sum.inl (2 : Fin 3)) : WeightedPolynomial F ι) ^ (D * (2 * D - (I.card + J.card))) ≠ 0 :=
    pow_ne_zero _ (X_ne_zero _)
  apply mul_left_cancel₀ hz
  rw [← mul_assoc, ← pow_add, he]
  exact hh.symm

end PaperP1.OrdinaryWeightedProjectionComposition
