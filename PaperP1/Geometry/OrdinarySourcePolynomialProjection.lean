module

public import PaperP1.Algebra.OrdinaryWeightedProjectionComposition
public import PaperP1.Geometry.OrdinaryCurveSourcePoint
public import PaperP1.Algebra.GradedPolynomialGenerators

/-! # The actual ordinary polynomial coordinates map into the original source Veronese algebra -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OrdinarySourcePolynomialProjection

open MvPolynomial HomogeneousSplitRadicalRelations HomogeneousSplitRadicalVeronese SourceVeroneseGrading

local instance rawGradedMonoid {F ι : Type*} [Field F] (c : ι → F) (D : ℕ) (I J : ι → Finset ℤ) :
    SetLike.GradedMonoid (HomogeneousSplitRadicalGrading.piece c D I J) :=
  WeightedPolynomialQuotientGrading.gradedMonoid (weight ι D) (relationIdeal c D I J)

variable {F ι : Type*} [Field F] (c : ι → F) (D : ℕ) (hD : 0 < D) (I J : ι → Finset ℤ)

def coordinate (i : Fin 3 ⊕ ι) : veronese c D I J :=
  ⟨Ideal.Quotient.mk (relationIdeal c D I J) (OrdinaryWeightedProjection.generator D i),
    GradedVeroneseAlgebra.piece_mem (HomogeneousSplitRadicalGrading.piece c D I J) D 1 (by
      rw [one_mul]
      exact Submodule.mem_map.mpr ⟨_, OrdinaryWeightedProjection.generator_homogeneous D hD i, rfl⟩)⟩

theorem coordinate_mem (i : Fin 3 ⊕ ι) : coordinate c D hD I J i ∈ sourcePiece c D I J 1 := by
  change Ideal.Quotient.mk (relationIdeal c D I J) (OrdinaryWeightedProjection.generator D i) ∈
    HomogeneousSplitRadicalGrading.piece c D I J (1 * D)
  rw [one_mul]
  exact Submodule.mem_map.mpr ⟨_, OrdinaryWeightedProjection.generator_homogeneous D hD i, rfl⟩

def evaluation : WeightedPolynomial F ι →ₐ[F] veronese c D I J := aeval (coordinate c D hD I J)

theorem evaluation_value (p : WeightedPolynomial F ι) :
    (evaluation c D hD I J p).val = Ideal.Quotient.mk (relationIdeal c D I J) (OrdinaryWeightedProjection.map D p) := by
  have he : (veronese c D I J).val.comp (evaluation c D hD I J) =
      (Ideal.Quotient.mkₐ F (relationIdeal c D I J)).comp (OrdinaryWeightedProjection.map D) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, evaluation, aeval_X]
    change Ideal.Quotient.mk (relationIdeal c D I J) (OrdinaryWeightedProjection.generator D i) =
      Ideal.Quotient.mk (relationIdeal c D I J) (OrdinaryWeightedProjection.map D (X i))
    rw [OrdinaryWeightedProjection.map, aeval_X]
  exact DFunLike.congr_fun he p

theorem evaluation_homogeneous (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D)
    {n : ℕ} (p : WeightedPolynomial F ι) (hp : p.IsHomogeneous n) :
    evaluation c D hD I J p ∈ sourcePiece c D I J n := by
  let := sourceGrading c D I J hdeg hD
  exact GradedPolynomialGenerators.eval_homogeneous (sourcePiece c D I J)
    (coordinate c D hD I J) (coordinate_mem c D hD I J) n p hp

theorem ordinary_relation_zero (i : ι) (hmin : 2 ≤ (I i).card + (J i).card)
    (hdeg : (I i).card + (J i).card ≤ 2 * D) :
    evaluation c D hD I J (WeightedOrdinarySubstitution.ordinaryRelation (c i) (I i) (J i) i) = 0 := by
  apply Subtype.ext
  change (evaluation c D hD I J _).val = 0
  rw [evaluation_value, OrdinaryWeightedProjectionComposition.map_relation (c i) D (I i) (J i) i hD hmin hdeg]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact (relationIdeal c D I J).mul_mem_left _ (Ideal.subset_span (Set.mem_range_self i))

theorem coordinate_Z : coordinate c D hD I J (Sum.inl (2 : Fin 3)) = OrdinaryCurveSourcePoint.sourceZ c D I J := by
  apply Subtype.ext
  change Ideal.Quotient.mk (relationIdeal c D I J)
    (X (Sum.inl (2 : Fin 3)) * X (Sum.inl (2 : Fin 3)) ^ (D - 1)) =
    Ideal.Quotient.mk (relationIdeal c D I J) (X (Sum.inl (2 : Fin 3)) ^ D)
  rw [← pow_succ', Nat.sub_add_cancel hD]

theorem evaluation_substitution (n : ℕ) (a : veronese c D I J) (p : WeightedPolynomial F ι)
    (hp : p.IsWeightedHomogeneous (weight ι D) (n * D))
    (hpa : Ideal.Quotient.mk (relationIdeal c D I J) p = a.val) :
    evaluation c D hD I J (WeightedOrdinarySubstitution.map D p) =
      OrdinaryCurveSourcePoint.sourceZ c D I J ^ ((D - 1) * n) * a := by
  apply Subtype.ext
  change (evaluation c D hD I J _).val =
    (Ideal.Quotient.mk (relationIdeal c D I J) (X (Sum.inl (2 : Fin 3)) ^ D)) ^ ((D - 1) * n) * a.val
  rw [evaluation_value, OrdinaryWeightedProjectionComposition.weighted_homogeneous D hD p hp,
    map_mul, map_pow, hpa, map_pow, ← pow_mul]
  have he : (D - 1) * (n * D) = D * ((D - 1) * n) := by ring
  rw [he]

end PaperP1.OrdinarySourcePolynomialProjection
