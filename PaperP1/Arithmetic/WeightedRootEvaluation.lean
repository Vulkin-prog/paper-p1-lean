module

public import PaperP1.Arithmetic.OrdinaryRootEvaluation
public import PaperP1.Algebra.SourceVeroneseGrading

/-! # Literal integer square roots construct an actual weighted-source and source-Veronese evaluation -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.WeightedRootEvaluation

open MvPolynomial PaperP1.HomogeneousSplitRadicalRelations PaperP1.HomogeneousSplitRadicalGrading
  PaperP1.HomogeneousSplitRadicalVeronese PaperP1.HomogeneousSplitRadicalFiniteVeronese
  PaperP1.OrdinaryIntegerPoints PaperP1.SplitRadicalPointHeight

variable {ι : Type*}

theorem ideal_le_kernel (d : ι → ℤ) (D : ℕ) (I J : ι → Finset ℤ) (x y : ℤ) (w : ι → ℤ)
    (hroot : ∀ i, w i ^ 2 = d i * integerProduct (I i) x * integerProduct (J i) y) :
    relationIdeal (fun i ↦ (d i : ℚ)) D I J ≤ RingHom.ker (evaluation (lift x y w)).toRingHom := by
  apply Ideal.span_le.mpr
  rintro _ ⟨i, rfl⟩
  change (evaluation (lift x y w)).toRingHom (relation (d i : ℚ) D (I i) (J i) i) = 0
  rw [WeightedOrdinaryAffineIdeal.relation_eq_at_one (evaluation (lift x y w)).toRingHom
    (by
      change evaluation (lift x y w) (X (Sum.inl (2 : Fin 3))) = 1
      rw [evaluation_X, lift_Z, Int.cast_one])]
  exact OrdinaryRootEvaluation.ideal_le_kernel d I J x y w hroot (Ideal.subset_span (Set.mem_range_self i))

variable (d : ι → ℤ) (D : ℕ) (I J : ι → Finset ℤ) (x y : ℤ) (w : ι → ℤ)
  (hroot : ∀ i, w i ^ 2 = d i * integerProduct (I i) x * integerProduct (J i) y)

def quotientEvaluation : CoordinateRing (fun i ↦ (d i : ℚ)) D I J →+* ℚ :=
  Ideal.Quotient.lift _ (evaluation (lift x y w)).toRingHom (ideal_le_kernel d D I J x y w hroot)

theorem quotientEvaluation_mk (p : WeightedPolynomial ℚ ι) :
    quotientEvaluation d D I J x y w hroot (quotientMap (fun i ↦ (d i : ℚ)) D I J p) =
      evaluation (lift x y w) p := rfl

def sourceEvaluation : veronese (fun i ↦ (d i : ℚ)) D I J →+* ℚ :=
  (quotientEvaluation d D I J x y w hroot).comp
    (veronese (fun i ↦ (d i : ℚ)) D I J).val.toRingHom

theorem sourceGenerator_value (g : SplitWeightedDegreeGenerators.generators ℚ ι D) :
    sourceEvaluation d D I J x y w hroot (SourceVeroneseGrading.sourceGenerator (fun i ↦ (d i : ℚ)) D I J g) =
      evaluation (lift x y w) (g : WeightedPolynomial ℚ ι) := rfl

end PaperP1.WeightedRootEvaluation
