module

public import PaperP1.Arithmetic.OrdinaryIntegerPoints
public import PaperP1.Arithmetic.SplitRadicalPointHeight
public import PaperP1.Algebra.WeightedOrdinaryAffineIdeal

/-! # Literal integer radical equations give actual points of the ordinary radical surface -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OrdinaryRootEvaluation

open Finset MvPolynomial PaperP1.HomogeneousSplitRadicalRelations PaperP1.HomogeneousSplitRadicalPolynomials
  PaperP1.OrdinaryIntegerPoints PaperP1.SplitRadicalPointHeight PaperP1.WeightedOrdinaryAffineIdeal

variable {ι : Type*}

theorem evaluation_C (v : Point ι) (c : ℚ) : evaluation v (C c) = c := by simp

theorem nativeLinear_value (v : Point ι) (hZ : v (Sum.inl 2) = 1) (j : Fin 3) (I : Finset ℤ) :
    evaluation v (rename Sum.inl (nativeLinear ℚ j I)) =
      ∏ z ∈ I, ((v (Sum.inl j) : ℚ) + (z : ℚ)) := by
  simp only [nativeLinear, map_prod, map_add, map_mul, rename_X, rename_C,
    evaluation_X, evaluation_C, hZ, Int.cast_one, mul_one]

theorem integerProduct_cast (I : Finset ℤ) (x : ℤ) :
    (integerProduct I x : ℚ) = ∏ z ∈ I, ((x : ℚ) + (z : ℚ)) := by
  simp [integerProduct]

theorem ordinaryRelation_value (d : ℤ) (I J : Finset ℤ) (x y : ℤ) (w : ι → ℤ) (i : ι) :
    evaluation (lift x y w) (WeightedOrdinarySubstitution.ordinaryRelation (d : ℚ) I J i) =
      (w i : ℚ) ^ 2 - (d : ℚ) * (integerProduct I x : ℚ) * (integerProduct J y : ℚ) := by
  simp only [WeightedOrdinarySubstitution.ordinaryRelation, map_sub, map_mul, map_pow, rename_C,
    evaluation_X, evaluation_C, lift_Z, Int.cast_one, one_pow, mul_one]
  rw [nativeLinear_value (lift x y w) (lift_Z x y w) 1 I,
    nativeLinear_value (lift x y w) (lift_Z x y w) 0 J]
  rw [integerProduct_cast, integerProduct_cast]
  rfl

theorem ideal_le_kernel (d : ι → ℤ) (I J : ι → Finset ℤ) (x y : ℤ) (w : ι → ℤ)
    (hroot : ∀ i, w i ^ 2 = d i * integerProduct (I i) x * integerProduct (J i) y) :
    ordinaryIdeal (fun i ↦ (d i : ℚ)) I J ≤ RingHom.ker (evaluation (lift x y w)).toRingHom := by
  apply Ideal.span_le.mpr
  rintro _ ⟨i, rfl⟩
  change evaluation (lift x y w) (WeightedOrdinarySubstitution.ordinaryRelation (d i : ℚ) (I i) (J i) i) = 0
  rw [ordinaryRelation_value]
  apply sub_eq_zero.mpr
  exact_mod_cast hroot i

variable [Fintype ι] [DecidableEq ι]

theorem lift_mem (d : ι → ℤ) (I J : ι → Finset ℤ) (x y : ℤ) (w : ι → ℤ) (H : ℕ)
    (hheight : ∀ i, |lift x y w i| ≤ (H : ℤ))
    (hroot : ∀ i, w i ^ 2 = d i * integerProduct (I i) x * integerProduct (J i) y) :
    lift x y w ∈ curvePoints (ordinaryIdeal (fun i ↦ (d i : ℚ)) I J) H :=
  (mem_curvePoints _ H _).mpr ⟨⟨hheight, lift_Z x y w⟩, ideal_le_kernel d I J x y w hroot⟩

end PaperP1.OrdinaryRootEvaluation
