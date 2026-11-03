module

public import PaperP1.Algebra.WeightedOrdinarySubstitution
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # The literal ordinary and weighted radical equations have the same Z=1 quotient -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.WeightedOrdinaryAffineIdeal

open MvPolynomial PaperP1.HomogeneousSplitRadicalRelations
  PaperP1.HomogeneousSplitRadicalPolynomials PaperP1.WeightedOrdinarySubstitution

variable {F ι : Type*} [Field F]

def ordinaryIdeal (c : ι → F) (I J : ι → Finset ℤ) : Ideal (WeightedPolynomial F ι) :=
  Ideal.span (Set.range fun i ↦ ordinaryRelation (c i) (I i) (J i) i)

def chartIdeal : Ideal (WeightedPolynomial F ι) := Ideal.span {X (Sum.inl (2 : Fin 3)) - 1}

theorem relation_eq_at_one {R : Type*} [CommRing R] (φ : WeightedPolynomial F ι →+* R)
    (hZ : φ (X (Sum.inl (2 : Fin 3))) = 1) (c : F) (D : ℕ) (I J : Finset ℤ) (i : ι) :
    φ (relation c D I J i) = φ (ordinaryRelation c I J i) := by
  simp only [relation, ordinaryRelation, nativeRadicand, map_sub, map_mul, map_pow,
    rename_X, hZ, one_pow, mul_one]

theorem substitution_eq_at_one {R : Type*} [CommRing R] (φ : WeightedPolynomial F ι →+* R)
    (hZ : φ (X (Sum.inl (2 : Fin 3))) = 1) (D : ℕ) (p : WeightedPolynomial F ι) :
    φ (WeightedOrdinarySubstitution.map D p) = φ p := by
  have heq : φ.comp (WeightedOrdinarySubstitution.map D).toRingHom = φ := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change φ (WeightedOrdinarySubstitution.map D (C a)) = φ (C a)
      simp only [WeightedOrdinarySubstitution.map, aeval_C, MvPolynomial.algebraMap_eq]
    · intro i
      cases i with
      | inl j =>
          change φ (WeightedOrdinarySubstitution.map D (X (Sum.inl j))) = φ (X (Sum.inl j))
          rw [WeightedOrdinarySubstitution.map_base]
      | inr i =>
          change φ (WeightedOrdinarySubstitution.map D (X (Sum.inr i))) = φ (X (Sum.inr i))
          rw [WeightedOrdinarySubstitution.map_radical, map_mul, map_pow, hZ, one_pow, one_mul]
  exact RingHom.congr_fun heq p

theorem ideals_sup_chart (c : ι → F) (D : ℕ) (I J : ι → Finset ℤ) :
    relationIdeal c D I J ⊔ chartIdeal = ordinaryIdeal c I J ⊔ chartIdeal := by
  have hz (K : Ideal (WeightedPolynomial F ι)) :
      Ideal.Quotient.mk (K ⊔ chartIdeal) (X (Sum.inl (2 : Fin 3))) = 1 := by
    apply sub_eq_zero.mp
    rw [← map_one (Ideal.Quotient.mk (K ⊔ chartIdeal)), ← map_sub]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      ((le_sup_right : chartIdeal ≤ K ⊔ chartIdeal) (Ideal.mem_span_singleton_self _))
  apply le_antisymm
  · apply sup_le _ le_sup_right
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [relation_eq_at_one _ (hz (ordinaryIdeal c I J))]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      ((show ordinaryIdeal c I J ≤ ordinaryIdeal c I J ⊔ chartIdeal from le_sup_left)
        (Ideal.subset_span (Set.mem_range_self i)))
  · apply sup_le _ le_sup_right
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    rw [← relation_eq_at_one _ (hz (relationIdeal c D I J)) (c i) D]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      ((show relationIdeal c D I J ≤ relationIdeal c D I J ⊔ chartIdeal from le_sup_left)
        (Ideal.subset_span (Set.mem_range_self i)))

end PaperP1.WeightedOrdinaryAffineIdeal
