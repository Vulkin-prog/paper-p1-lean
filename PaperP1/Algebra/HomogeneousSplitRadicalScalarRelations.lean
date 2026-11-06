module

public import PaperP1.Algebra.HomogeneousSplitRadicalRelations
public import Mathlib.Algebra.MvPolynomial.Rename

/-! # The literal homogeneous radical relations commute with extension of the coefficient field -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HomogeneousSplitRadicalScalarRelations

open MvPolynomial HomogeneousSplitRadicalPolynomials HomogeneousSplitRadicalRelations

variable {F E ι : Type*} [Field F] [Field E]

theorem linear_map (φ : F →+* E) (j : Fin 3) (I : Finset ℤ) :
    map φ (nativeLinear F j I) = nativeLinear E j I := by
  simp only [nativeLinear, map_prod, map_add, map_mul, map_X, map_intCast]

theorem radicand_map (φ : F →+* E) (c : F) (e : ℕ) (I J : Finset ℤ) :
    map φ (nativeRadicand c e I J) = nativeRadicand (φ c) e I J := by
  rw [nativeRadicand, map_mul, map_mul, map_mul, map_pow, map_C, map_X,
    linear_map, linear_map]
  rfl

theorem relation_map (φ : F →+* E) (c : F) (D : ℕ) (I J : Finset ℤ) (i : ι) :
    map φ (relation c D I J i) = relation (φ c) D I J i := by
  rw [relation, map_sub, map_pow, map_X, map_rename, radicand_map]
  rfl

theorem ideal_map (φ : F →+* E) (c : ι → F) (D : ℕ) (I J : ι → Finset ℤ) :
    (relationIdeal c D I J).map (map φ) = relationIdeal (fun i ↦ φ (c i)) D I J := by
  rw [relationIdeal, Ideal.map_span, ← Set.range_comp']
  congr 1
  exact congrArg Set.range (funext fun i ↦ relation_map φ (c i) D (I i) (J i) i)

end PaperP1.HomogeneousSplitRadicalScalarRelations
