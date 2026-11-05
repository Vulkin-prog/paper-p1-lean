module

public import PaperP1.Algebra.BoundedPrimitiveLinearCombination
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-! # Original algebra coordinates generate the actual fraction field and admit a bounded primitive form -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CoordinateFractionFieldGenerators

open MvPolynomial

theorem quotient_variables_generate {F σ : Type*} [Field F] (I : Ideal (MvPolynomial σ F)) :
    Algebra.adjoin F (Set.range (fun i : σ ↦ Ideal.Quotient.mk I (X i))) = ⊤ := by
  let q := Ideal.Quotient.mkₐ F I
  have he : aeval (R := F) (fun i : σ ↦ Ideal.Quotient.mk I (X i)) = q := by
    apply MvPolynomial.algHom_ext
    intro i
    exact aeval_X _ i
  rw [← MvPolynomial.aeval_range, he]
  exact (AlgHom.range_eq_top q).mpr (Ideal.Quotient.mkₐ_surjective F I)

theorem fraction_field_generated {F A K L ι : Type*} [Field F] [CommRing A] [IsDomain A]
    [Field K] [Field L] [Algebra F A] [Algebra A L] [Algebra F L] [IsScalarTower F A L]
    [Algebra F K] [Algebra K L] [IsScalarTower F K L] [IsFractionRing A L]
    (x : ι → A) (hgen : Algebra.adjoin F (Set.range x) = ⊤) :
    IntermediateField.adjoin K (Set.range (fun i ↦ algebraMap A L (x i))) = ⊤ := by
  let T := IntermediateField.adjoin K (Set.range (fun i ↦ algebraMap A L (x i)))
  have himage (a : A) : algebraMap A L a ∈ T := by
    have ha : a ∈ Algebra.adjoin F (Set.range x) := by rw [hgen]; trivial
    induction ha using Algebra.adjoin_induction with
    | mem a ha =>
      obtain ⟨i, rfl⟩ := ha
      exact IntermediateField.subset_adjoin K _ ⟨i, rfl⟩
    | algebraMap r =>
      rw [← IsScalarTower.algebraMap_apply F A L, IsScalarTower.algebraMap_apply F K L]
      exact T.algebraMap_mem (algebraMap F K r)
    | add a b _ha _hb ha hb =>
      rw [map_add]
      exact T.add_mem ha hb
    | mul a b _ha _hb ha hb =>
      rw [map_mul]
      exact T.mul_mem ha hb
  apply top_unique
  intro z _hz
  obtain ⟨a, b, _hb, rfl⟩ := IsFractionRing.div_surjective A z
  exact T.div_mem (himage a) (himage b)

theorem coordinate_evaluation {F A K L : Type*} [Field F] [CommRing A] [Field K] [Field L]
    [Algebra F A] [Algebra A L] [Algebra K L] {n : ℕ} (u : Fin n → ℕ) (x : Fin n → A) :
    algebraMap A L (MvPolynomial.aeval x (CommonLinearNormalization.form (fun i ↦ (u i : F)))) =
      BoundedPrimitiveLinearCombination.combination K u (fun i ↦ algebraMap A L (x i)) := by
  classical
  simp only [CommonLinearNormalization.form, BoundedPrimitiveLinearCombination.combination,
    map_sum, map_mul, aeval_X, Algebra.smul_def, map_natCast]

theorem bounded_primitive {F A K L : Type*} [Field F] [CommRing A] [IsDomain A]
    [Field K] [CharZero K] [Field L] [Algebra F A] [Algebra A L] [Algebra F L] [IsScalarTower F A L]
    [Algebra F K] [Algebra K L] [IsScalarTower F K L] [IsFractionRing A L] [FiniteDimensional K L]
    (n : ℕ) (x : Fin n → A) (hgen : Algebra.adjoin F (Set.range x) = ⊤) :
    ∃ u : Fin n → ℕ,
      (∀ i, u i ≤ ((n - 1) * (Module.finrank K L) ^ 2 + 1) ^ (n - 1)) ∧
      IntermediateField.adjoin K
        {algebraMap A L (MvPolynomial.aeval x
          (CommonLinearNormalization.form (fun i ↦ (u i : F))))} = ⊤ ∧
      (minpoly K (algebraMap A L (MvPolynomial.aeval x
        (CommonLinearNormalization.form (fun i ↦ (u i : F)))))).natDegree = Module.finrank K L := by
  obtain ⟨u, hu, hprimitive, hdegree⟩ := BoundedPrimitiveLinearCombination.exists_primitive
    K L n _ (fraction_field_generated x hgen)
  refine ⟨u, hu, ?_, ?_⟩
  · rw [coordinate_evaluation (K := K)]
    exact hprimitive
  · rw [coordinate_evaluation (K := K)]
    exact hdegree

end PaperP1.CoordinateFractionFieldGenerators
