module

public import PaperP1.Algebra.BoundedMomentLinearForm
public import Mathlib.FieldTheory.PrimitiveElement
public import Mathlib.FieldTheory.Perfect
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

/-! # A bounded integer linear combination of actual field generators is primitive -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BoundedPrimitiveLinearCombination

open Finset IntermediateField

def combination (K : Type*) [Field K] {L : Type*} [Field L] [Algebra K L] {n : ℕ}
    (u : Fin n → ℕ) (x : Fin n → L) : L := ∑ i, (u i : K) • x i

theorem difference_evaluation {K L Ω : Type*} [Field K] [Field L] [Field Ω]
    [Algebra K L] [Algebra K Ω] {n : ℕ} (u : Fin n → ℕ) (x : Fin n → L)
    (φ ψ : L →ₐ[K] Ω) :
    MvPolynomial.eval (fun i ↦ φ (x i) - ψ (x i))
      (CommonLinearNormalization.form (fun i ↦ (u i : Ω))) =
      φ (combination K u x) - ψ (combination K u x) := by
  classical
  rw [CommonLinearNormalization.evaluation, combination, map_sum, map_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _hi
  rw [map_smul, map_smul, Algebra.smul_def, Algebra.smul_def, map_natCast]
  ring

theorem exists_separating_coefficients (K L Ω : Type*) [Field K] [CharZero K] [Field L] [Field Ω]
    [Algebra K L] [Algebra K Ω] [FiniteDimensional K L] [IsAlgClosed Ω] [CharZero Ω]
    (n : ℕ) (x : Fin n → L) (hgen : Algebra.adjoin K (Set.range x) = ⊤) :
    ∃ u : Fin n → ℕ,
      (∀ i, u i ≤ ((n - 1) * (Module.finrank K L) ^ 2 + 1) ^ (n - 1)) ∧
      Function.Injective (fun φ : L →ₐ[K] Ω ↦ φ (combination K u x)) := by
  classical
  let T := (Finset.univ : Finset ((L →ₐ[K] Ω) × (L →ₐ[K] Ω))).filter (fun p ↦ p.1 ≠ p.2)
  let w (p : (L →ₐ[K] Ω) × (L →ₐ[K] Ω)) : Fin n → Ω := fun i ↦ p.1 (x i) - p.2 (x i)
  let S := T.image w
  have hnonzero : ∀ v ∈ S, v ≠ 0 := by
    intro v hv
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hv
    intro hz
    apply (Finset.mem_filter.mp hp).2
    apply AlgHom.ext_of_adjoin_eq_top hgen
    rintro _ ⟨i, rfl⟩
    exact sub_eq_zero.mp (congrFun hz i)
  have hcard : S.card ≤ (Module.finrank K L) ^ 2 := by
    calc
      _ ≤ T.card := Finset.card_image_le
      _ ≤ (Finset.univ : Finset ((L →ₐ[K] Ω) × (L →ₐ[K] Ω))).card := Finset.card_filter_le _ _
      _ = _ := by simp only [Finset.card_univ, Fintype.card_prod, AlgHom.card, pow_two]
  obtain ⟨u, hu, havoid⟩ := BoundedMomentLinearForm.exists_coefficients n S hnonzero
  refine ⟨u, ?_, ?_⟩
  · intro i
    apply (hu i).trans
    apply Nat.pow_le_pow_left
    exact Nat.add_le_add_right (Nat.mul_le_mul_left (n - 1) hcard) 1
  · intro φ ψ he
    by_contra hneq
    have hp : (φ, ψ) ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hneq⟩
    have hv : w (φ, ψ) ∈ S := Finset.mem_image.mpr ⟨(φ, ψ), hp, rfl⟩
    have hb := havoid (w (φ, ψ)) hv
    have heval : MvPolynomial.eval (w (φ, ψ))
        (CommonLinearNormalization.form (fun i ↦ (u i : Ω))) =
        φ (combination K u x) - ψ (combination K u x) := difference_evaluation u x φ ψ
    rw [heval] at hb
    exact hb (sub_eq_zero.mpr he)

theorem exists_primitive (K L : Type*) [Field K] [CharZero K] [Field L] [Algebra K L]
    [FiniteDimensional K L] (n : ℕ) (x : Fin n → L)
    (hgen : IntermediateField.adjoin K (Set.range x) = ⊤) :
    ∃ u : Fin n → ℕ,
      (∀ i, u i ≤ ((n - 1) * (Module.finrank K L) ^ 2 + 1) ^ (n - 1)) ∧
      K⟮combination K u x⟯ = ⊤ ∧
      (minpoly K (combination K u x)).natDegree = Module.finrank K L := by
  have hgenAlg : Algebra.adjoin K (Set.range x) = ⊤ := by
    rw [← IntermediateField.adjoin_toSubalgebra, hgen]
    rfl
  obtain ⟨u, hu, hsep⟩ := exists_separating_coefficients K L (AlgebraicClosure K) n x hgenAlg
  have hprimitive : K⟮combination K u x⟯ = ⊤ :=
    (Field.primitive_element_iff_algHom_eq_of_eval' K (AlgebraicClosure K)
      (fun _ ↦ IsAlgClosed.splits _) (combination K u x)).mpr hsep
  exact ⟨u, hu, hprimitive, (Field.primitive_element_iff_minpoly_natDegree_eq K _).mp hprimitive⟩

end PaperP1.BoundedPrimitiveLinearCombination
