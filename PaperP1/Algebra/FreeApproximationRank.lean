module

public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.Dimension.Localization
public import Mathlib.RingTheory.Finiteness.Basic

/-! # The size of an independent free approximation is the actual module and fraction-field rank -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FreeApproximationRank

open Finset Module

variable {A B ι : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [Fintype ι] (v : ι → B)

theorem finite_of_span (hgen : Submodule.span A (Set.range v) = ⊤) : Module.Finite A B := by
  have : Module.Finite A (Submodule.span A (Set.range v)) :=
    Module.Finite.span_of_finite A (Set.finite_range v)
  rw [hgen] at this
  exact Module.Finite.of_surjective (⊤ : Submodule A B).subtype (fun b ↦ ⟨⟨b, trivial⟩, rfl⟩)

theorem finrank_eq [Module.Finite A B] [IsDomain A] [IsDomain B]
    (hinj : Function.Injective (algebraMap A B)) (hli : LinearIndependent A v)
    (q : A) (hq : q ≠ 0) (hclear : ∀ b : B, q • b ∈ Submodule.span A (Set.range v)) :
    Module.finrank A B = Fintype.card ι := by
  let S := Submodule.span A (Set.range v)
  have hS : Module.finrank A S = Fintype.card ι := Module.finrank_eq_card_basis (Basis.span hli)
  have : Module.Finite A S := Module.Finite.of_basis (Basis.span hli)
  let u : B →ₗ[A] S := (LinearMap.lsmul A B q).codRestrict S hclear
  have hu : Function.Injective u := by
    intro a b hab
    have he : q • a = q • b := congrArg Subtype.val hab
    simp only [Algebra.smul_def] at he
    exact mul_left_cancel₀ (fun h ↦ hq (hinj (h.trans (map_zero (algebraMap A B)).symm))) he
  apply Nat.le_antisymm
  · exact (LinearMap.finrank_le_finrank_of_injective hu).trans_eq hS
  · exact hS.symm.trans_le S.finrank_le

theorem fraction_finrank_eq
    (K L : Type*) [CommRing K] [CommRing L] [Module K L]
    [Algebra A K] [Algebra B L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L]
    [IsFractionRing A K] [IsFractionRing B L]
    [Module.Finite A B] [IsDomain A] [IsDomain B]
    (hinj : Function.Injective (algebraMap A B)) (hli : LinearIndependent A v)
    (q : A) (hq : q ≠ 0) (hclear : ∀ b : B, q • b ∈ Submodule.span A (Set.range v)) :
    Module.finrank K L = Fintype.card ι :=
  (IsFractionRing.finrank_eq A K B L).trans (finrank_eq v hinj hli q hq hclear)

end PaperP1.FreeApproximationRank
