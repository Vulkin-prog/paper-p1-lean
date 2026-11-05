module

public import PaperP1.Arithmetic.PhysicalWindowRelations
public import PaperP1.Coding.DisjointRecoveryTheorem
public import PaperP1.Coding.RecoveryImage
public import PaperP1.Analysis.SmallRecoveryParameter

/-! # An effective relation with injective projections has a regularized physical lift

Every fixed arity has an independently chosen recovery order.
Local window kernels are removed by choosing a section, before regularization.
The fixed recovery order precedes every physical window and every chosen lift.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FixedArityPhysicalRelationRegularization

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.PhysicalWindowRelations

local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) :
    AddCommGroup S := Submodule.addCommGroup (R := F₂) (M := U) S
local instance {U : Type*} [AddCommGroup U] [Module F₂ U] (S : Submodule F₂ U) : Module F₂ S := S.module
local instance codeAddCommGroup {ι : Type*} [Fintype ι] (X : ι → ℕ) (L : ℕ) : AddCommGroup (code X L) := by
  with_unfolding_all exact Submodule.addCommGroup (R := F₂) (M := ((ι × Fin (L + 1)) → F₂)) (code X L)
local instance effectiveAddCommGroup {ι : Type*} [Fintype ι] (X : ι → ℕ) (L : ℕ) :
    AddCommGroup (EffectiveKernel X L) := by
  with_unfolding_all
    exact Submodule.addCommGroup (R := F₂) (M := (i : ι) → squareClassSpace (X i) L) (EffectiveKernel X L)
local instance physicalAddCommGroup {ι : Type*} [Fintype ι] (X : ι → ℕ) (L : ℕ)
    (M : Submodule F₂ (code X L)) : AddCommGroup M := by
  with_unfolding_all exact Submodule.addCommGroup (R := F₂) (M := code X L) M

theorem uniform_subspace (d : ℕ) (hd : 1 ≤ d) (η : ℝ) (hη : 0 < η) :
    ∃ t : ℕ, 2 ≤ t ∧ ∀ (ι : Type*) [Fintype ι] [DecidableEq ι], Fintype.card ι ≤ d + 1 →
      ∀ (X : ι → ℕ) (L : ℕ), 1 ≤ L →
      (∀ i, Function.Injective (effectiveProjection X L i)) →
      ∃ M : Submodule F₂ (code X L),
        DisjointRecoverySubspace.NoDisjointRecovery (CoordinateForms.coordinateFamily (code X L)) M d t ∧
        (Module.finrank F₂ (EffectiveKernel X L) : ℝ) - η * L / 4 ≤ Module.finrank F₂ M ∧
        ∀ i, Function.Injective ((projection X L i).comp M.subtype) := by
  obtain ⟨t, ht, hcost⟩ := SmallRecoveryParameter.exists_relative_cost d hd η hη
  refine ⟨t, ht, ?_⟩
  intro ι _ _ hι X L hL hinj
  classical
  obtain ⟨σ, hσ⟩ := (toEffective X L).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr (toEffective_surjective X L))
  have hσfun (r : EffectiveKernel X L) : toEffective X L (σ r) = r := LinearMap.congr_fun hσ r
  have hσinj : Function.Injective σ := by
    intro r s he
    exact (hσfun r).symm.trans ((congrArg (toEffective X L) he).trans (hσfun s))
  let : FiniteDimensional F₂ (EffectiveKernel X L) := FiniteDimensional.of_injective σ hσinj
  have hproj (i : ι) : Function.Injective ((projection X L i).comp σ) := by
    intro r s he
    apply hinj i
    have hsel : localSelection X L i (σ r) = localSelection X L i (σ s) := by
      apply Subtype.ext
      exact he
    have hval := congrArg ((evenSquareClassMap (X i) L).rangeRestrict) hsel
    change effectiveProjection X L i (toEffective X L (σ r)) =
      effectiveProjection X L i (toEffective X L (σ s)) at hval
    simpa only [hσfun] using hval
  let ℓ := fun v ↦ (CoordinateForms.coordinateFamily (code X L) v).comp σ
  obtain ⟨P, hP⟩ := DisjointRecoveryTheorem.disjoint_recovery_sharp ℓ d t hd ht
  let M := P.map σ
  have hdim : Module.finrank F₂ M = Module.finrank F₂ P := RecoveryImage.finrank_image σ hσinj P
  have hcard : Fintype.card (ι × Fin (L + 1)) ≤ (d + 1) * (L + 1) := by
    rw [Fintype.card_prod, Fintype.card_fin]
    exact Nat.mul_le_mul_right _ hι
  have hbudget : 2 * (Fintype.card (ι × Fin (L + 1)) : ℝ) *
      DisjointRecoveryParameters.parameter d t ≤ η * L / 4 := by
    have hcardR : (Fintype.card (ι × Fin (L + 1)) : ℝ) ≤ (((d + 1) * (L + 1) : ℕ) : ℝ) := by
      exact_mod_cast hcard
    calc
      _ ≤ 2 * (((d + 1) * (L + 1) : ℕ) : ℝ) * DisjointRecoveryParameters.parameter d t :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcardR (by norm_num))
          (DisjointRecoveryParameters.parameter_pos d t ht).le
      _ ≤ _ := hcost L hL
  have hcodim := hP.1
  rw [Nat.cast_sub (Submodule.finrank_le P)] at hcodim
  refine ⟨M, RecoveryImage.no_recovery_image σ hσinj _ P d t hP.2.1, ?_, ?_⟩
  · rw [hdim]
    linarith only [hcodim, hbudget]
  · intro i
    exact RecoveryImage.projection_image_injective σ hσinj P
      ((projection X L i).comp σ) (projection X L i) rfl (hproj i)

end PaperP1.FixedArityPhysicalRelationRegularization
