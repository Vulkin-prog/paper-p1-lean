module

public import PaperP1.Affine.FamilyConditionalMass

/-! # Merging linear character systems can only increase the conditional relation kernel -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FactorConditionalKernel

open Finset PaperP1.Affine

local instance factorConditionalKernelTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

variable {V W ι β : Type*} [AddCommGroup V] [Module 𝔽₂ V] [Fintype V]
  [AddCommGroup W] [Module 𝔽₂ W] [Fintype W] [Fintype ι] [Fintype β]

omit [Fintype V] [Fintype W] [Fintype ι] in
theorem oldSpace_map_le (A : Option ι → V →ₗ[𝔽₂] (β → 𝔽₂))
    (B : Option ι → W →ₗ[𝔽₂] (β → 𝔽₂))
    (D : Module.Dual 𝔽₂ V →ₗ[𝔽₂] Module.Dual 𝔽₂ W)
    (hfactor : ∀ i, relationMap (B i) = D.comp (relationMap (A i))) :
    Submodule.map D (FamilyConditionalMass.oldSpace A) ≤ FamilyConditionalMass.oldSpace B := by
  rw [FamilyConditionalMass.oldSpace, Submodule.map_iSup]
  apply iSup_le
  intro i
  change Submodule.map D (LinearMap.range (relationMap (A (some i)))) ≤ _
  rw [← LinearMap.range_comp, ← hfactor (some i)]
  exact le_iSup (fun j ↦ effectiveRowSpace (B (some j))) i

omit [Fintype V] [Fintype W] [Fintype ι] in
theorem conditional_kernel_le (A : Option ι → V →ₗ[𝔽₂] (β → 𝔽₂))
    (B : Option ι → W →ₗ[𝔽₂] (β → 𝔽₂))
    (D : Module.Dual 𝔽₂ V →ₗ[𝔽₂] Module.Dual 𝔽₂ W)
    (hfactor : ∀ i, relationMap (B i) = D.comp (relationMap (A i))) :
    (FamilyConditionalMass.oldSpace A).comap (relationMap (A none)) ≤
      (FamilyConditionalMass.oldSpace B).comap (relationMap (B none)) := by
  intro u hu
  have hm : D (relationMap (A none) u) ∈ Submodule.map D (FamilyConditionalMass.oldSpace A) :=
    ⟨relationMap (A none) u, hu, rfl⟩
  have h := oldSpace_map_le A B D hfactor hm
  change (D.comp (relationMap (A none))) u ∈ FamilyConditionalMass.oldSpace B at h
  rw [← hfactor none] at h
  exact h

omit [Fintype ι] in
theorem mass_le_merged_homogeneous (A : Option ι → V →ₗ[𝔽₂] (β → 𝔽₂))
    (B : Option ι → W →ₗ[𝔽₂] (β → 𝔽₂))
    (D : Module.Dual 𝔽₂ V →ₗ[𝔽₂] Module.Dual 𝔽₂ W)
    (hfactor : ∀ i, relationMap (B i) = D.comp (relationMap (A i))) (a : V) (b : β → 𝔽₂) :
    FamilyConditionalMass.mass A a b ≤ FamilyConditionalMass.mass B 0 0 := by
  have hkernel := Submodule.finrank_mono (conditional_kernel_le A B D hfactor)
  have hzero : effectiveEvent (FamilyConditionalMass.oldSpace B) (0 : W) 0 ∧ B none 0 = 0 :=
    ⟨fun _ ↦ rfl, map_zero _⟩
  have hhom := conditionalAffineMass_of_witness (FamilyConditionalMass.oldSpace B) 0 (B none) 0 0 hzero
  change FamilyConditionalMass.mass B 0 0 = _ at hhom
  rw [hhom]
  rcases conditionalAffineMass_zero_or_pow (FamilyConditionalMass.oldSpace A) a (A none) b with hz | hq
  · change FamilyConditionalMass.mass A a b = 0 at hz
    rw [hz]
    positivity
  · change FamilyConditionalMass.mass A a b = _ at hq
    rw [hq]
    exact div_le_div_of_nonneg_right (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hkernel) (by positivity)

end PaperP1.FactorConditionalKernel
