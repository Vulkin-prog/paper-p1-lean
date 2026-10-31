module

public import PaperP1.Affine.RelativeNullity

/-!
# Monotonicity of effective relative nullity under inclusion

Extension by zero embeds the relation kernel of a subfamily in that of every
larger family. This is proved on the actual effective spaces, so it adds no
local relations a second time.
-/

@[expose] public noncomputable section

open scoped BigOperators

namespace PaperP1.Affine

local instance subfamilyPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

variable {U κ : Type*} [AddCommGroup U] [Module 𝔽₂ U] [DecidableEq κ]
variable (S : κ → Submodule 𝔽₂ U) [∀ i, Fintype (S i)]

def relativeNullityOn (I : Finset κ) : ℕ :=
  relativeNullity (fun i : I => S i.val)

def subfamilyExtend {I J : Finset κ} (_hsub : I ⊆ J) :
    ((i : I) → S i.val) →ₗ[𝔽₂] ((j : J) → S j.val) where
  toFun := fun s j => if hj : j.val ∈ I then s ⟨j.val, hj⟩ else 0
  map_add' := by
    intro s t
    funext j
    by_cases hj : j.val ∈ I <;> simp [hj]
  map_smul' := by
    intro a s
    funext j
    by_cases hj : j.val ∈ I <;> simp [hj]

omit [∀ i, Fintype (S i)] in
theorem subfamilyExtend_injective {I J : Finset κ} (hsub : I ⊆ J) :
    Function.Injective (subfamilyExtend S hsub) := by
  intro s t h
  funext i
  have hi := congrFun h (⟨i.val, hsub i.property⟩ : J)
  simpa [subfamilyExtend, i.property] using hi

omit [Module 𝔽₂ U] [∀ i, Fintype (S i)] [DecidableEq κ] in
theorem sum_finset_subtype (I : Finset κ) (f : κ → U) :
    (∑ i : I, f i.val) = ∑ i ∈ I, f i := by
  rw [Finset.univ_eq_attach]
  exact Finset.sum_attach I f

omit [∀ i, Fintype (S i)] in
theorem relationAddition_subfamilyExtend {I J : Finset κ} (hsub : I ⊆ J)
    (s : (i : I) → S i.val) :
    relationAddition (fun j : J => S j.val) (subfamilyExtend S hsub s) =
      relationAddition (fun i : I => S i.val) s := by
  let f : κ → U := fun i => if hi : i ∈ I then (s ⟨i, hi⟩).val else 0
  change (∑ j : J, (subfamilyExtend S hsub s j).val) = ∑ i : I, (s i).val
  have hleft : (∑ j : J, (subfamilyExtend S hsub s j).val) = ∑ j ∈ J, f j := by
    rw [← sum_finset_subtype J f]
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j.val ∈ I <;> simp [subfamilyExtend, f, hj]
  have hright : (∑ i : I, (s i).val) = ∑ i ∈ I, f i := by
    rw [← sum_finset_subtype I f]
    apply Finset.sum_congr rfl
    intro i _
    simp [f, i.property]
  rw [hleft, hright]
  symm
  apply Finset.sum_subset hsub
  intro i _ hi
  simp [f, hi]

def subfamilyKernelExtend {I J : Finset κ} (hsub : I ⊆ J) :
    LinearMap.ker (relationAddition (fun i : I => S i.val)) →ₗ[𝔽₂]
      LinearMap.ker (relationAddition (fun j : J => S j.val)) :=
  ((subfamilyExtend S hsub).domRestrict
    (LinearMap.ker (relationAddition (fun i : I => S i.val)))).codRestrict
    (LinearMap.ker (relationAddition (fun j : J => S j.val))) (fun s => by
      change relationAddition (fun j : J => S j.val) (subfamilyExtend S hsub s.val) = 0
      rw [relationAddition_subfamilyExtend]
      exact s.property)

omit [∀ i, Fintype (S i)] in
theorem subfamilyKernelExtend_injective {I J : Finset κ} (hsub : I ⊆ J) :
    Function.Injective (subfamilyKernelExtend S hsub) := by
  intro s t h
  apply Subtype.ext
  exact subfamilyExtend_injective S hsub (congrArg Subtype.val h)

theorem relativeNullityOn_mono {I J : Finset κ} (hsub : I ⊆ J) :
    relativeNullityOn S I ≤ relativeNullityOn S J := by
  exact LinearMap.finrank_le_finrank_of_injective (f := subfamilyKernelExtend S hsub)
    (subfamilyKernelExtend_injective S hsub)

end PaperP1.Affine
