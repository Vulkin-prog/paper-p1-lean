module

public import PaperP1.Combinatorics.AllFamilyEnumerations

/-! # The exact factorial cardinality of injective lists representing an actual family population -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FamilyEnumerationUpper

open Finset PaperP1.FiniteFamilyEnumeration

theorem tupleSet_card {r : ℕ} (n : Fin r → ℕ) (hinj : Function.Injective n) : (tupleSet n).card = r := by
  rw [tupleSet, card_image_of_injective _ hinj, card_univ, Fintype.card_fin]

theorem factorial_count_ge {r : ℕ} (F : Finset (Finset ℕ)) (P : Finset (Fin r → ℕ))
    (hF : ∀ I ∈ F, I.card = r)
    (hP : ∀ n ∈ P, Function.Injective n ∧ tupleSet n ∈ F) :
    P.card ≤ F.card * r.factorial := by
  classical
  let I : P → F := fun z ↦ ⟨tupleSet z.val, (hP z.val z.property).2⟩
  let f (z : P) : Fin r → (I z).val := fun i ↦ ⟨z.val i, mem_image.mpr ⟨i, mem_univ _, rfl⟩⟩
  have hf (z : P) : Function.Bijective (f z) := by
    refine ⟨fun i j heq ↦ (hP z.val z.property).1 (congrArg Subtype.val heq), ?_⟩
    intro x
    obtain ⟨j, _, hj⟩ := mem_image.mp x.property
    exact ⟨j, Subtype.ext hj⟩
  let e (z : P) : Fin r ≃ (I z).val := Equiv.ofBijective (f z) (hf z)
  let σ (z : P) : Equiv.Perm (Fin r) := (e z).trans (enumeration (I z).val (hF (I z).val (I z).property)).symm
  let g : P → F × Equiv.Perm (Fin r) := fun z ↦ (I z, σ z)
  have hrec (z : P) (j : Fin r) : centres (I z).val (hF (I z).val (I z).property) (σ z j) = z.val j :=
    congrArg Subtype.val ((enumeration (I z).val (hF (I z).val (I z).property)).apply_symm_apply (e z j))
  have hg : Function.Injective g := by
    intro z w heq
    have hfun := congrArg
      (fun v : F × Equiv.Perm (Fin r) ↦ centres v.1.val (hF v.1.val v.1.property) ∘ v.2) heq
    apply Subtype.ext
    funext j
    exact (hrec z j).symm.trans ((congrFun hfun j).trans (hrec w j))
  have h := Fintype.card_le_of_injective g hg
  simpa only [Fintype.card_coe, Fintype.card_prod, Fintype.card_perm, Fintype.card_fin] using h

theorem factorial_count_eq {r : ℕ} (F : Finset (Finset ℕ)) (P : Finset (Fin r → ℕ))
    (hF : ∀ I ∈ F, I.card = r)
    (hP : ∀ n ∈ P, Function.Injective n ∧ tupleSet n ∈ F)
    (hcover : ∀ I ∈ F, ∀ n : Fin r → ℕ, Function.Injective n → tupleSet n = I → n ∈ P) :
    P.card = F.card * r.factorial :=
  le_antisymm (factorial_count_ge F P hF hP) (AllFamilyEnumerations.factorial_count_le F P hF hcover)

end PaperP1.FamilyEnumerationUpper
