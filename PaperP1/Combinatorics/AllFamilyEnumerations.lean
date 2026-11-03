module

public import PaperP1.Combinatorics.FiniteFamilyEnumeration
public import Mathlib.Data.Fintype.Perm

/-! # Counting all permutations of each actual finite family recovers the exact factorial divisor -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AllFamilyEnumerations

open Finset PaperP1.FiniteFamilyEnumeration

theorem tupleSet_comp_perm {r : ℕ} (n : Fin r → ℕ) (σ : Equiv.Perm (Fin r)) :
    tupleSet (n ∘ σ) = tupleSet n := by
  ext x
  simp only [tupleSet, mem_image, mem_univ, true_and, Function.comp_apply]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨σ i, hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨σ.symm i, by simpa only [σ.apply_symm_apply] using hi⟩

theorem factorial_count_le {r : ℕ} (F : Finset (Finset ℕ)) (P : Finset (Fin r → ℕ))
    (hF : ∀ I ∈ F, I.card = r)
    (hP : ∀ I ∈ F, ∀ n : Fin r → ℕ, Function.Injective n → tupleSet n = I → n ∈ P) :
    F.card * r.factorial ≤ P.card := by
  classical
  let n := fun I : F ↦ centres I.val (hF I.val I.property)
  have hn (I : F) : Function.Injective (n I) := centres_injective I.val (hF I.val I.property)
  have hset (I : F) (σ : Equiv.Perm (Fin r)) : tupleSet (n I ∘ σ) = I.val :=
    (tupleSet_comp_perm (n I) σ).trans (centres_tupleSet I.val (hF I.val I.property))
  let f : F × Equiv.Perm (Fin r) → P := fun v ↦
    ⟨n v.1 ∘ v.2, hP v.1.val v.1.property _ ((hn v.1).comp v.2.injective) (hset v.1 v.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨I, σ⟩ ⟨J, τ⟩ heq
    have hfun : n I ∘ σ = n J ∘ τ := congrArg Subtype.val heq
    have hvalues := congrArg tupleSet hfun
    rw [hset I σ, hset J τ] at hvalues
    have hIJ : I = J := Subtype.ext hvalues
    subst J
    have hστ : σ = τ := by
      apply Equiv.ext
      intro i
      exact hn I (congrFun hfun i)
    exact congrArg (fun π ↦ (I, π)) hστ
  have h := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_prod, Fintype.card_coe, Fintype.card_perm, Fintype.card_fin] using h

end PaperP1.AllFamilyEnumerations
