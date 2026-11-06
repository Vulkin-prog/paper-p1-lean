module

public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.Polynomial.UniqueFactorization

/-! # Exact primality and irreducibility under an injective extension of polynomial variables -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IrreducibleVariableExtension

open MvPolynomial

theorem prime_rename {R σ τ : Type*} [CommRing R] (f : σ → τ) (hf : Function.Injective f)
    (P : MvPolynomial σ R) : Prime (rename f P) ↔ Prime P := by
  let e : σ ≃ Set.range f := Equiv.ofInjective f hf
  have he : rename f P = rename (Subtype.val : Set.range f → τ) (renameEquiv R e P) := by
    simp only [renameEquiv_apply, rename_rename]
    rfl
  rw [he, MvPolynomial.prime_rename_iff]
  exact MulEquiv.prime_iff (renameEquiv R e)

theorem irreducible_rename {F σ τ : Type*} [Field F] (f : σ → τ) (hf : Function.Injective f)
    (P : MvPolynomial σ F) : Irreducible (rename f P) ↔ Irreducible P := by
  rw [irreducible_iff_prime, irreducible_iff_prime]
  exact prime_rename f hf P

end PaperP1.IrreducibleVariableExtension
