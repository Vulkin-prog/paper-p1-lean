/-
Adapted from Vulkin-prog/paper-c-lean, PaperCV282/PrescribedValues.lean,
commit b9fa9ba490f201b408a302a86f1594ee620b228b, Apache-2.0,
Git blob 625c4f842089815294ca062396f80694980d449f.
Only the raw value system and prime-basis identities are ported here.
The original affine probability/error interfaces are not assumed.
-/
module

public import PaperP1.Model.FiniteRademacher

/-! # Actual raw-value words and their private prime coordinates -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrivateValueSystem

open PaperP1.Arithmetic PaperP1.Model

variable {ι : Type*}

def valueSystem (M : ℕ) (v : ι → ℕ) : SampleSpace M →ₗ[F₂] (ι → F₂) :=
  LinearMap.pi fun i ↦ valueLinear M (v i)

@[simp]
theorem valueSystem_apply (M : ℕ) (v : ι → ℕ) (ω : SampleSpace M) (i : ι) :
    valueSystem M v ω i = valueBit ω (v i) := rfl

theorem valueSystem_eq_iff (M : ℕ) (v : ι → ℕ) (b : ι → F₂) (ω : SampleSpace M) :
    valueSystem M v ω = b ↔ ∀ i, valueBit ω (v i) = b i := funext_iff

theorem valueBit_prime_basis (M n : ℕ) (p : PrimeUpTo M) :
    valueBit (Pi.single p 1 : SampleSpace M) n = parityVec n p.val.val := by
  classical
  rw [valueBit, Fintype.sum_eq_single p]
  · simp
  · intro q hq
    simp [hq]

theorem valueSystem_prime_basis [DecidableEq ι] (M : ℕ) (v : ι → ℕ) (i : ι)
    (p : PrimeUpTo M) (hdiag : parityVec (v i) p.val.val = 1)
    (hoff : ∀ j, j ≠ i → parityVec (v j) p.val.val = 0) :
    valueSystem M v (Pi.single p 1) = Pi.single i 1 := by
  funext j
  rw [valueSystem_apply, valueBit_prime_basis]
  by_cases hji : j = i
  · subst j
    simpa using hdiag
  · simp [hji, hoff j hji]

end PaperP1.PrivateValueSystem
