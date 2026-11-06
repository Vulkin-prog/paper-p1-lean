module

public import PaperP1.Algebra.P3CoefficientFieldTransport
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # An explicit finite universal-form proposition for geometric irreducibility

The existence of these universal forms in general degree is an UNPROVED INPUT.
The forms are actual integer polynomials in the actual homogeneous coefficients.
No axiom is introduced.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3UniversalNoetherForms

open MvPolynomial P3HomogeneousCoefficientFamily

def Valid (d : ℕ) (forms : Finset (MvPolynomial (Index d) ℤ)) : Prop :=
  ∀ (F : Type) [Field F] (a : Index d → F),
    Irreducible (map (algebraMap F (AlgebraicClosure F)) (polynomial d a)) ↔
      ∃ Φ ∈ forms, eval a (map (Int.castRingHom F) Φ) ≠ 0

def ExistsForms (d : ℕ) : Prop := ∃ forms : Finset (MvPolynomial (Index d) ℤ), Valid d forms

end PaperP1.P3UniversalNoetherForms
