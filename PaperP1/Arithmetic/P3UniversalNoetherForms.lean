module

public import PaperP1.Algebra.P3CoefficientFieldTransport
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # An explicit finite universal-form proposition for geometric irreducibility

The forms are actual integer polynomials in the actual homogeneous coefficients.
Their existence in EVERY degree is proved in
`PaperP1.Arithmetic.P3UniversalNoetherFormsExistence` from the actual proper
projective factor loci and coefficient-preserving field-point lifts.
This file defines the exact property; no axiom is introduced.
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
