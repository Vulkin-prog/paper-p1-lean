module

public import PaperP1.Algebra.RegularSurfaceHilbertSection
public import PaperP1.Algebra.SourceVeroneseHilbertPolynomial

/-! # Every actual nonzero homogeneous source-surface section has genuine Hilbert degree e 2^k D² -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SourceSurfaceSectionHilbert

open HomogeneousSplitRadicalData HomogeneousSplitRadicalVeronese SourceVeroneseGrading

local instance polynomialRing (F : Type*) [Field F] : CommRing (PolynomialRing F) := inferInstance

theorem exists_linear_hilbert {F : Type*} [Field F] [CharZero F]
    (s : List (PolynomialRing F)) (c : Fin s.length → F) (D : ℕ) (hD : 0 < D)
    (I J : Fin s.length → Finset ℤ)
    (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i))
    (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D)
    (hc : ∀ i, c i ≠ 0) (hne : ∀ i, (I i).Nonempty ∨ (J i).Nonempty)
    (hI : Pairwise fun i j ↦ Disjoint (I i) (I j))
    (hJ : Pairwise fun i j ↦ Disjoint (J i) (J j))
    (e : ℕ) (f : veronese c D I J) (hf : f ∈ sourcePiece c D I J e) (hf0 : f ≠ 0) :
    ∃ b : ℚ, GradedHilbertPolynomial.IsHilbertPolynomial (HomogeneousPrincipalQuotient.piece
      (sourcePiece c D I J) f) (Polynomial.C ((e * (2 ^ s.length * D ^ 2) : ℕ) : ℚ) *
        Polynomial.X + Polynomial.C b) := by
  let := sourceGrading c D I J hdeg hD
  let := source_isDomain s c D I J hs hc hne hI hJ
  let (n : ℕ) : Module.Finite F (sourcePiece c D I J n) :=
    SourceVeroneseHilbert.piece_finite_all s c D I J hdeg hs hD n
  let p := SourceVeroneseHilbertPolynomial.polynomial s c D I J hdeg
  have hcoeff : p.coeff 2 = ((2 ^ s.length * D ^ 2 : ℕ) : ℚ) / 2 := by
    rw [SourceVeroneseHilbertPolynomial.coeff_two]
    push_cast
    rfl
  exact ⟨(e : ℚ) * p.coeff 1 - (e : ℚ) ^ 2 * p.coeff 2,
    RegularSurfaceHilbertSection.linear_hilbert (sourcePiece c D I J) p
      (SourceVeroneseHilbertPolynomial.natDegree_le s c D I J hdeg)
      (SourceVeroneseHilbertPolynomial.isHilbertPolynomial s c D I J hdeg hs hD)
      (2 ^ s.length * D ^ 2) hcoeff hf (fun _ _ he ↦ mul_right_cancel₀ hf0 he)⟩

end PaperP1.SourceSurfaceSectionHilbert
