module

public import PaperP1.Geometry.SourceProjectiveCurveData
public import PaperP1.Arithmetic.SourceIntegerPoints
public import Mathlib.Analysis.Real.Sqrt

/-! # The explicit uniform covering input in the actual chosen weighted-source embedding

`UniformCover` is an UNPROVED ARGUMENT, not an axiom or an asserted surface
theorem. It includes Salberger's projective surface covering and its translation
through bounded finite projection, lifting, degree bounds and the actual source
prime/Hilbert presentation. The chosen source surface has the already proved
Hilbert multiplicity 2^k*D^2. The weaker decay 2^(-k/2) below suffices for D>=1.
The bounded finite projection, its fixed exceptional-curve family, and the
lifting of each individual actual image curve are proved in
`ActualSourceSurfaceProjectionExceptionalCurves` and `ActualSourceProjectedCurveCover`.
The primary surface theorem still required is Lemma 2 of
https://arxiv.org/pdf/2311.05561v1 . Its statement is in P3; the full uniform covering conclusion below
remains unproved. The completed projection and individual-curve lifting do not
by themselves provide the determinant-method covering family.
This property is distinct from the ordinary-embedding cover property.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UniformSourceSurfaceCover

open PaperP1.HomogeneousSplitRadicalData PaperP1.SourceProjectiveCurveData PaperP1.SourceIntegerPoints

local instance polynomialRing : CommRing (PolynomialRing ℚ) := inferInstance

def UniformCover (kmax K D : ℕ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ M : ℕ, ∃ A : ℝ, 0 < A ∧
    ∀ s : List (PolynomialRing ℚ), s.length ≤ kmax →
    ∀ (d : Fin s.length → ℤ) (I J : Fin s.length → Finset ℤ),
    ∀ (hs : ∀ i, s.get i = radicand (d i : ℚ) (2 * D - ((I i).card + (J i).card)) (I i) (J i))
      (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D) (hD : 0 < D),
      (∀ i, d i ≠ 0) → (Pairwise fun i j ↦ Disjoint (I i) (I j)) →
      (Pairwise fun i j ↦ Disjoint (J i) (J j)) → (∀ i, (I i).Nonempty) → (∀ i, (J i).Nonempty) →
      (∀ i, (I i).card + (J i).card ≤ K) →
    ∀ H : ℕ, 1 ≤ H → ∀ U : Finset (SourceProjectiveEmbedding.GeneratorIndex ℚ (Fin s.length) D → ℤ),
      U ⊆ curvePoints D (RingHom.ker
        (SourceProjectiveEmbedding.evaluation (fun i ↦ (d i : ℚ)) D I J hdeg hD).toRingHom) H →
      ∃ (V : Finset (SourceProjectiveEmbedding.GeneratorIndex ℚ (Fin s.length) D → ℤ))
        (curves : Finset (Curve s (fun i ↦ (d i : ℚ)) D I J hdeg hD)),
        (∀ Γ ∈ curves, degree s (fun i ↦ (d i : ℚ)) D I J hs hdeg hD Γ ≤ (M : ℚ)) ∧
        (V.card : ℝ) ≤ A * (H : ℝ) ^ (2 / Real.sqrt ((2 : ℝ) ^ s.length) + δ) ∧
        (curves.card : ℝ) ≤ A * (H : ℝ) ^ (1 / Real.sqrt ((2 : ℝ) ^ s.length) + δ) ∧
        ∀ v ∈ U, v ∉ V → ∃ Γ ∈ curves, v ∈ curvePoints D (ideal s (fun i ↦ (d i : ℚ)) D I J hdeg hD Γ) H

end PaperP1.UniformSourceSurfaceCover
