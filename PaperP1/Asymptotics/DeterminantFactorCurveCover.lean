module

public import PaperP1.Arithmetic.IntegerFactorProjectiveCurve
public import PaperP1.Asymptotics.DeterminantFactorHeight

/-! # A uniformly bounded family of actual integer factor curves covers every source point -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DeterminantFactorCurveCover

open Finset Polynomial PaperP1.BivariateDegrees PaperP1.BivariateHeight
  PaperP1.BivariateEvaluation PaperP1.TwoKernelDeterminantBoxes PaperP1.IntegerFactorProjectiveCurve
  PaperP1.DeterminantIntegerRows PaperP1.DeterminantAuxiliaryBiform
  PaperP1.BiquadraticCoefficientPolynomials

def zeros (F : ℤ[X][X]) (S : Finset Quad) : Finset Quad :=
  S.filter (fun p ↦ evaluate ((p.1.1 : ℚ) / p.1.2) ((p.2.2 : ℚ) / p.2.1) F = 0)

theorem finite_rational_cover (F : ℤ[X][X]) (hF : F ≠ 0) :
    ∃ T : Finset ℤ[X][X], T.card ≤ degreeX F + degreeY F ∧
      (∀ G ∈ T, Irreducible G ∧ G ∣ F ∧ 0 < degreeX G + degreeY G ∧
        degreeX G ≤ degreeX F ∧ degreeY G ≤ degreeY F) ∧
      ∀ x y : ℚ, evaluate x y F = 0 → ∃ G ∈ T, evaluate x y G = 0 := by
  obtain ⟨T, hT, hfactors, hcover⟩ := IntegerBivariateFactorCover.exists_finite_cover F hF
  refine ⟨T, hT, ?_, hcover⟩
  intro G hG
  have h := hfactors G hG
  have hd := IrreduciblePointFactor.factor_partial_degrees F G hF h.2.1
  exact ⟨h.1, h.2.1, h.2.2, hd⟩

theorem population_sum_bound (T : Finset ℤ[X][X]) (S : Finset Quad)
    (hcover : ∀ p ∈ S, ∃ G ∈ T, evaluate ((p.1.1 : ℚ) / p.1.2) ((p.2.2 : ℚ) / p.2.1) G = 0) :
    S.card ≤ ∑ G ∈ T, (zeros G S).card := by
  calc
    _ ≤ (T.biUnion (fun G ↦ zeros G S)).card := by
      apply card_le_card
      intro p hp
      obtain ⟨G, hG, hz⟩ := hcover p hp
      exact mem_biUnion.mpr ⟨G, hG, mem_filter.mpr ⟨hp, hz⟩⟩
    _ ≤ _ := card_biUnion_le

theorem uniform_bounded_projective_cover (Amax B κ : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ F : ℤ[X][X], F ≠ 0 → degreeX F ≤ Amax → degreeY F ≤ B →
      height F ≤ N ^ κ → ∀ S : Finset Quad,
      (∀ p ∈ S, 0 < p.1.2) → (∀ p ∈ S, 0 < p.2.1) →
      (∀ p ∈ S, evaluate ((p.1.1 : ℚ) / p.1.2) ((p.2.2 : ℚ) / p.2.1) F = 0) →
      ∃ T : Finset ℤ[X][X], T.card ≤ Amax + B ∧
        (∀ G ∈ T, Irreducible G ∧ G ∣ F ∧ 0 < degreeX G + degreeY G ∧
          degreeX G ≤ Amax ∧ degreeY G ≤ B ∧ height G ≤ N ^ (κ + 1) ∧
          projective G ≠ 0 ∧
          (∀ m n, |((projective G).coeff m).coeff n| ≤ ((N ^ (κ + 1) : ℕ) : ℤ))) ∧
        (∀ p ∈ S, ∃ G ∈ T,
          MvPolynomial.eval₂ (MvPolynomial.eval ![(p.2.2 : ℤ), p.2.1]) ![(p.1.1 : ℤ), p.1.2]
            (projective G) = 0) ∧ S.card ≤ ∑ G ∈ T, (zeros G S).card := by
  obtain ⟨N₀, hheight⟩ := DeterminantFactorHeight.uniform_factor_height Amax B κ
  refine ⟨N₀, ?_⟩
  intro N hN F hF hx hy hH S he hu hzero
  obtain ⟨T, hT, hfactors, hcover⟩ := finite_rational_cover F hF
  have hactual (p : Quad) (hp : p ∈ S) :
      ∃ G ∈ T, evaluate ((p.1.1 : ℚ) / p.1.2) ((p.2.2 : ℚ) / p.2.1) G = 0 :=
    hcover _ _ (hzero p hp)
  refine ⟨T, hT.trans (Nat.add_le_add hx hy), ?_, ?_, population_sum_bound T S hactual⟩
  · intro G hG
    have hg := hfactors G hG
    obtain ⟨hh, hdx, hdy⟩ := hheight N hN F G hF hg.2.1 hx hy hH
    refine ⟨hg.1, hg.2.1, hg.2.2.1, hdx, hdy, hh, projective_nonzero G hg.1.ne_zero, ?_⟩
    intro m n
    exact (projective_height G m n).trans (by exact_mod_cast hh)
  · intro p hp
    obtain ⟨G, hG, hz⟩ := hactual p hp
    exact ⟨G, hG, (projective_zero_iff G p (he p hp) (hu p hp)).mpr hz⟩

theorem affine_of_biform (A B H : ℕ) (w : Exponent A B → ℤ) (hw : biform A B w ≠ 0)
    (hheight : ∀ m n, |((biform A B w).coeff m).coeff n| ≤ (H : ℤ))
    (S : Finset Quad) (he : ∀ p ∈ S, 0 < p.1.2) (hu : ∀ p ∈ S, 0 < p.2.1)
    (hzero : ∀ p ∈ S, MvPolynomial.eval₂ (MvPolynomial.eval ![(p.2.2 : ℤ), p.2.1])
      ![(p.1.1 : ℤ), p.1.2] (biform A B w) = 0) :
    ∃ F : ℤ[X][X], F ≠ 0 ∧ degreeX F ≤ A ∧ degreeY F ≤ B ∧ height F ≤ H ∧
      ∀ p ∈ S, evaluate ((p.1.1 : ℚ) / p.1.2) ((p.2.2 : ℚ) / p.2.1) F = 0 := by
  have hw₀ : w ≠ 0 := fun h ↦ hw ((BiformCoefficientRecovery.biform_zero_iff A B w).mpr h)
  have hcoeff := BiformCoefficientRecovery.coefficient_bound_from_biform A B H w hheight
  refine ⟨rectangle A B w, DeterminantAuxiliaryPolynomial.rectangle_ne_zero A B w hw₀,
    rectangle_degreeX A B w, rectangle_degreeY A B w,
    DeterminantAuxiliaryPolynomial.rectangle_height_le A B H w hcoeff, ?_⟩
  intro p hp
  exact (rectangle_zero_iff A B w p (he p hp) (hu p hp)).mp (hzero p hp)

end PaperP1.DeterminantFactorCurveCover
