module

public import PaperP1.Arithmetic.IntegerPairFactorCharts
public import PaperP1.Asymptotics.DeterminantFactorCurveCover

/-! # Uniform integer factor curves on arbitrary signed affine-chart populations -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IntegerPairFactorCover

open Finset Polynomial PaperP1.BivariateDegrees PaperP1.BivariateHeight
open PaperP1.BivariateEvaluation PaperP1.IntegerFactorProjectiveCurve
open PaperP1.DeterminantIntegerRows PaperP1.DeterminantAuxiliaryBiform
open PaperP1.BiquadraticCoefficientPolynomials

def zeros (F : ℤ[X][X]) (S : Finset ((Fin 2 → ℤ) × (Fin 2 → ℤ))) :
    Finset ((Fin 2 → ℤ) × (Fin 2 → ℤ)) :=
  S.filter (fun p ↦ evaluate ((p.1 0 : ℚ) / p.1 1) ((p.2 0 : ℚ) / p.2 1) F = 0)

theorem population_sum_bound (T : Finset ℤ[X][X]) (S : Finset ((Fin 2 → ℤ) × (Fin 2 → ℤ)))
    (hcover : ∀ p ∈ S, ∃ G ∈ T, evaluate ((p.1 0 : ℚ) / p.1 1) ((p.2 0 : ℚ) / p.2 1) G = 0) :
    S.card ≤ ∑ G ∈ T, (zeros G S).card := by
  calc
    _ ≤ (T.biUnion (fun G ↦ zeros G S)).card := by
      apply card_le_card
      intro p hp
      obtain ⟨G, hG, hz⟩ := hcover p hp
      exact mem_biUnion.mpr ⟨G, hG, mem_filter.mpr ⟨hp, hz⟩⟩
    _ ≤ _ := card_biUnion_le

theorem uniform_bounded_projective_cover (Amax Bmax κ : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ F : ℤ[X][X], F ≠ 0 → degreeX F ≤ Amax → degreeY F ≤ Bmax →
      height F ≤ N ^ κ → ∀ S : Finset ((Fin 2 → ℤ) × (Fin 2 → ℤ)),
      (∀ p ∈ S, p.1 1 ≠ 0 ∧ p.2 1 ≠ 0) →
      (∀ p ∈ S, evaluate ((p.1 0 : ℚ) / p.1 1) ((p.2 0 : ℚ) / p.2 1) F = 0) →
      ∃ T : Finset ℤ[X][X], T.card ≤ Amax + Bmax ∧
        (∀ G ∈ T, Irreducible G ∧ G ∣ F ∧ 0 < degreeX G + degreeY G ∧
          degreeX G ≤ Amax ∧ degreeY G ≤ Bmax ∧ height G ≤ N ^ (κ + 1) ∧
          projective G ≠ 0 ∧
          (∀ m n, |((projective G).coeff m).coeff n| ≤ ((N ^ (κ + 1) : ℕ) : ℤ))) ∧
        (∀ p ∈ S, ∃ G ∈ T, MvPolynomial.eval₂ (MvPolynomial.eval p.2) p.1 (projective G) = 0) ∧
        S.card ≤ ∑ G ∈ T, (zeros G S).card := by
  obtain ⟨N₀, hheight⟩ := DeterminantFactorHeight.uniform_factor_height Amax Bmax κ
  refine ⟨N₀, ?_⟩
  intro N hN F hF hx hy hH S hdenom hzero
  obtain ⟨T, hT, hfactors, hcover⟩ := DeterminantFactorCurveCover.finite_rational_cover F hF
  have hactual (p : (Fin 2 → ℤ) × (Fin 2 → ℤ)) (hp : p ∈ S) :
      ∃ G ∈ T, evaluate ((p.1 0 : ℚ) / p.1 1) ((p.2 0 : ℚ) / p.2 1) G = 0 :=
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
    exact ⟨G, hG, (IntegerPairFactorCharts.projective_zero_iff G p.1 p.2
      (hdenom p hp).1 (hdenom p hp).2).mpr hz⟩

theorem affine_of_biform (a b H : ℕ) (w : Exponent a b → ℤ) (hw : biform a b w ≠ 0)
    (hheight : ∀ m n, |((biform a b w).coeff m).coeff n| ≤ (H : ℤ))
    (S : Finset ((Fin 2 → ℤ) × (Fin 2 → ℤ)))
    (hdenom : ∀ p ∈ S, p.1 1 ≠ 0 ∧ p.2 1 ≠ 0)
    (hzero : ∀ p ∈ S, MvPolynomial.eval₂ (MvPolynomial.eval p.2) p.1 (biform a b w) = 0) :
    ∃ F : ℤ[X][X], F ≠ 0 ∧ degreeX F ≤ a ∧ degreeY F ≤ b ∧ height F ≤ H ∧
      ∀ p ∈ S, evaluate ((p.1 0 : ℚ) / p.1 1) ((p.2 0 : ℚ) / p.2 1) F = 0 := by
  have hw₀ : w ≠ 0 := fun h ↦ hw ((BiformCoefficientRecovery.biform_zero_iff a b w).mpr h)
  have hcoeff := BiformCoefficientRecovery.coefficient_bound_from_biform a b H w hheight
  refine ⟨rectangle a b w, DeterminantAuxiliaryPolynomial.rectangle_ne_zero a b w hw₀,
    rectangle_degreeX a b w, rectangle_degreeY a b w,
    DeterminantAuxiliaryPolynomial.rectangle_height_le a b H w hcoeff, ?_⟩
  intro p hp
  exact (IntegerPairFactorCharts.rectangle_zero_iff a b w p.1 p.2
    (hdenom p hp).1 (hdenom p hp).2).mp (hzero p hp)

end PaperP1.IntegerPairFactorCover
