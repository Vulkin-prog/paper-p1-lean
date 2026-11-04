module

public import PaperP1.Diophantine.LinearProjectiveFactor
public import PaperP1.Arithmetic.BivariateProjectiveSwap
public import PaperP1.Diophantine.PrimitiveHomogeneousZeros

/-! # Exact one-pair equations and primitive projections of degree-zero factors -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ZeroPartialDegreeFactor

open Finset Polynomial PaperP1.BivariateDegrees PaperP1.IntegerFactorProjectiveCurve
open PaperP1.HomogeneousCharts PaperP1.BivariateProjectiveSwap

def secondForm (G : ℤ[X][X]) : MvPolynomial (Fin 2) ℤ :=
  ((Bivariate.swap G).coeff 0).homogenize (degreeY G)

theorem secondForm_homogeneous (G : ℤ[X][X]) : (secondForm G).IsHomogeneous (degreeY G) :=
  Polynomial.isHomogeneous_homogenize _

theorem projective_first_degree_zero (G : ℤ[X][X]) (hG : degreeX G = 0) :
    projective G = MvPolynomial.C (secondForm G) := by
  have hhom : (projective G).IsHomogeneous 0 := by simpa only [hG] using projective_homogeneous G
  have h0 := LinearProjectiveFactor.projective_chart_coefficient G ⟨0, by omega⟩
  have he := BihomogeneousSwap.binary_expansion (projective G) hhom
  change projective G = ∑ j : Fin 1, MvPolynomial.C ((chart (projective G)).coeff j.val) *
    MvPolynomial.X 0 ^ j.val * MvPolynomial.X 1 ^ (0 - j.val) at he
  simpa only [Fin.sum_univ_one, Fin.val_zero, Nat.sub_self, pow_zero, mul_one, h0, secondForm] using he

theorem evaluation_first_degree_zero (G : ℤ[X][X]) (hG : degreeX G = 0) (x y : Fin 2 → ℤ) :
    MvPolynomial.eval₂ (MvPolynomial.eval y) x (projective G) = MvPolynomial.eval y (secondForm G) := by
  rw [projective_first_degree_zero G hG, MvPolynomial.eval₂_C]

theorem secondForm_nonzero (G : ℤ[X][X]) (hG : G ≠ 0) (hdegree : degreeX G = 0) :
    secondForm G ≠ 0 := by
  intro hz
  apply projective_nonzero G hG
  rw [projective_first_degree_zero G hdegree, hz, map_zero]

theorem primitive_second_projection_count (G : ℤ[X][X]) (hG : G ≠ 0) (hdegree : degreeX G = 0)
    (S : Finset ((Fin 2 → ℤ) × (Fin 2 → ℤ)))
    (hprim : ∀ s ∈ S, (s.2 0).natAbs.Coprime (s.2 1).natAbs)
    (hzero : ∀ s ∈ S, MvPolynomial.eval₂ (MvPolynomial.eval s.2) s.1 (projective G) = 0) :
    (S.image Prod.snd).card ≤ 2 * (degreeY G + 1) := by
  apply PrimitiveHomogeneousZeros.primitive_card (secondForm G) (secondForm_homogeneous G)
    (secondForm_nonzero G hG hdegree)
  · intro y hy
    obtain ⟨s, hs, rfl⟩ := mem_image.mp hy
    exact hprim s hs
  · intro y hy
    obtain ⟨s, hs, rfl⟩ := mem_image.mp hy
    exact (evaluation_first_degree_zero G hdegree s.1 s.2).symm.trans (hzero s hs)

theorem primitive_first_projection_count (G : ℤ[X][X]) (hG : G ≠ 0) (hdegree : degreeY G = 0)
    (S : Finset ((Fin 2 → ℤ) × (Fin 2 → ℤ)))
    (hprim : ∀ s ∈ S, (s.1 0).natAbs.Coprime (s.1 1).natAbs)
    (hzero : ∀ s ∈ S, MvPolynomial.eval₂ (MvPolynomial.eval s.2) s.1 (projective G) = 0) :
    (S.image Prod.fst).card ≤ 2 * (degreeX G + 1) := by
  have hswap : Bivariate.swap G ≠ 0 := by
    intro hz
    apply hG
    exact (Bivariate.swap (R := ℤ)).injective (hz.trans (map_zero _).symm)
  have hb := primitive_second_projection_count (Bivariate.swap G) hswap
    (by simpa only [degreeX_swap] using hdegree) (S.image Prod.swap)
    (by intro s hs; obtain ⟨t, ht, rfl⟩ := mem_image.mp hs; exact hprim t ht)
    (by intro s hs; obtain ⟨t, ht, rfl⟩ := mem_image.mp hs; exact (evaluation_swap G t.1 t.2).trans (hzero t ht))
  simpa only [image_image, Function.comp_def, Prod.snd_swap, degreeY_swap] using hb

end PaperP1.ZeroPartialDegreeFactor
