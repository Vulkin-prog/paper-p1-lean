module

public import PaperP1.Diophantine.ActualAuxiliaryCoordinates
public import PaperP1.Asymptotics.FourChartFactorCover

/-! # Actual primitive source quadruples covered by bounded factors in their inverse coordinates -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ActualAuxiliaryFactorCover

open Finset Polynomial PaperP1.DeterminantIntegerRows PaperP1.DeterminantAuxiliaryBiform
open PaperP1.ActualProjectivePairs PaperP1.ActualAuxiliaryCoordinates PaperP1.TwoKernelDeterminantBoxes
open PaperP1.BivariateDegrees PaperP1.BivariateHeight PaperP1.IntegerFactorProjectiveCurve
open PaperP1.FourProjectiveCharts PaperP1.IntegerPairFactorCover

theorem uniform_actual_cover (Amax Bmax κ μ ν : ℕ) :
    ∃ κ' N₀ : ℕ, ∀ N ≥ N₀, ∀ a ≤ Amax, ∀ b ≤ Bmax, ∀ w : Exponent a b → ℤ,
      biform a b w ≠ 0 → (∀ m n, |((biform a b w).coeff m).coeff n| ≤ ((N ^ κ : ℕ) : ℤ)) →
      ∀ A B C D : Matrix (Fin 2) (Fin 2) ℤ, A * B = 1 → B * A = 1 → C * D = 1 → D * C = 1 →
      (∀ i j, |A i j| ≤ ((N ^ μ : ℕ) : ℤ)) → (∀ i j, |C i j| ≤ ((N ^ ν : ℕ) : ℤ)) →
      ∀ S : Finset Quad, (∀ p ∈ S, Primitive p) →
      (∀ p ∈ S, MvPolynomial.eval₂ (MvPolynomial.eval ![(p.2.2 : ℤ), p.2.1])
        ![(p.1.1 : ℤ), p.1.2] (biform a b w) = 0) →
      let P := S.image (coordinates B D)
      ∃ T : Bool × Bool → Finset ℤ[X][X],
        (∀ c : Bool × Bool, (T c).card ≤ Amax + Bmax ∧
          (∀ G ∈ T c, Irreducible G ∧ 0 < degreeX G + degreeY G ∧
            degreeX G ≤ Amax ∧ degreeY G ≤ Bmax ∧ height G ≤ N ^ κ' ∧ projective G ≠ 0 ∧
            (∀ m n, |((projective G).coeff m).coeff n| ≤ ((N ^ κ' : ℕ) : ℤ))) ∧
          (∀ p ∈ population c P, ∃ G ∈ T c,
            MvPolynomial.eval₂ (MvPolynomial.eval p.2) p.1 (projective G) = 0) ∧
          (population c P).card ≤ ∑ G ∈ T c, (zeros G (population c P)).card) ∧
        S.card ≤ ∑ c : Bool × Bool, ∑ G ∈ T c, (zeros G (population c P)).card := by
  obtain ⟨κ₁, NH, hheight⟩ := uniform_transformed_family_height Amax Bmax κ μ ν
  obtain ⟨κ', NC, hcover⟩ := FourChartFactorCover.uniform_factor_covers Amax Bmax κ₁
  refine ⟨κ', max NH NC, ?_⟩
  intro N hN a ha b hb w hw hH A B C D hAB hBA hCD hDC hA hC S hprimitive hzero
  let F := PaperP1.BiformLinearCoordinates.transform (b := b) A C (forms a b w)
  have hF : ∀ i, (F i).IsHomogeneous b := PaperP1.BiformLinearCoordinates.transform_homogeneous A C _
  have hF0 : F ≠ 0 := PaperP1.BiformLinearCoordinates.transform_nonzero A B C D hAB hBA hCD hDC
    (forms a b w) (forms_homogeneous a b w) (forms_family_nonzero a b w hw)
  have hAnat : ∀ i j, (A i j).natAbs ≤ N ^ μ := by
    intro i j
    have hh : ((A i j).natAbs : ℤ) ≤ ((N ^ μ : ℕ) : ℤ) := by simpa only [Int.natCast_natAbs] using hA i j
    exact_mod_cast hh
  have hCnat : ∀ i j, (C i j).natAbs ≤ N ^ ν := by
    intro i j
    have hh : ((C i j).natAbs : ℤ) ≤ ((N ^ ν : ℕ) : ℤ) := by simpa only [Int.natCast_natAbs] using hC i j
    exact_mod_cast hh
  have hFH : ∀ i m, ((F i).coeff m).natAbs ≤ N ^ κ₁ :=
    hheight N (by omega) a ha b hb w hH A C hAnat hCnat
  let P := S.image (coordinates B D)
  have hPprimitive : ∀ p ∈ P, (p.1 0).natAbs.Coprime (p.1 1).natAbs ∧ (p.2 0).natAbs.Coprime (p.2 1).natAbs := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hp
    exact coordinates_primitive A B C D hAB hCD q (hprimitive q hq)
  have hPzero : ∀ p ∈ P, BidegreeOneElimination.original F p.1 p.2 = 0 := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := mem_image.mp hp
    exact coordinate_zero a b w A B C D hAB hCD q (hzero q hq)
  obtain ⟨T, hT, hsum⟩ := hcover N (by omega) a ha b hb F hF hF0 hFH P hPprimitive hPzero
  refine ⟨T, hT, ?_⟩
  calc
    S.card = P.card := (coordinates_card A B C D hAB hCD S).symm
    _ ≤ _ := hsum

end PaperP1.ActualAuxiliaryFactorCover
