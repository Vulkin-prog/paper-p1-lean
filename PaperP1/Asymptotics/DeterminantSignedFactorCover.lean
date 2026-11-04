module

public import PaperP1.Asymptotics.DeterminantSignedAuxiliary
public import PaperP1.Asymptotics.DeterminantFactorCurveCover

/-! # Every signed original source interval reduces to boundedly many actual factor curves -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DeterminantSignedFactorCover

open Finset Polynomial PaperP1.DeterminantSourceBox PaperP1.DeterminantSignedBoxes
  PaperP1.TwoKernelDeterminantBoxes PaperP1.DeterminantRelativeIntervals
  PaperP1.DeterminantHorizontalScale PaperP1.DeterminantSignedAuxiliary
  PaperP1.DeterminantFactorCurveCover PaperP1.BivariateDegrees PaperP1.BivariateHeight
  PaperP1.IntegerFactorProjectiveCurve

theorem signedCluster_subset (h : ℤ) (M : ℕ) (D E : ℝ) (k : ℕ) (S : Finset Quad) :
    signedCluster h M D E k S ⊆ S := by
  intro p hp
  unfold signedCluster at hp
  split_ifs at hp
  · exact (mem_filter.mp hp).1
  · exact (mem_filter.mp hp).1

theorem uniform_factor_covers (δ C ρ Kshift A₀ ζ : ℝ)
    (hδ : 0 < δ) (hC : 0 < C) (hρ : 0 < ρ) (hρ₁ : ρ ≤ 1)
    (hζ : 0 < ζ) (hζsmall : ζ < 7 / 16) :
    ∃ B Amax κ N₀ : ℕ, 0 < B ∧ ∀ N ≥ N₀, ∀ h : ℤ,
      h ≠ 0 → (h.natAbs : ℝ) ≤ Kshift * (Real.log N) ^ A₀ →
      ∀ X : Box N ρ C δ, ∀ S : Finset Quad, SignedPopulation X h S →
      let M := horizontalScale N X.D X.E X.U X.V ζ
      4 ≤ M ∧ S.card = ∑ k ∈ intervalIndices M, (signedCluster h M X.D X.E k S).card ∧
      ∀ k ∈ intervalIndices M, (signedCluster h M X.D X.E k S).Nonempty →
        ∃ T : Finset ℤ[X][X], T.card ≤ Amax + B ∧
          (∀ G ∈ T, Irreducible G ∧ 0 < degreeX G + degreeY G ∧
            degreeX G ≤ Amax ∧ degreeY G ≤ B ∧ height G ≤ N ^ κ ∧
            projective G ≠ 0 ∧
            (∀ m n, |((projective G).coeff m).coeff n| ≤ ((N ^ κ : ℕ) : ℤ))) ∧
          (∀ p ∈ signedCluster h M X.D X.E k S, ∃ G ∈ T,
            MvPolynomial.eval₂ (MvPolynomial.eval ![(p.2.2 : ℤ), p.2.1]) ![(p.1.1 : ℤ), p.1.2]
              (projective G) = 0) ∧
          (signedCluster h M X.D X.E k S).card ≤
            ∑ G ∈ T, (zeros G (signedCluster h M X.D X.E k S)).card := by
  obtain ⟨B, Amax, κ, Na, hB, haux⟩ :=
    DeterminantSignedAuxiliary.uniform_biforms δ C ρ Kshift A₀ ζ hδ hC hρ hρ₁ hζ hζsmall
  obtain ⟨Nf, hfactors⟩ := uniform_bounded_projective_cover Amax B κ
  refine ⟨B, Amax, κ + 1, max Na Nf, hB, ?_⟩
  intro N hN h hh hshift X S hS
  obtain ⟨hM₄, hpartition, hcurves⟩ := haux N (by omega) h hh hshift X S hS
  refine ⟨hM₄, hpartition, ?_⟩
  intro k hk hnonempty
  let R := signedCluster h (horizontalScale N X.D X.E X.U X.V ζ) X.D X.E k S
  have hsub : R ⊆ S := signedCluster_subset _ _ _ _ _ _
  have he (p : Quad) (hp : p ∈ R) : 0 < p.1.2 := by
    have hh : (0 : ℝ) < p.1.2 := by
      have hlo := (hS.e_bounds p (hsub hp)).1
      linarith only [X.E_ge_one, hlo]
    exact_mod_cast hh
  have hu (p : Quad) (hp : p ∈ R) : 0 < p.2.1 := by
    have hh : (0 : ℝ) < p.2.1 := by
      have hlo := (hS.u_bounds p (hsub hp)).1
      linarith only [X.U_ge_one, hlo]
    exact_mod_cast hh
  obtain ⟨A, _, hA, w, hw, _, _, hheight, hzero⟩ := hcurves k hk hnonempty
  obtain ⟨F, hF, hx, hy, hH, hFzero⟩ := affine_of_biform A B (N ^ κ) w hw hheight R he hu hzero
  obtain ⟨T, hT, hG, hpoints, hcount⟩ := hfactors N (by omega) F hF (hx.trans hA) hy hH R he hu hFzero
  refine ⟨T, hT, ?_, hpoints, hcount⟩
  intro G hg
  obtain ⟨hirr, _, hpos, hdx, hdy, hheightG, hGne, hcoeff⟩ := hG G hg
  exact ⟨hirr, hpos, hdx, hdy, hheightG, hGne, hcoeff⟩

end PaperP1.DeterminantSignedFactorCover
