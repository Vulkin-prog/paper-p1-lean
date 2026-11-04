module

public import PaperP1.Diophantine.ActualLinearFactorCount
public import PaperP1.Arithmetic.BivariateProjectiveSwap

/-! # The unconditional local count when the other partial degree is one -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ActualSecondLinearFactorCount

open Finset Polynomial PaperP1.BivariateDegrees PaperP1.BivariateHeight
open PaperP1.BidegreeOneFibreCount PaperP1.IntegerFactorProjectiveCurve
open PaperP1.BivariateProjectiveSwap

theorem uniform_count (ell k d κ : ℕ) (hd : 0 < d) (hdegree : 0 < ell + d * k)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ G : ℤ[X][X], Irreducible G → degreeY G = 1 → degreeX G = d →
      height G ≤ N ^ κ → ∀ C : Fin (ell + 1) → MvPolynomial (Fin 2) ℤ,
      (∀ i, (C i).IsHomogeneous k) → ∀ h : ℤ, h ≠ 0 → ∀ L T : ℝ, 1 ≤ L → 0 ≤ T →
      ∀ S : Finset Point,
      (∀ s ∈ S, (s.1 0).natAbs.Coprime (s.1 1).natAbs ∧ (s.2 0).natAbs.Coprime (s.2 1).natAbs) →
      (∀ s ∈ S, MvPolynomial.eval₂ (MvPolynomial.eval s.2) s.1 (projective G) = 0) →
      (∀ s ∈ S, BidegreeOneElimination.original C s.1 s.2 = h) →
      (∀ s ∈ S, (∀ i, |(s.1 i : ℝ)| ≤ L) ∧ ∀ i, |(s.2 i : ℝ)| ≤ T) →
        (S.card : ℝ) ≤ (N : ℝ) ^ ε * L := by
  obtain ⟨N₀, hN₀⟩ := ActualLinearFactorCount.uniform_count k ell d κ hd hdegree ε hε
  refine ⟨N₀, ?_⟩
  intro N hN G hG hsecond hfirst hheight C hC h hh L T hL hT S hprim hzero hsource hbox
  have hirr : Irreducible (Bivariate.swap G) := (MulEquiv.irreducible_iff (Bivariate.swap (R := ℤ))).mpr hG
  have hcount := hN₀ N hN (Bivariate.swap G) hirr (by simpa only [degreeX_swap] using hsecond)
    (by simpa only [degreeY_swap] using hfirst) (by simpa only [BivariateLargeRoot.height_swap] using hheight)
    (BihomogeneousSwap.coefficients (k := k) C) (BihomogeneousSwap.coefficients_homogeneous C)
    h hh T L hT hL (S.image Prod.swap)
  have hb : ((S.image Prod.swap).card : ℝ) ≤ (N : ℝ) ^ ε * L := by
    apply hcount
    · intro s hs
      obtain ⟨t, ht, rfl⟩ := mem_image.mp hs
      exact ⟨(hprim t ht).2, (hprim t ht).1⟩
    · intro s hs
      obtain ⟨t, ht, rfl⟩ := mem_image.mp hs
      exact (evaluation_swap G t.1 t.2).trans (hzero t ht)
    · intro s hs
      obtain ⟨t, ht, rfl⟩ := mem_image.mp hs
      exact (BihomogeneousSwap.original_swap C hC t.1 t.2).trans (hsource t ht)
    · intro s hs
      obtain ⟨t, ht, rfl⟩ := mem_image.mp hs
      exact ⟨(hbox t ht).2, (hbox t ht).1⟩
  simpa only [card_image_of_injective S Prod.swap_injective] using hb

end PaperP1.ActualSecondLinearFactorCount
