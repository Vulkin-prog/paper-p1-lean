module

public import PaperP1.Diophantine.HeathBrownBiformInput
public import PaperP1.Diophantine.GeometricBiformCoarseCount

/-! # The ordinary Heath-Brown property for second degree at least two

The exact original input is recovered using the internally proved b=1 case.
The b>=2 property is proved internally by GeometricBiformPointCount.higher_input
(P1-MATH-0361); it remains an ordinary explicit parameter in this generic bridge.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HeathBrownHigherDegreeBiformInput

open Polynomial PaperP1.BivariateDegrees PaperP1.BivariateHeight PaperP1.IntegerFactorProjectiveCurve
  PaperP1.GeometricFactorSwap PaperP1.BidegreeOneFibreCount

def Input : Prop :=
  ∀ a b : ℕ, 0 < a → 2 ≤ b → ∀ ε : ℝ, 0 < ε →
    ∃ K : ℝ, 0 ≤ K ∧ ∀ G : ℤ[X][X], degreeX G = a → degreeY G = b → Geometric G →
      ∀ L : ℝ, 1 ≤ L → ∀ S : Finset Point,
      (∀ s ∈ S, (s.1 0).natAbs.Coprime (s.1 1).natAbs ∧ (s.2 0).natAbs.Coprime (s.2 1).natAbs) →
      (∀ s ∈ S, MvPolynomial.eval₂ (MvPolynomial.eval s.2) s.1 (projective G) = 0) →
      (∀ s ∈ S, ∀ i, |(s.1 i : ℝ)| ≤ L) →
        (S.card : ℝ) ≤ K * L ^ (2 / (b : ℝ) + ε) * (height G : ℝ) ^ ε

theorem full_input (hHigher : Input) : PaperP1.HeathBrownBiformInput.Input := by
  intro a b ha hb ε hε
  by_cases hb₁ : b = 1
  · refine ⟨36, by norm_num, ?_⟩
    intro G _hX hY hgeom L hL S hprim hzero hbox
    have hne : G ≠ 0 := by
      intro hz
      have hd : degreeY G = 0 := by simp [degreeY, hz]
      omega
    have hc := GeometricBiformCoarseCount.second_degree_one G hne (hY.trans hb₁)
      hgeom ε hε L hL S hprim hzero hbox
    simpa only [hb₁, Nat.cast_one, div_one] using hc
  · exact hHigher a b ha (by omega) ε hε

theorem restriction_of_full_input (hHB : PaperP1.HeathBrownBiformInput.Input) : Input := by
  intro a b ha hb ε hε
  exact hHB a b ha (by omega) ε hε

end PaperP1.HeathBrownHigherDegreeBiformInput
