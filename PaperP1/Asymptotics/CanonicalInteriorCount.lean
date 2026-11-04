module

public import PaperP1.Arithmetic.CanonicalInteriorSourceBox
public import PaperP1.Asymptotics.SevenTwelfthsSourceCount
public import PaperP1.Asymptotics.DeterminantEnumerationBudget

/-! # Sharp counting on all occupied canonical interior boxes at fixed smooth coefficients -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CanonicalInteriorCount

open Finset PaperP1.TwoKernelDeterminantBoxes PaperP1.TwoKernelDeterminantScale
open PaperP1.TwoSmallKernelSquareParts PaperP1.SmallPrimeBudget PaperP1.LargeOddKernel PaperP1.DefectivePredicate

theorem uniform_fixed_coefficients (hHB : HeathBrownBiformInput.Input) (hNG : NonGeometricBiformInput.Input)
    (δ K A ε : ℝ) (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 2) (hK : 0 ≤ K) (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ H h c₁ c₂ : ℕ, ∀ T : ℝ,
      0 < h → (h : ℝ) ≤ K * (Real.log N) ^ A → 0 ≤ T →
      ∀ S : Finset ℕ,
      (∀ n ∈ S, 0 < n ∧ N ≤ 2 * n ∧ n ≤ 3 * N ∧ n + h ≤ 4 * N) →
      (∀ n ∈ S, smallOddPart H n = c₁ ∧ smallOddPart H (n + h) = c₂) →
      (∀ n ∈ S, (largeOddKernel H n : ℝ) ≤ T ∧ (largeOddKernel H (n + h) : ℝ) ≤ T) →
      (∀ n ∈ S, 4 * Real.sqrt N < ((canonicalSquarePart n * canonicalSquarePart (n + h) : ℕ) : ℝ) ∧
        4 * (N : ℝ) ^ δ < ((largeOddKernel H n * largeOddKernel H (n + h) : ℕ) : ℝ)) →
      (S.card : ℝ) ≤ (T + (N : ℝ) ^ (7 / 12 : ℝ)) * (N : ℝ) ^ ε := by
  classical
  obtain ⟨Nc, hc⟩ := SevenTwelfthsSourceCount.uniform_count hHB hNG δ 4 (1 / 16) K A (ε / 2)
    hδ (by norm_num) (by norm_num) (by norm_num) hK hA (by positivity)
  obtain ⟨Nb, hb⟩ := DeterminantEnumerationBudget.boxes_subpolynomial 4 (by norm_num) (ε / 2) (by positivity)
  refine ⟨max 2 (max Nc Nb), ?_⟩
  intro N hN H h c₁ c₂ T hh hshift hT S hheight hcoefs hkernel hlarge
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  let I := occupied H h c₁ c₂ (4 * N) S
  let B := T + (N : ℝ) ^ (7 / 12 : ℝ)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hlocal : ∀ a ∈ I, ((solutions c₁ c₂ h (2 ^ a.1.1) (2 ^ a.1.2) (2 ^ a.2.1) (2 ^ a.2.2)).card : ℝ) ≤
      B * (N : ℝ) ^ (ε / 2) := by
    intro a ha
    obtain ⟨_ha, n, hnS, hbox⟩ := mem_filter.mp ha
    obtain ⟨hnpos, hnlo, hnhi, hmhi⟩ := hheight n hnS
    obtain ⟨hc₁, hc₂⟩ := hcoefs n hnS
    obtain ⟨hk₁, hk₂⟩ := hkernel n hnS
    obtain ⟨hlD, hlU⟩ := hlarge n hnS
    have hpow : ∀ j : ℕ, 1 ≤ (2 : ℕ) ^ j := by
      intro j
      have hp : 0 < (2 : ℕ) ^ j := by positivity
      omega
    obtain ⟨X, hxc₁, hxc₂, hD, hE, hU, hV, hbarrier, hcapU, hcapV⟩ :=
      CanonicalInteriorSourceBox.witness_box δ T (by omega) hδ hδsmall
        (hpow a.1.1) (hpow a.1.2) (hpow a.2.1) (hpow a.2.2)
        hnpos hnlo hnhi hmhi hc₁ hc₂ hk₁ hk₂ hlD hlU hbox
    let coefs : IntegralSourceCoefficients.IntegerCoefficients X := ⟨c₁, c₂, hxc₁, hxc₂⟩
    have hhZ : (h : ℤ) ≠ 0 := by exact_mod_cast hh.ne'
    have hsigned : |((h : ℤ) : ℝ)| ≤ K * (Real.log N) ^ A := by
      simpa only [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg h : (0 : ℝ) ≤ h)] using hshift
    exact hc N (by omega) (h : ℤ) hhZ hsigned X coefs hbarrier T hT hcapU hcapV
      (solutions c₁ c₂ h (2 ^ a.1.1) (2 ^ a.1.2) (2 ^ a.2.1) (2 ^ a.2.2))
      (CanonicalInteriorSourceBox.solutions_population X hxc₁ hxc₂ hD hE hU hV)
  have hcover : (S.card : ℝ) ≤ ∑ a ∈ I,
      ((solutions c₁ c₂ h (2 ^ a.1.1) (2 ^ a.1.2) (2 ^ a.2.1) (2 ^ a.2.2)).card : ℝ) := by
    have hhcover := finite_cover_occupied S (by
      intro n hnS
      exact ⟨(hheight n hnS).1, (hheight n hnS).2.2.2, (hcoefs n hnS).1, (hcoefs n hnS).2⟩)
    exact_mod_cast hhcover
  have hI : (I.card : ℝ) ≤ (N : ℝ) ^ (ε / 2) := by
    have hi : I.card ≤ (boxes (4 * N)).card := card_filter_le _ _
    exact (by exact_mod_cast hi : (I.card : ℝ) ≤ (boxes (4 * N)).card).trans (hb N (by omega))
  calc
    _ ≤ ∑ a ∈ I, ((solutions c₁ c₂ h (2 ^ a.1.1) (2 ^ a.1.2) (2 ^ a.2.1) (2 ^ a.2.2)).card : ℝ) := hcover
    _ ≤ ∑ _a ∈ I, B * (N : ℝ) ^ (ε / 2) := sum_le_sum hlocal
    _ = (I.card : ℝ) * (B * (N : ℝ) ^ (ε / 2)) := by simp only [sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ) ^ (ε / 2) * (B * (N : ℝ) ^ (ε / 2)) :=
      mul_le_mul_of_nonneg_right hI (mul_nonneg hB (Real.rpow_nonneg hn.le _))
    _ = _ := by
      calc
        _ = B * ((N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / 2)) := by ring
        _ = _ := by rw [← Real.rpow_add hn, add_halves]

end PaperP1.CanonicalInteriorCount
