module

public import PaperP1.Diophantine.HeathBrownBiformInput
public import PaperP1.Asymptotics.SplitQuadraticCongruenceCount

/-! # The ordinary geometric count pays for the actual moving coefficient height -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HeathBrownHeightBudget

open Finset Polynomial PaperP1.BivariateDegrees PaperP1.BivariateHeight
open PaperP1.IntegerFactorProjectiveCurve PaperP1.GeometricFactorSwap PaperP1.BidegreeOneFibreCount

theorem uniform_first_count (hHB : HeathBrownBiformInput.Input) (a b K κ : ℕ)
    (ha : 0 < a) (hb : 2 ≤ b) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ G : ℤ[X][X], degreeX G = a → degreeY G = b → Geometric G →
      height G ≤ N ^ κ → ∀ L : ℝ, 1 ≤ L → L ≤ (N : ℝ) ^ K → ∀ S : Finset Point,
      (∀ s ∈ S, (s.1 0).natAbs.Coprime (s.1 1).natAbs ∧ (s.2 0).natAbs.Coprime (s.2 1).natAbs) →
      (∀ s ∈ S, MvPolynomial.eval₂ (MvPolynomial.eval s.2) s.1 (projective G) = 0) →
      (∀ s ∈ S, ∀ i, |(s.1 i : ℝ)| ≤ L) → (S.card : ℝ) ≤ (N : ℝ) ^ ε * L := by
  let ν := K + κ + 1
  have hν : (0 : ℝ) < ν := by dsimp [ν]; positivity
  let θ : ℝ := ε / (2 * ν)
  have hθ : 0 < θ := by dsimp [θ]; positivity
  have hνθ : (ν : ℝ) * θ = ε / 2 := by dsimp [θ]; field_simp [hν.ne']
  obtain ⟨CHB, hCHB, hcount⟩ := hHB a b ha (by omega) θ hθ
  obtain ⟨Nc, hc⟩ := SplitQuadraticCongruenceCount.polylog_le_rpow CHB 0 (ε / 2) (by positivity)
  refine ⟨max 1 Nc, ?_⟩
  intro N hN G hfirst hsecond hgeo hheight L hL hLH S hprim hzero hbox
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hLp : 0 < L := by linarith
  have hbR : (2 : ℝ) ≤ b := by exact_mod_cast hb
  have hbr : (0 : ℝ) < b := by linarith
  have hbase : L ^ (2 / (b : ℝ)) ≤ L := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hL ((div_le_one hbr).mpr hbR)
  have hLθ : L ^ θ ≤ (N : ℝ) ^ ((K : ℝ) * θ) := by
    calc
      _ ≤ ((N : ℝ) ^ K) ^ θ := Real.rpow_le_rpow hLp.le hLH hθ.le
      _ = _ := by rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le]
  have hGθ : (height G : ℝ) ^ θ ≤ (N : ℝ) ^ ((κ : ℝ) * θ) := by
    have hh : (height G : ℝ) ≤ (N : ℝ) ^ κ := by exact_mod_cast hheight
    calc
      _ ≤ ((N : ℝ) ^ κ) ^ θ := Real.rpow_le_rpow (Nat.cast_nonneg _) hh hθ.le
      _ = _ := by rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le]
  have hfull : L ^ (2 / (b : ℝ) + θ) ≤ L * (N : ℝ) ^ ((K : ℝ) * θ) := by
    rw [Real.rpow_add hLp]
    exact mul_le_mul hbase hLθ (Real.rpow_nonneg hLp.le _) hLp.le
  have hexp : ((K : ℝ) + κ) * θ ≤ ε / 2 := by
    calc
      _ ≤ (ν : ℝ) * θ := mul_le_mul_of_nonneg_right (by dsimp [ν]; push_cast; linarith) hθ.le
      _ = _ := hνθ
  have hproduct : L ^ (2 / (b : ℝ) + θ) * (height G : ℝ) ^ θ ≤ L * (N : ℝ) ^ (ε / 2) := by
    calc
      _ ≤ (L * (N : ℝ) ^ ((K : ℝ) * θ)) * (N : ℝ) ^ ((κ : ℝ) * θ) := by gcongr
      _ = L * (N : ℝ) ^ (((K : ℝ) + κ) * θ) := by rw [mul_assoc, ← Real.rpow_add hn]; congr 2; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn1 hexp) hLp.le
  have hconstant : CHB ≤ (N : ℝ) ^ (ε / 2) := by simpa only [Real.rpow_zero, mul_one] using hc N (by omega)
  calc
    _ ≤ CHB * L ^ (2 / (b : ℝ) + θ) * (height G : ℝ) ^ θ :=
      hcount G hfirst hsecond hgeo L hL S hprim hzero hbox
    _ = CHB * (L ^ (2 / (b : ℝ) + θ) * (height G : ℝ) ^ θ) := by ring
    _ ≤ CHB * (L * (N : ℝ) ^ (ε / 2)) := mul_le_mul_of_nonneg_left hproduct hCHB
    _ ≤ (N : ℝ) ^ (ε / 2) * (L * (N : ℝ) ^ (ε / 2)) := by gcongr
    _ = ((N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / 2)) * L := by ring
    _ = _ := by rw [← Real.rpow_add hn]; congr 2; ring

theorem uniform_second_count (hHB : HeathBrownBiformInput.Input) (a b K κ : ℕ)
    (ha : 2 ≤ a) (hb : 0 < b) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ G : ℤ[X][X], degreeX G = a → degreeY G = b → Geometric G →
      height G ≤ N ^ κ → ∀ T : ℝ, 1 ≤ T → T ≤ (N : ℝ) ^ K → ∀ S : Finset Point,
      (∀ s ∈ S, (s.1 0).natAbs.Coprime (s.1 1).natAbs ∧ (s.2 0).natAbs.Coprime (s.2 1).natAbs) →
      (∀ s ∈ S, MvPolynomial.eval₂ (MvPolynomial.eval s.2) s.1 (projective G) = 0) →
      (∀ s ∈ S, ∀ i, |(s.2 i : ℝ)| ≤ T) → (S.card : ℝ) ≤ (N : ℝ) ^ ε * T := by
  obtain ⟨N₀, hN₀⟩ := uniform_first_count hHB b a K κ hb ha ε hε
  refine ⟨N₀, ?_⟩
  intro N hN G hfirst hsecond hgeo hheight T hT hTH S hprim hzero hbox
  have hbnd := hN₀ N hN (Bivariate.swap G)
    (by simpa only [BivariateProjectiveSwap.degreeX_swap] using hsecond)
    (by simpa only [BivariateProjectiveSwap.degreeY_swap] using hfirst) (geometric_swap G hgeo)
    (by simpa only [BivariateLargeRoot.height_swap] using hheight) T hT hTH (S.image Prod.swap)
  have hh : ((S.image Prod.swap).card : ℝ) ≤ (N : ℝ) ^ ε * T := by
    apply hbnd
    · intro s hs
      obtain ⟨t, ht, rfl⟩ := mem_image.mp hs
      exact ⟨(hprim t ht).2, (hprim t ht).1⟩
    · intro s hs
      obtain ⟨t, ht, rfl⟩ := mem_image.mp hs
      exact (BivariateProjectiveSwap.evaluation_swap G t.1 t.2).trans (hzero t ht)
    · intro s hs
      obtain ⟨t, ht, rfl⟩ := mem_image.mp hs
      exact hbox t ht
  simpa only [card_image_of_injective S Prod.swap_injective] using hh

end PaperP1.HeathBrownHeightBudget
