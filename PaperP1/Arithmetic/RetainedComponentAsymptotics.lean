module

public import PaperP1.Arithmetic.MediumPrimeHarmonic
public import PaperP1.Arithmetic.ShortBasisComponentStage
public import PaperP1.Arithmetic.ComponentPrimeBudget

/-! # The actual two-thirds component loss in every critical pair of windows -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RetainedComponentAsymptotics

open Finset Filter PaperP1.Arithmetic PaperP1.DefectCounting PaperP1.LocalDefectBound
  PaperP1.MediumPrimeColumns PaperP1.MediumPrimeHarmonic PaperP1.ShortBasisComponentStage
  PaperP1.FreeComponentRank PaperP1.LargePrimeGraphResolution
  PaperP1.LargePrimeComponentArithmetic PaperP1.CriticalBandScale

theorem medium_card_le_primeCount (L z : ℕ) : (mediumPrimes L z).card ≤ primeCount (10 * (L + 1)) := by
  apply card_le_card
  intro p hp
  obtain ⟨hprime, _hz, hbound⟩ := (mem_mediumPrimes L z p).mp hp
  exact mem_smallPrimesUpTo.mpr ⟨hprime, hbound⟩

theorem component_size_cost (L : ℕ) (hL : 1 ≤ L) :
    2 * ((L + 1 : ℕ) : ℝ) / (⌊Real.log ((L + 1 : ℕ) : ℝ)⌋₊ + 1 : ℕ) ≤
      2 * ((L + 1 : ℕ) : ℝ) / Real.log ((L + 1 : ℕ) : ℝ) := by
  have hlog : 0 < Real.log ((L + 1 : ℕ) : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < L + 1 by omega))
  have hfloor : Real.log ((L + 1 : ℕ) : ℝ) ≤ ((⌊Real.log ((L + 1 : ℕ) : ℝ)⌋₊ + 1 : ℕ) : ℝ) := by
    push_cast
    exact (Nat.lt_floor_add_one _).le
  exact div_le_div_of_nonneg_left (by positivity) hlog hfloor

def lossConstant (a : ℝ) : ℝ := (2 / 3) * windowConstant a + 18

theorem lossConstant_pos (a : ℝ) (ha : 0 < a) : 0 < lossConstant a := by
  have h := windowConstant_pos a ha
  unfold lossConstant
  linarith

theorem eventual_retained_lower (a : ℝ) (ha : 0 < a) (ha₁ : a ≤ 1) :
    ∃ L₀ : ℕ, 1 ≤ L₀ ∧ ∀ L ≥ L₀, ∀ x y : ℕ, 1 ≤ x → 1 ≤ y →
      (pairIntersectionRank x y L : ℝ) - defectiveVertexCount x y L -
        (2 / 3) * ((L + 1 : ℕ) : ℝ) * Real.log (1 / a) -
        lossConstant a * (((L + 1 : ℕ) : ℝ) / Real.log ((L + 1 : ℕ) : ℝ)) ≤
      ((retainedComponents x y L ⌊((L + 1 : ℕ) : ℝ) ^ a⌋₊
        ⌊Real.log ((L + 1 : ℕ) : ℝ)⌋₊).card : ℝ) := by
  obtain ⟨L₁, hL₁, hharmonic⟩ := eventual_medium_bound a ha ha₁
  obtain ⟨B₀, _hB₀, hprime⟩ := ComponentPrimeBudget.prime_constraint_cost_eventually
  refine ⟨max L₁ B₀, hL₁.trans (le_max_left _ _), ?_⟩
  intro L hL x y hx hy
  let B : ℝ := ((L + 1 : ℕ) : ℝ)
  let z : ℕ := ⌊B ^ a⌋₊
  let M : ℕ := ⌊Real.log B⌋₊
  have hLpos : 1 ≤ L := by omega
  have hsum := hharmonic L (by omega)
  have hsumup : (∑ p ∈ mediumPrimes L z, 1 / (p : ℝ)) ≤ Real.log (1 / a) + windowConstant a / Real.log B := by
    linarith [(abs_le.mp hsum).2]
  have hsize := component_size_cost L hLpos
  have hp := hprime (L + 1) (by omega)
  have hcard : ((mediumPrimes L z).card : ℝ) ≤ 24 * B / Real.log B := by
    have hc : ((mediumPrimes L z).card : ℝ) ≤ (primeCount (10 * (L + 1)) : ℝ) := by
      exact_mod_cast medium_card_le_primeCount L z
    linarith
  have hweight := mul_le_mul_of_nonneg_left hsumup (show (0 : ℝ) ≤ 2 * B by positivity)
  have hret := retained_card_lower x y L z M hx hy
  unfold lossConstant
  simp only [div_eq_mul_inv] at hsize hcard hweight hret ⊢
  nlinarith

theorem critical_retained_lower (a : ℝ) (ha : 0 < a) (ha₁ : a ≤ 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ C : ℝ, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ x ∈ PaperP1.Model.dyadicBlock N, ∀ y ∈ PaperP1.Model.dyadicBlock N,
      (pairIntersectionRank x y L : ℝ) - (2 / 3) * ((L + 1 : ℕ) : ℝ) * Real.log (1 / a) -
        K * (((L + 1 : ℕ) : ℝ) / Real.log ((L + 1 : ℕ) : ℝ)) ≤
      ((retainedComponents x y L ⌊((L + 1 : ℕ) : ℝ) ^ a⌋₊
        ⌊Real.log ((L + 1 : ℕ) : ℝ)⌋₊).card : ℝ) := by
  obtain ⟨KD, hKD, hdefect⟩ := defectiveVertexCount_critical_bound
  obtain ⟨L₀, _hL₀, hretained⟩ := eventual_retained_lower a ha ha₁
  refine ⟨KD + lossConstant a, add_pos hKD (lossConstant_pos a ha), fun C ↦ ?_⟩
  obtain ⟨Ndef, hNdef⟩ := hdefect C
  obtain ⟨Nscale, hNscale⟩ := critical_band_scale C
  obtain ⟨Nlog, hNlog⟩ := eventually_atTop.mp
    (PrimeLogBudget.log_nat_tendsto_atTop.eventually
      (eventually_ge_atTop (((L₀ + 1 : ℕ) : ℝ) / lowerScale)))
  refine ⟨max 2 (max Ndef (max Nscale Nlog)), ?_⟩
  intro N hN L hband x hx y hy
  have hblog : ((L₀ + 1 : ℕ) : ℝ) ≤ lowerScale * Real.log N := by
    have h := (div_le_iff₀ lowerScale_pos).mp (hNlog N (by omega))
    nlinarith
  have hB := hblog.trans (hNscale N (by omega) L hband).1
  have hL : L₀ ≤ L := by
    have hn : L₀ + 1 ≤ L + 1 := by exact_mod_cast hB
    omega
  have hxpos : 1 ≤ x := by have h := (mem_Ico.mp hx).1; omega
  have hypos : 1 ≤ y := by have h := (mem_Ico.mp hy).1; omega
  have hret := hretained L hL x y hxpos hypos
  have hd := hNdef N (by omega) L hband x hx y hy
  simp only [div_eq_mul_inv] at hret hd ⊢
  nlinarith

end PaperP1.RetainedComponentAsymptotics
