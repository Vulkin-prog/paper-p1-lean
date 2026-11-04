module

public import PaperP1.Arithmetic.TwoKernelDeterminantScale
public import PaperP1.Arithmetic.IntegralSourceCoefficients

/-! # An actual large-product canonical point supplies every admissible source-box field -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CanonicalInteriorSourceBox

open Finset PaperP1.TwoKernelDeterminantBoxes PaperP1.TwoSmallKernelSquareParts
open PaperP1.TwoKernelDeterminantScale PaperP1.SmallPrimeBudget PaperP1.LargeOddKernel
open PaperP1.DefectivePredicate

theorem witness_box {N H h n c₁ c₂ D E U V : ℕ} (δ T : ℝ) (hN : 2 ≤ N)
    (_hδ : 0 < δ) (hδsmall : δ ≤ 1 / 2) (hD : 1 ≤ D) (hE : 1 ≤ E) (hU : 1 ≤ U) (hV : 1 ≤ V)
    (hn : 0 < n) (hnlo : N ≤ 2 * n) (hnhi : n ≤ 3 * N) (hmhi : n + h ≤ 4 * N)
    (hc₁ : smallOddPart H n = c₁) (hc₂ : smallOddPart H (n + h) = c₂)
    (hk₁ : (largeOddKernel H n : ℝ) ≤ T) (hk₂ : (largeOddKernel H (n + h) : ℝ) ≤ T)
    (hlargeD : 4 * Real.sqrt N < ((canonicalSquarePart n * canonicalSquarePart (n + h) : ℕ) : ℝ))
    (hlargeU : 4 * (N : ℝ) ^ δ < ((largeOddKernel H n * largeOddKernel H (n + h) : ℕ) : ℝ))
    (hbox : canonicalCode H h n ∈ solutions c₁ c₂ h D E U V) :
    ∃ X : DeterminantSourceBox.Box N (1 / 16) 4 δ,
      X.c₁ = (c₁ : ℝ) ∧ X.c₂ = (c₂ : ℝ) ∧ X.D = (D : ℝ) ∧ X.E = (E : ℝ) ∧ X.U = (U : ℝ) ∧ X.V = (V : ℝ) ∧
      (N : ℝ) ≤ X.c₁ * X.c₂ * (X.D * X.E) ^ 2 ∧ X.U ≤ T ∧ X.V ≤ T := by
  have hnR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn₁ : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hlogN : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hn₁
  have hc₁pos : 0 < c₁ := by rw [← hc₁]; exact smallOddPart_pos H n
  have hc₂pos : 0 < c₂ := by rw [← hc₂]; exact smallOddPart_pos H (n + h)
  have hc₁R : (1 : ℝ) ≤ c₁ := by exact_mod_cast hc₁pos
  have hc₂R : (1 : ℝ) ≤ c₂ := by exact_mod_cast hc₂pos
  have hDR : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hER : (1 : ℝ) ≤ E := by exact_mod_cast hE
  have hUR : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hVR : (1 : ℝ) ≤ V := by exact_mod_cast hV
  obtain ⟨hflo, hfhi, hglo, hghi, _hdheight, _heheight, hu, hv⟩ := canonical_box_bounds hn hc₁ hc₂ hbox
  obtain ⟨hp, _heq⟩ := mem_filter.mp hbox
  obtain ⟨hde, huv⟩ := mem_product.mp hp
  obtain ⟨hd, he⟩ := mem_product.mp hde
  obtain ⟨hu', hv'⟩ := mem_product.mp huv
  have hdhi : canonicalSquarePart n ≤ 2 * D := (mem_Ico.mp hd).2.le
  have hehi : canonicalSquarePart (n + h) ≤ 2 * E := (mem_Ico.mp he).2.le
  have huhi : largeOddKernel H n ≤ 2 * U := (mem_Ico.mp hu').2.le
  have hvhi : largeOddKernel H (n + h) ≤ 2 * V := (mem_Ico.mp hv').2.le
  have hprodD : ((canonicalSquarePart n * canonicalSquarePart (n + h) : ℕ) : ℝ) ≤ 4 * ((D : ℝ) * E) := by
    have hh := Nat.mul_le_mul hdhi hehi
    have hr : ((canonicalSquarePart n * canonicalSquarePart (n + h) : ℕ) : ℝ) ≤ (2 * (D : ℝ)) * (2 * E) := by exact_mod_cast hh
    nlinarith only [hr]
  have hprodU : ((largeOddKernel H n * largeOddKernel H (n + h) : ℕ) : ℝ) ≤ 4 * ((U : ℝ) * V) := by
    have hh := Nat.mul_le_mul huhi hvhi
    have hr : ((largeOddKernel H n * largeOddKernel H (n + h) : ℕ) : ℝ) ≤ (2 * (U : ℝ)) * (2 * V) := by exact_mod_cast hh
    nlinarith only [hr]
  have hDE : Real.sqrt N ≤ (D : ℝ) * E := by linarith only [hlargeD, hprodD]
  have hUV : (N : ℝ) ^ δ ≤ (U : ℝ) * V := by linarith only [hlargeU, hprodU]
  have hfirst : (δ * Real.log N) ≤ Real.log ((D : ℝ) * E) := by
    have hl := Real.log_le_log (Real.sqrt_pos.mpr hnR) hDE
    rw [Real.log_sqrt hnR.le] at hl
    have hm := mul_le_mul_of_nonneg_right hδsmall hlogN
    linarith only [hl, hm]
  have hsecond : (δ * Real.log N) ≤ Real.log ((U : ℝ) * V) := by
    have hl := Real.log_le_log (Real.rpow_pos_of_pos hnR δ) hUV
    simpa only [Real.log_rpow hnR] using hl
  have hcoeff : (1 : ℝ) ≤ (c₁ : ℝ) * c₂ := by
    nlinarith only [hc₁R, hc₂R, mul_nonneg (sub_nonneg.mpr hc₁R) (sub_nonneg.mpr hc₂R)]
  have hbarrier : (N : ℝ) ≤ (c₁ : ℝ) * c₂ * ((D : ℝ) * E) ^ 2 := by
    have hs := pow_le_pow_left₀ (Real.sqrt_nonneg (N : ℝ)) hDE 2
    rw [Real.sq_sqrt hnR.le] at hs
    have hh := mul_le_mul_of_nonneg_right hcoeff (sq_nonneg ((D : ℝ) * E))
    simp only [one_mul] at hh
    exact hs.trans hh
  have hfloR : (c₁ : ℝ) * (D : ℝ) ^ 2 * U ≤ n := by exact_mod_cast hflo
  have hfhiR : (n : ℝ) ≤ 8 * ((c₁ : ℝ) * (D : ℝ) ^ 2 * U) := by exact_mod_cast hfhi
  have hgloR : (c₂ : ℝ) * (E : ℝ) ^ 2 * V ≤ (n + h : ℕ) := by exact_mod_cast hglo
  have hghiR : ((n + h : ℕ) : ℝ) ≤ 8 * ((c₂ : ℝ) * (E : ℝ) ^ 2 * V) := by exact_mod_cast hghi
  have hnloR : (N : ℝ) ≤ 2 * n := by exact_mod_cast hnlo
  have hnhiR : (n : ℝ) ≤ 3 * N := by exact_mod_cast hnhi
  have hmhiR : ((n + h : ℕ) : ℝ) ≤ 4 * N := by exact_mod_cast hmhi
  have hnm : (n : ℝ) ≤ (n + h : ℕ) := by exact_mod_cast Nat.le_add_right n h
  let X : DeterminantSourceBox.Box N (1 / 16) 4 δ := {
    c₁ := c₁, c₂ := c₂, D := D, E := E, U := U, V := V
    c₁_ge_one := hc₁R, c₂_ge_one := hc₂R
    D_ge_one := hDR, E_ge_one := hER, U_ge_one := hUR, V_ge_one := hVR
    first_lower := by linarith only [hnloR, hfhiR]
    first_upper := by linarith only [hfloR, hnhiR, hnR]
    second_lower := by linarith only [hnloR, hnm, hghiR]
    second_upper := hgloR.trans hmhiR
    first_log := hfirst, second_log := hsecond }
  refine ⟨X, rfl, rfl, rfl, rfl, rfl, rfl, hbarrier, ?_, ?_⟩
  · exact (by exact_mod_cast hu : (U : ℝ) ≤ largeOddKernel H n).trans hk₁
  · exact (by exact_mod_cast hv : (V : ℝ) ≤ largeOddKernel H (n + h)).trans hk₂

theorem solutions_population {N h c₁ c₂ D E U V : ℕ} {ρ C δ : ℝ}
    (X : DeterminantSourceBox.Box N ρ C δ) (hc₁ : X.c₁ = (c₁ : ℝ)) (hc₂ : X.c₂ = (c₂ : ℝ))
    (hD : X.D = (D : ℝ)) (hE : X.E = (E : ℝ)) (hU : X.U = (U : ℝ)) (hV : X.V = (V : ℝ)) :
    DeterminantSignedBoxes.SignedPopulation X (h : ℤ) (solutions c₁ c₂ h D E U V) := by
  refine { d_bounds := ?_, e_bounds := ?_, u_bounds := ?_, v_bounds := ?_, equation := ?_ }
  all_goals intro p hp
  all_goals obtain ⟨hpbox, heq⟩ := mem_filter.mp hp
  all_goals obtain ⟨hde, huv⟩ := mem_product.mp hpbox
  all_goals obtain ⟨hd, he⟩ := mem_product.mp hde
  all_goals obtain ⟨hu, hv⟩ := mem_product.mp huv
  · rw [hD]
    exact ⟨by exact_mod_cast (mem_Ico.mp hd).1, by exact_mod_cast (mem_Ico.mp hd).2.le⟩
  · rw [hE]
    exact ⟨by exact_mod_cast (mem_Ico.mp he).1, by exact_mod_cast (mem_Ico.mp he).2.le⟩
  · rw [hU]
    exact ⟨by exact_mod_cast (mem_Ico.mp hu).1, by exact_mod_cast (mem_Ico.mp hu).2.le⟩
  · rw [hV]
    exact ⟨by exact_mod_cast (mem_Ico.mp hv).1, by exact_mod_cast (mem_Ico.mp hv).2.le⟩
  · rw [hc₁, hc₂]
    exact_mod_cast heq.symm

end PaperP1.CanonicalInteriorSourceBox
