module

public import PaperP1.Arithmetic.TwoSmallKernelBlocks
public import PaperP1.Asymptotics.SharpComparableTwoSmallKernelCount

/-! # Apply sharp counting to every actual offset pair in arbitrary selected blocks -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoSmallKernelBlockCount

open Finset PaperP1.TwoSmallKernelBlocks PaperP1.LargeOddKernel

theorem logarithmic_blocks (hHB : HeathBrownBiformInput.Input) (hNG : NonGeometricBiformInput.Input)
    (Q : ℕ) (hQ : 1 ≤ Q) (D E ε : ℝ) (_hD : 0 ≤ D) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ G O : Finset ℤ, ∀ H R : ℕ,
      (R : ℝ) ≤ D * Real.log N → (H : ℝ) ≤ E * Real.log N → O ⊆ Icc (-(R : ℤ)) R →
      (∀ x ∈ G, ∀ u ∈ O, 0 < x + u → N ≤ Q * (x + u).toNat ∧ (x + u).toNat ≤ Q * N) →
      ∀ T : ℝ, 0 ≤ T → ((starts G O H T).card : ℝ) ≤ (T + (N : ℝ) ^ (7 / 12 : ℝ)) * (N : ℝ) ^ ε := by
  classical
  obtain ⟨Nc, _hNc, hc⟩ := SharpComparableTwoSmallKernelCount.uniform_count hHB hNG Q hQ E (2 * D) 1 (ε / 2)
    (by norm_num) (by positivity)
  obtain ⟨Np, hp⟩ := SplitQuadraticCongruenceCount.polylog_le_rpow (2 * D + 1) 1 (ε / 4) (by positivity)
  refine ⟨max 2 (max ⌈Real.exp (1 : ℝ)⌉₊ (max Nc Np)), ?_⟩
  intro N hN G O H R hR hH hO hheight T hT
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hexp : Real.exp (1 : ℝ) ≤ N :=
    (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈Real.exp (1 : ℝ)⌉₊ ≤ N by omega))
  have hlog : 1 ≤ Real.log (N : ℝ) := by
    have hh := Real.log_le_log (Real.exp_pos (1 : ℝ)) hexp
    simpa only [Real.log_exp] using hh
  let I := (O ×ˢ O).filter (fun uv ↦ uv.1 < uv.2)
  let F := fun uv : ℤ × ℤ ↦ offsetPairStarts G H T uv.1 uv.2
  let B := T + (N : ℝ) ^ (7 / 12 : ℝ)
  have hF : ∀ uv ∈ I, ((F uv).card : ℝ) ≤ B * (N : ℝ) ^ (ε / 2) := by
    intro uv huv
    obtain ⟨hpool, horder⟩ := mem_filter.mp huv
    obtain ⟨hu, hv⟩ := mem_product.mp hpool
    obtain ⟨hgap, hgaphi⟩ := offset_gap R uv.1 uv.2 (hO hu) (hO hv) horder
    have hshift : ((uv.2 - uv.1).toNat : ℝ) ≤ (2 * D) * (Real.log N) ^ (1 : ℝ) := by
      have hcast : ((uv.2 - uv.1).toNat : ℝ) ≤ 2 * R := by exact_mod_cast hgaphi
      rw [Real.rpow_one]
      linarith only [hcast, hR]
    rw [← card_image_of_injOn (fixed_pair_injective G H T uv.1 uv.2)]
    apply hc N (by omega) H (uv.2 - uv.1).toNat T hH hgap hshift hT
      ((F uv).image (fun x : ℤ ↦ (x + uv.1).toNat))
    intro n hnS
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hnS
    obtain ⟨hxG, hxpos, _hxvpos, hk₁, hk₂⟩ := mem_filter.mp hx
    obtain ⟨hnlo, hnhi⟩ := hheight x hxG uv.1 hu hxpos
    refine ⟨hnlo, hnhi, hk₁, ?_⟩
    rw [pair_translation x uv.1 uv.2 hxpos horder]
    exact hk₂
  have hOfull : (Icc (-(R : ℤ)) R).card = 2 * R + 1 := by rw [Int.card_Icc]; omega
  have hOcard : (O.card : ℝ) ≤ 2 * (R : ℝ) + 1 := by
    exact_mod_cast (card_le_card hO).trans_eq hOfull
  have hOlog : (O.card : ℝ) ≤ (2 * D + 1) * Real.log N := by linarith only [hOcard, hR, hlog]
  have hObudget : (O.card : ℝ) ≤ (N : ℝ) ^ (ε / 4) := by
    have hh := hp N (by omega)
    rw [Real.rpow_one] at hh
    exact hOlog.trans hh
  have hI : (I.card : ℝ) ≤ (N : ℝ) ^ (ε / 2) := by
    have hi : I.card ≤ (O ×ˢ O).card := card_filter_le _ _
    calc
      _ ≤ (O.card : ℝ) * O.card := by
        simpa only [card_product, Nat.cast_mul] using (show (I.card : ℝ) ≤ (O ×ˢ O).card by exact_mod_cast hi)
      _ ≤ (N : ℝ) ^ (ε / 4) * (N : ℝ) ^ (ε / 4) :=
        mul_le_mul hObudget hObudget (Nat.cast_nonneg _) (Real.rpow_nonneg hn.le _)
      _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring
  have hcover : ((starts G O H T).card : ℝ) ≤ ∑ uv ∈ I, ((F uv).card : ℝ) := by
    exact_mod_cast (card_biUnion_le : (I.biUnion F).card ≤ ∑ uv ∈ I, (F uv).card)
  calc
    _ ≤ ∑ uv ∈ I, ((F uv).card : ℝ) := hcover
    _ ≤ ∑ _uv ∈ I, B * (N : ℝ) ^ (ε / 2) := sum_le_sum hF
    _ = (I.card : ℝ) * (B * (N : ℝ) ^ (ε / 2)) := by simp only [sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ) ^ (ε / 2) * (B * (N : ℝ) ^ (ε / 2)) :=
      mul_le_mul_of_nonneg_right hI (by dsimp only [B]; positivity)
    _ = _ := by
      calc
        _ = B * ((N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / 2)) := by ring
        _ = _ := by rw [← Real.rpow_add hn, add_halves]

theorem arbitrary_selected_blocks (hHB : HeathBrownBiformInput.Input) (hNG : NonGeometricBiformInput.Input)
    (Q : ℕ) (hQ : 1 ≤ Q) (D E ε : ℝ) (hD : 0 ≤ D) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ G O : Finset ℤ, ∀ H R : ℕ,
      (R : ℝ) ≤ D * Real.log N → (H : ℝ) ≤ E * Real.log N → O ⊆ Icc (-(R : ℤ)) R →
      (∀ x ∈ G, ∀ u ∈ O, 0 < x + u → N ≤ Q * (x + u).toNat ∧ (x + u).toNat ≤ Q * N) →
      ∀ V : ℤ → Finset ℕ, (∀ x ∈ G, ∀ n ∈ V x, 0 < n ∧ (n : ℤ) - x ∈ O) →
      ∀ T : ℝ, 0 ≤ T → ((selectedStarts G V H T).card : ℝ) ≤ (T + (N : ℝ) ^ (7 / 12 : ℝ)) * (N : ℝ) ^ ε := by
  obtain ⟨N₀, hN₀⟩ := logarithmic_blocks hHB hNG Q hQ D E ε hD hε
  refine ⟨N₀, ?_⟩
  intro N hN G O H R hR hH hO hheight V hV T hT
  have hc : ((selectedStarts G V H T).card : ℝ) ≤ (starts G O H T).card := by
    exact_mod_cast card_le_card (selected_subset hV)
  exact hc.trans (hN₀ N hN G O H R hR hH hO hheight T hT)

end PaperP1.TwoSmallKernelBlockCount
