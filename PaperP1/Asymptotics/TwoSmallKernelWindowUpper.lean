module

public import PaperP1.Arithmetic.TwoSmallKernelWindowCover
public import PaperP1.Asymptotics.TwoSmallKernelElementaryUpper

/-! # An unconditional upper exponent and sharpness for beta at least two thirds -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoSmallKernelWindowUpper

open Finset PaperP1.TwoSmallKernelWindows PaperP1.LargeOddKernel PaperP1.Model

local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem uniform_budget (D E A ε : ℝ) (hD : 0 ≤ D) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ H L : ℕ, ∀ T : ℝ,
      (H : ℝ) ≤ D * Real.log N → (L + 1 : ℕ) ≤ E * (Real.log N) ^ A → L ≤ N → 0 ≤ T →
      ((windows N L H T).card : ℝ) ≤ (T + (N : ℝ) ^ (2 / 3 : ℝ)) * (N : ℝ) ^ ε := by
  obtain ⟨NU, _hNU, hu⟩ := TwoSmallKernelElementaryUpper.uniform_count D E A (ε / 2) hD (by positivity)
  obtain ⟨NW, hw⟩ := SplitQuadraticCongruenceCount.polylog_le_rpow E A (ε / 4) (by positivity)
  refine ⟨max 4 (max NU NW), by omega, ?_⟩
  intro N hN H L T hH hwidth hL hT
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  let S := windows N L H T
  let I := (range (L + 1)) ×ˢ (Icc 1 L)
  let F := fun w : ℕ × ℕ ↦ S.filter fun x ↦
    (largeOddKernel H (x - 1 + w.1) : ℝ) ≤ T ∧ (largeOddKernel H (x - 1 + w.1 + w.2) : ℝ) ≤ T
  have hcover : ∀ x ∈ S, ∃ w ∈ I, x ∈ F w := by
    intro x hx
    obtain ⟨i, hi, h, hh, hk₁, hk₂⟩ := TwoSmallKernelWindowCover.witness (by omega : 0 < N) hx
    exact ⟨(i, h), mem_product.mpr ⟨hi, hh⟩, mem_filter.mpr ⟨hx, hk₁, hk₂⟩⟩
  have hF : ∀ w ∈ I, ((F w).card : ℝ) ≤ (T + (N : ℝ) ^ (2 / 3 : ℝ)) * (N : ℝ) ^ (ε / 2) := by
    intro w hwI
    obtain ⟨hi, hh⟩ := mem_product.mp hwI
    let f : ℕ → ℕ := fun x ↦ x - 1 + w.1
    have hinj := TwoSmallKernelWindowCover.translated_injective (by omega : 2 ≤ N) w.1 (F w) (by
      intro x hx
      exact (mem_filter.mp (mem_filter.mp hx).1).1)
    rw [← card_image_of_injOn hinj]
    apply hu N (by omega) H w.2 T hH (mem_Icc.mp hh).1
      (by have hh' : (w.2 : ℝ) ≤ (L + 1 : ℕ) := by exact_mod_cast (show w.2 ≤ L + 1 by have := (mem_Icc.mp hh).2; omega)
          exact hh'.trans hwidth) hT ((F w).image f)
    intro n hnF
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hnF
    obtain ⟨hxS, hk₁, hk₂⟩ := mem_filter.mp hx
    have hxd := (mem_filter.mp hxS).1
    obtain ⟨hnpos, hnlo, hnhi, hmhi⟩ := TwoSmallKernelWindowCover.translated_heights (by omega : 2 ≤ N) hL hxd hi hh
    exact ⟨hnpos, hnlo, hnhi, hmhi, hk₁, hk₂⟩
  have hB : ((L + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ (ε / 4) := hwidth.trans (hw N (by omega))
  have hI : (I.card : ℝ) ≤ (N : ℝ) ^ (ε / 2) := by
    calc
      _ = ((L + 1 : ℕ) : ℝ) * L := by simp only [I, card_product, card_range, Nat.card_Icc, Nat.add_sub_cancel, Nat.cast_mul]
      _ ≤ ((L + 1 : ℕ) : ℝ) * (L + 1 : ℕ) := mul_le_mul_of_nonneg_left (by exact_mod_cast (Nat.le_succ L)) (Nat.cast_nonneg _)
      _ ≤ (N : ℝ) ^ (ε / 4) * (N : ℝ) ^ (ε / 4) := mul_le_mul hB hB (Nat.cast_nonneg _) (Real.rpow_nonneg hn.le _)
      _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring
  calc
    _ ≤ (I.card : ℝ) * ((T + (N : ℝ) ^ (2 / 3 : ℝ)) * (N : ℝ) ^ (ε / 2)) :=
      FiniteCoverCount.cardinal_le S I F _ hcover hF
    _ ≤ (N : ℝ) ^ (ε / 2) * ((T + (N : ℝ) ^ (2 / 3 : ℝ)) * (N : ℝ) ^ (ε / 2)) :=
      mul_le_mul_of_nonneg_right hI (by positivity)
    _ = _ := by
      calc
        _ = (T + (N : ℝ) ^ (2 / 3 : ℝ)) * ((N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / 2)) := by ring
        _ = _ := by rw [← Real.rpow_add hn, add_halves]

theorem critical_budget (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ, ∀ T : ℝ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → 0 ≤ T →
      ((windows N L (L + 1) T).card : ℝ) ≤ (T + (N : ℝ) ^ (2 / 3 : ℝ)) * (N : ℝ) ^ ε := by
  obtain ⟨NU, _hNU, hu⟩ := uniform_budget CriticalBandScale.upperScale CriticalBandScale.upperScale 1 ε
    CriticalBandScale.upperScale_pos.le hε
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 1
  refine ⟨max 4 (max NU NG), by omega, ?_⟩
  intro N hN L T hband hT
  obtain ⟨_hNtwo, _hBmin, _hBtwo, hlarge, _hBlo, hBhi⟩ := hg N (by omega) L hband
  exact hu N (by omega) (L + 1) L T hBhi (by simpa only [Real.rpow_one] using hBhi) (by omega) hT

theorem critical_upper (β C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ((windows N L (L + 1) ((N : ℝ) ^ β)).card : ℝ) ≤ (N : ℝ) ^ (max β (2 / 3) + ε) := by
  obtain ⟨NB, _hNB, hb⟩ := critical_budget C (ε / 2) (by positivity)
  obtain ⟨NC, hc⟩ := HalfCountSchedule.factor_absorption 2 0 (ε / 2) (by positivity)
  refine ⟨max 4 (max NB NC), by omega, ?_⟩
  intro N hN L hband
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn₁ : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hβ : (N : ℝ) ^ β ≤ (N : ℝ) ^ (max β (2 / 3)) := Real.rpow_le_rpow_of_exponent_le hn₁ (le_max_left _ _)
  have hthird : (N : ℝ) ^ (2 / 3 : ℝ) ≤ (N : ℝ) ^ (max β (2 / 3)) := Real.rpow_le_rpow_of_exponent_le hn₁ (le_max_right _ _)
  have hconst : 2 ≤ (N : ℝ) ^ (ε / 2) := by simpa only [Real.rpow_zero, mul_one, zero_add] using hc N (by omega)
  calc
    _ ≤ ((N : ℝ) ^ β + (N : ℝ) ^ (2 / 3 : ℝ)) * (N : ℝ) ^ (ε / 2) := hb N (by omega) L _ hband (by positivity)
    _ ≤ ((N : ℝ) ^ (max β (2 / 3)) * (N : ℝ) ^ (ε / 2)) * (N : ℝ) ^ (ε / 2) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      have hh' := mul_le_mul_of_nonneg_left hconst (Real.rpow_nonneg hn.le (max β (2 / 3)))
      nlinarith only [hβ, hthird, hh']
    _ = _ := by rw [mul_assoc, ← Real.rpow_add hn, add_halves, ← Real.rpow_add hn]

theorem critical_sharp (β C ε : ℝ) (hβlo : 2 / 3 ≤ β) (hβhi : β < 1) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      (N : ℝ) ^ (β - ε) ≤ ((windows N L (L + 1) ((N : ℝ) ^ β)).card : ℝ) ∧
      ((windows N L (L + 1) ((N : ℝ) ^ β)).card : ℝ) ≤ (N : ℝ) ^ (β + ε) := by
  obtain ⟨NL, _hNL, hl⟩ := critical_lower β ε C (by linarith only [hβlo]) hβhi hε
  obtain ⟨NU, _hNU, hu⟩ := critical_upper β C ε hε
  refine ⟨max 10 (max NL NU), by omega, ?_⟩
  intro N hN L hband
  exact ⟨hl N (by omega) L hband, by simpa only [max_eq_left hβlo] using hu N (by omega) L hband⟩

end PaperP1.TwoSmallKernelWindowUpper
