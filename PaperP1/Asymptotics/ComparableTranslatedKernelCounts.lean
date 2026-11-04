module

public import PaperP1.Asymptotics.TranslatedKernelCounts
public import PaperP1.Asymptotics.ComparableTwoSmallKernelUpper

/-! # Translated two-small-kernel windows with a fixed lower comparison -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ComparableTranslatedKernelCounts

open Finset PaperP1.TranslatedKernelWindows PaperP1.LargeOddKernel

theorem two_uniform_budget (Q : ℕ) (D ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ H U : ℕ, H ≤ N → 2 ≤ U → U ≤ N → N ≤ Q * (U - 1) →
      (H : ℝ) ≤ D * Real.log N → ∀ T : ℝ, 0 ≤ T →
      ((twoStarts N H U T).card : ℝ) ≤ (T + (N : ℝ) ^ (2 / 3 : ℝ)) * (N : ℝ) ^ ε := by
  obtain ⟨Na, _hNa, ha⟩ := ComparableTwoSmallKernelUpper.uniform_count (Q + 3) (by omega) D D 1 (ε / 2) (by positivity)
  obtain ⟨Np, hp⟩ := SplitQuadraticCongruenceCount.polylog_le_rpow D 1 (ε / 4) (by positivity)
  refine ⟨max 4 (max Na Np), by omega, ?_⟩
  intro N hN H U hH hU hUN hUratio hlog T hT
  classical
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  let S := twoStarts N H U T
  let I := (range H) ×ˢ (Icc 1 H)
  let F := fun w : ℕ × ℕ ↦ S.filter fun x ↦
    (largeOddKernel H (x - 1 + w.1) : ℝ) ≤ T ∧ (largeOddKernel H (x - 1 + w.1 + w.2) : ℝ) ≤ T
  have hcover : ∀ x ∈ S, ∃ w ∈ I, x ∈ F w := by
    intro x hx
    obtain ⟨i, hi, h, hh, hk₁, hk₂⟩ := two_witness hx
    exact ⟨(i, h), mem_product.mpr ⟨hi, hh⟩, mem_filter.mpr ⟨hx, hk₁, hk₂⟩⟩
  have hF : ∀ w ∈ I, ((F w).card : ℝ) ≤ (T + (N : ℝ) ^ (2 / 3 : ℝ)) * (N : ℝ) ^ (ε / 2) := by
    intro w hwI
    obtain ⟨hi, hh⟩ := mem_product.mp hwI
    let f : ℕ → ℕ := fun x ↦ x - 1 + w.1
    have hinj := translated_injective hU w.1 (F w) (by
      intro x hx
      exact (mem_filter.mp (mem_filter.mp hx).1).1)
    rw [← card_image_of_injOn hinj]
    apply ha N (by omega) H w.2 T hlog (mem_Icc.mp hh).1
      (by
        have hh' : (w.2 : ℝ) ≤ H := by exact_mod_cast (mem_Icc.mp hh).2
        simpa only [Real.rpow_one] using hh'.trans hlog) hT ((F w).image f)
    intro n hnF
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hnF
    obtain ⟨hxS, hk₁, hk₂⟩ := mem_filter.mp hx
    obtain ⟨hxlo, hxhi⟩ := mem_Ico.mp (mem_filter.mp hxS).1
    have hi' := mem_range.mp hi
    have hh' := mem_Icc.mp hh
    have hnhi : x - 1 + w.1 ≤ 3 * N := by omega
    refine ⟨?_, ?_, hk₁, hk₂⟩
    · calc
        N ≤ Q * (U - 1) := hUratio
        _ ≤ Q * (x - 1 + w.1) := Nat.mul_le_mul_left Q (by omega)
        _ ≤ (Q + 3) * (x - 1 + w.1) := Nat.mul_le_mul_right _ (by omega)
    · exact hnhi.trans (Nat.mul_le_mul_right N (by omega))

  have hB : (H : ℝ) ≤ (N : ℝ) ^ (ε / 4) := hlog.trans (by
    simpa only [Real.rpow_one] using hp N (by omega))
  have hI : (I.card : ℝ) ≤ (N : ℝ) ^ (ε / 2) := by
    calc
      _ = (H : ℝ) * H := by
        simp only [I, card_product, card_range, Nat.card_Icc, Nat.add_sub_cancel, Nat.cast_mul]
      _ ≤ (N : ℝ) ^ (ε / 4) * (N : ℝ) ^ (ε / 4) :=
        mul_le_mul hB hB (Nat.cast_nonneg _) (Real.rpow_nonneg hn.le _)
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


end PaperP1.ComparableTranslatedKernelCounts
