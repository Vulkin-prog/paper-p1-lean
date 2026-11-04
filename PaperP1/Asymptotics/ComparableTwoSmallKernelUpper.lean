module

public import PaperP1.Asymptotics.TwoSmallKernelElementaryUpper
public import PaperP1.Asymptotics.ComparableSplitProductCount

/-! # Two small kernels on any fixed comparable positive range -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ComparableTwoSmallKernelUpper

open Finset PaperP1.ComparableDyadicCover PaperP1.ComparableLogBounds PaperP1.LargeOddKernel

theorem uniform_count (Q : ℕ) (hQ : 1 ≤ Q) (D E A ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ H h : ℕ, ∀ T : ℝ,
      (H : ℝ) ≤ D * Real.log N → 0 < h → (h : ℝ) ≤ E * (Real.log N) ^ A → 0 ≤ T →
      ∀ S : Finset ℕ, (∀ n ∈ S, N ≤ Q * n ∧ n ≤ Q * N ∧
        (largeOddKernel H n : ℝ) ≤ T ∧ (largeOddKernel H (n + h) : ℝ) ≤ T) →
      (S.card : ℝ) ≤ (T + (N : ℝ) ^ (2 / 3 : ℝ)) * (N : ℝ) ^ ε := by
  let δ := ε / 2
  let d := distortion Q
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hd : 1 ≤ d := distortion_ge_one Q
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨Mc, _hMc, hc⟩ := TwoSmallKernelElementaryUpper.uniform_count
    (widthConstant D 1) (widthConstant E A) A δ
    (le_trans zero_le_one (widthConstant_ge_one D 1)) hδ
  obtain ⟨Nw, hw⟩ := ComparableSplitProductCount.width_lt_centre d E A
  obtain ⟨Nf, hf⟩ := HalfCountSchedule.factor_absorption
    (((indices Q).card : ℝ) * (d : ℝ) ^ (2 / 3 + δ)) 0 (ε - δ) (by dsimp [δ]; linarith)
  refine ⟨max 4 (max (2 * Q) (max (d ^ 2) (max (d * max 2 Mc) (max Nw Nf)))), by omega, ?_⟩
  intro N hN H h T hH hh hwidth hT S hS
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  let F := fun j ↦ S.filter fun n ↦ base Q N j ≤ n ∧ n ≤ 2 * base Q N j
  have hcover : ∀ n ∈ S, ∃ j ∈ indices Q, n ∈ F j := by
    intro n hn
    obtain ⟨j, hj, hbox⟩ := cover Q N n hQ (by omega) (hS n hn).1 (hS n hn).2.1
    exact ⟨j, hj, mem_filter.mpr ⟨hn, hbox⟩⟩
  have hcell : ∀ j ∈ indices Q, ((F j).card : ℝ) ≤
      (d : ℝ) ^ (2 / 3 + δ) * ((T + (N : ℝ) ^ (2 / 3 : ℝ)) * (N : ℝ) ^ δ) := by
    intro j hj
    let M := base Q N j
    have hcomp := base_comparison Q N j hQ (by omega) hj
    have hMlarge : max 2 Mc ≤ M := base_large Q N j (max 2 Mc) hQ (by omega) hj (by
      change d * max 2 Mc ≤ N
      omega)
    have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
    have hHM : (H : ℝ) ≤ widthConstant D 1 * Real.log M := by
      have hH' : (H : ℝ) ≤ D * (Real.log N) ^ (1 : ℝ) := by simpa only [Real.rpow_one] using hH
      simpa only [Real.rpow_one] using width_transfer D 1 d N M H hd (by omega) (by omega)
        hcomp.1 hcomp.2 hH'
    have hhM := width_transfer E A d N M h hd (by omega) (by omega) hcomp.1 hcomp.2 hwidth
    have hgap : h < M := hw N (by omega) M h hcomp.1 hwidth
    have hcount : ((F j).card : ℝ) ≤ (T + (M : ℝ) ^ (2 / 3 : ℝ)) * (M : ℝ) ^ δ :=
      hc M (by omega) H h T hHM hh hhM hT (F j) (by
        intro n hn
        obtain ⟨hnS, hbox⟩ := mem_filter.mp hn
        have hnlo := hbox.1
        have hnhi := hbox.2
        exact ⟨by omega, by omega, by omega, by omega, (hS n hnS).2.2.1, (hS n hnS).2.2.2⟩)
    have hMbound : (M : ℝ) ≤ (d : ℝ) * N := by exact_mod_cast hcomp.2
    have hpowδ := Real.rpow_le_rpow hMpos.le hMbound hδ.le
    have hpowmain := Real.rpow_le_rpow hMpos.le hMbound
      (show 0 ≤ (2 / 3 : ℝ) + δ by positivity)
    rw [Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)] at hpowδ hpowmain
    have hdexp : (d : ℝ) ^ δ ≤ (d : ℝ) ^ (2 / 3 + δ) :=
      Real.rpow_le_rpow_of_exponent_le hdR (by linarith)
    have hδbound : (M : ℝ) ^ δ ≤ (d : ℝ) ^ (2 / 3 + δ) * (N : ℝ) ^ δ :=
      hpowδ.trans (mul_le_mul_of_nonneg_right hdexp (Real.rpow_nonneg hNpos.le _))
    calc
      _ ≤ (T + (M : ℝ) ^ (2 / 3 : ℝ)) * (M : ℝ) ^ δ := hcount
      _ = T * (M : ℝ) ^ δ + (M : ℝ) ^ (2 / 3 + δ) := by
        rw [Real.rpow_add hMpos]
        ring
      _ ≤ T * ((d : ℝ) ^ (2 / 3 + δ) * (N : ℝ) ^ δ) +
          (d : ℝ) ^ (2 / 3 + δ) * (N : ℝ) ^ (2 / 3 + δ) :=
        add_le_add (mul_le_mul_of_nonneg_left hδbound hT) hpowmain
      _ = _ := by rw [Real.rpow_add hNpos]; ring
  have htotal := FiniteCoverCount.cardinal_le S (indices Q) F _ hcover hcell
  have hfactor : ((indices Q).card : ℝ) * (d : ℝ) ^ (2 / 3 + δ) ≤ (N : ℝ) ^ (ε - δ) := by
    simpa only [Real.rpow_zero, mul_one, zero_add] using hf N (by omega)
  calc
    _ ≤ (((indices Q).card : ℝ) * (d : ℝ) ^ (2 / 3 + δ)) *
        ((T + (N : ℝ) ^ (2 / 3 : ℝ)) * (N : ℝ) ^ δ) := by
      simpa only [mul_assoc] using htotal
    _ ≤ (N : ℝ) ^ (ε - δ) * ((T + (N : ℝ) ^ (2 / 3 : ℝ)) * (N : ℝ) ^ δ) :=
      mul_le_mul_of_nonneg_right hfactor (by positivity)
    _ = _ := by rw [mul_left_comm, ← Real.rpow_add hNpos, sub_add_cancel]

end PaperP1.ComparableTwoSmallKernelUpper
