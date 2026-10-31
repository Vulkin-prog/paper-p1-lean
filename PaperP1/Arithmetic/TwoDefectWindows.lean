module

public import PaperP1.Arithmetic.TwoDefectCount

@[expose] public section

/-! # Two defective values in the manuscript's exact dyadic run windows -/

namespace PaperP1.TwoDefectWindows

open Finset DefectivePredicate TwoDefectHosts

/-- The starts in [N,2N) whose full vertex window [x-1,x+L-1]
contains two distinct defective integers. -/
noncomputable def dyadicTwoDefectWindows (N H L : ℕ) : Finset ℕ := by
  classical
  exact (Ico N (2 * N)).filter fun x =>
    ∃ n ∈ Icc (x - 1) (x + L - 1), ∃ m ∈ Icc (x - 1) (x + L - 1),
      n ≠ m ∧ HDefective H n ∧ HDefective H m

theorem mem_dyadicTwoDefectWindows {N H L x : ℕ} :
    x ∈ dyadicTwoDefectWindows N H L ↔
      N ≤ x ∧ x < 2 * N ∧
        ∃ n ∈ Icc (x - 1) (x + L - 1), ∃ m ∈ Icc (x - 1) (x + L - 1),
          n ≠ m ∧ HDefective H n ∧ HDefective H m := by
  classical
  simp [dyadicTwoDefectWindows, and_assoc]

theorem shifted_start_mem_twoDefectStarts
    {N H L x : ℕ} (hN : 2 ≤ N) (hx : x ∈ dyadicTwoDefectWindows N H L) :
    x - 1 ∈ twoDefectStarts H L (2 * N) := by
  obtain ⟨hxN, hx2N, n, hn, m, hm, hnm, hdn, hdm⟩ := mem_dyadicTwoDefectWindows.mp hx
  obtain ⟨hnlo, hnhi⟩ := mem_Icc.mp hn
  obtain ⟨hmlo, hmhi⟩ := mem_Icc.mp hm
  let i := n - (x - 1)
  let j := m - (x - 1)
  have hi : i ≤ L := by dsimp [i]; omega
  have hj : j ≤ L := by dsimp [j]; omega
  have hnrep : x - 1 + i = n := by dsimp [i]; omega
  have hmrep : x - 1 + j = m := by dsimp [j]; omega
  apply mem_twoDefectStarts.mpr
  refine ⟨by omega, by omega, i, hi, j, hj, ?_, ?_, ?_⟩
  · intro hij
    apply hnm
    omega
  · simpa only [hnrep] using hdn
  · simpa only [hmrep] using hdm

theorem card_dyadicTwoDefectWindows_le {N H L : ℕ} (hN : 2 ≤ N) :
    (dyadicTwoDefectWindows N H L).card ≤ (twoDefectStarts H L (2 * N)).card := by
  classical
  have hinj : Set.InjOn (fun x : ℕ => x - 1) (dyadicTwoDefectWindows N H L : Set ℕ) := by
    intro x hx y hy heq
    change x - 1 = y - 1 at heq
    have hxlo := (mem_dyadicTwoDefectWindows.mp hx).1
    have hylo := (mem_dyadicTwoDefectWindows.mp hy).1
    omega
  have hsub : (dyadicTwoDefectWindows N H L).image (fun x => x - 1) ⊆
      twoDefectStarts H L (2 * N) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := mem_image.mp hy
    exact shifted_start_mem_twoDefectStarts hN hx
  calc
    _ = ((dyadicTwoDefectWindows N H L).image (fun x => x - 1)).card :=
      (card_image_of_injOn hinj).symm
    _ ≤ _ := card_le_card hsub

/-- The exact two-defect-window conclusion of companion T1.3, with a
threshold before all logarithmic cutoffs and run lengths. -/
theorem dyadic_two_defect_windows_le_rpow_eventually
    (D E : ℝ) (hD : 0 ≤ D) (hE : 0 ≤ E) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ H L : ℕ,
      (H : ℝ) ≤ D * Real.log N →
      (L : ℝ) ≤ E * Real.log N →
      ((dyadicTwoDefectWindows N H L).card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨Ncore, hcore⟩ := TwoDefectCount.two_defect_count_le_rpow_eventually
    2 D E (by norm_num) hD hE ε hε
  refine ⟨max Ncore 2, ?_⟩
  intro N hN H L hH hL
  have hNtwo : 2 ≤ N := (le_max_right _ _).trans hN
  have hbound := hcore N ((le_max_left _ _).trans hN) H L (2 * N) hH hL
    (by norm_num)
  exact (by exact_mod_cast card_dyadicTwoDefectWindows_le (H := H) (L := L) hNtwo :
    ((dyadicTwoDefectWindows N H L).card : ℝ) ≤
      ((twoDefectStarts H L (2 * N)).card : ℝ)).trans hbound

end PaperP1.TwoDefectWindows

