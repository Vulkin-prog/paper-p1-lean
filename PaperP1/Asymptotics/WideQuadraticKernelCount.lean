module

public import PaperP1.Asymptotics.WideQuadraticSquarePartCount
public import PaperP1.Asymptotics.PrescribedQuadraticKernelTheorem

/-! # Uniform affine quadratic-kernel counts on N/2 <= n <= 3N -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.WideQuadraticKernelCount

open Finset PaperP1.QuadraticKernelFibres PaperP1.QuadraticKernelExponents

theorem three_exponent_bounds (D A₀ ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ h e : ℕ, ∀ β : ℝ, 0 < h → 0 < e →
      (h : ℝ) ≤ D * (Real.log N) ^ A₀ → ∀ S : Finset ℕ,
        (∀ n ∈ S, N ≤ 2 * n ∧ n ≤ 3 * N ∧ (N : ℝ) ^ β ≤ kernel h n ∧
          (kernel h n : ℝ) < 2 * (N : ℝ) ^ β ∧ e ∣ kernel h n) →
        (S.card : ℝ) ≤ (N : ℝ) ^ (1 + ε) ∧
        (S.card : ℝ) ≤ (N : ℝ) ^ (β - Real.log e / Real.log N + ε) ∧
        (S.card : ℝ) ≤ (N : ℝ) ^
          (max (β / 2 - Real.log e / Real.log N) (1 - β / 2) + ε) := by
  obtain ⟨Nf, hNf⟩ := PaperP1.PrescribedQuadraticKernelCount.real_first_branch_count 2
    (ε / 2) (by positivity)
  obtain ⟨Ns, hNs⟩ := PaperP1.WideQuadraticSquarePartCount.second_branch_count D A₀ (ε / 2) (by positivity)
  obtain ⟨Nh, hNh⟩ := PaperP1.SplitQuadraticCongruenceCount.polylog_le_rpow D A₀ 1 (by norm_num)
  obtain ⟨Nc, hNc⟩ := PaperP1.UniformReal.uniformSubpolynomialOn_le_rpow
    (PaperP1.ExpSqrtLog.uniformSubpolynomialOn_const (fun _ _ : ℕ ↦ True) 3) (ε / 2) (by positivity)
  refine ⟨max 3 (max Nf (max Ns (max Nh Nc))), ?_⟩
  intro N hN h e β hh he hshift S hS
  have hNtwo : 3 ≤ N := by omega
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hp : 0 ≤ (N : ℝ) ^ (ε / 2) := Real.rpow_nonneg hn.le _
  have hpmono : (N : ℝ) ^ (ε / 2) ≤ (N : ℝ) ^ ε :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hc : (3 : ℝ) ≤ (N : ℝ) ^ (ε / 2) := (le_abs_self _).trans (hNc N (by omega) 0 trivial)
  have hhN : h ≤ N := by
    have hr := hshift.trans (hNh N (by omega))
    simpa only [Real.rpow_one, Nat.cast_le] using hr
  have htwo : 3 * N ≤ N ^ 2 := by nlinarith
  obtain ⟨hi1, hi2, hi3⟩ := PaperP1.PrescribedQuadraticKernelTheorem.size_identities N e (by omega) he β
  have hf := hNf N (by omega) (3 * N) h e ((N : ℝ) ^ β)
    (Real.rpow_nonneg hn.le _) hh he htwo (hhN.trans (by nlinarith : N ≤ N ^ 2)) S (by
      intro n hmem
      obtain ⟨hlo, hhi, _, hqhi, hdiv⟩ := hS n hmem
      exact ⟨by omega, hhi, hqhi, hdiv⟩)
  rw [hi1] at hf
  have hs := hNs N (by omega) h e ((N : ℝ) ^ β) (Real.rpow_pos_of_pos hn _) hh he hshift S hS
  rw [hi2, hi3] at hs
  have htriv : (S.card : ℝ) ≤ 3 * N := by
    apply PaperP1.QuadraticKernelRanges.positive_card (3 * N) (by positivity)
    intro n hmem
    exact ⟨by have hlo := (hS n hmem).1; omega, by exact_mod_cast (hS n hmem).2.1⟩
  refine ⟨?_, ?_, ?_⟩
  · calc
      _ ≤ 3 * (N : ℝ) := htriv
      _ ≤ (N : ℝ) ^ ε * N := mul_le_mul_of_nonneg_right (hc.trans hpmono) hn.le
      _ = _ := by rw [Real.rpow_add hn, Real.rpow_one]; ring
  · calc
      _ ≤ (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (β - Real.log e / Real.log N) := hf
      _ ≤ (N : ℝ) ^ ε * (N : ℝ) ^ (β - Real.log e / Real.log N) :=
        mul_le_mul_of_nonneg_right hpmono (Real.rpow_nonneg hn.le _)
      _ = _ := by rw [Real.rpow_add hn]; ring
  · let m := max (β / 2 - Real.log e / Real.log N) (1 - β / 2)
    have hb1 : (N : ℝ) ^ (β / 2 - Real.log e / Real.log N) ≤ (N : ℝ) ^ m :=
      Real.rpow_le_rpow_of_exponent_le hn1 (le_max_left _ _)
    have hb2 : (N : ℝ) ^ (1 - β / 2) ≤ (N : ℝ) ^ m :=
      Real.rpow_le_rpow_of_exponent_le hn1 (le_max_right _ _)
    calc
      _ ≤ (N : ℝ) ^ (ε / 2) * ((N : ℝ) ^ (β / 2 - Real.log e / Real.log N) +
          (N : ℝ) ^ (1 - β / 2)) := hs
      _ ≤ (N : ℝ) ^ (ε / 2) * (2 * (N : ℝ) ^ m) :=
        mul_le_mul_of_nonneg_left (by linarith) hp
      _ = (2 * (N : ℝ) ^ (ε / 2)) * (N : ℝ) ^ m := by ring
      _ ≤ ((N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / 2)) * (N : ℝ) ^ m :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith : (2 : ℝ) ≤ (N : ℝ) ^ (ε / 2)) hp) (Real.rpow_nonneg hn.le _)
      _ = (N : ℝ) ^ (m + ε) := by
        rw [← Real.rpow_add hn, ← Real.rpow_add hn]
        congr 1
        dsimp [m]
        ring

theorem uniform_affine_count (D A₀ ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ h e : ℕ, ∀ β : ℝ, 0 < h → 0 < e →
      (h : ℝ) ≤ D * (Real.log N) ^ A₀ → ∀ S : Finset ℕ,
        (∀ n ∈ S, N ≤ 2 * n ∧ n ≤ 3 * N ∧ (N : ℝ) ^ β ≤ kernel h n ∧
          (kernel h n : ℝ) < 2 * (N : ℝ) ^ β ∧ e ∣ kernel h n) →
        (S.card : ℝ) ≤ (N : ℝ) ^ (affine β (Real.log e / Real.log N) + ε) := by
  obtain ⟨N₀, hN₀⟩ := three_exponent_bounds D A₀ ε hε
  refine ⟨max 2 N₀, ?_⟩
  intro N hN h e β hh he hshift S hS
  obtain ⟨ht, hf, hs⟩ := hN₀ N (by omega) h e β hh he hshift S hS
  have hexp : (S.card : ℝ) ≤ (N : ℝ) ^ (exponent β (Real.log e / Real.log N) + ε) := by
    unfold exponent
    rcases le_total (β - Real.log e / Real.log N)
      (max (β / 2 - Real.log e / Real.log N) (1 - β / 2)) with ha | ha
    · simpa only [min_eq_left ha] using hf
    · simpa only [min_eq_right ha] using hs
  have hcap : (S.card : ℝ) ≤ (N : ℝ) ^ (capped β (Real.log e / Real.log N) + ε) := by
    unfold capped
    rcases le_total (1 : ℝ) (exponent β (Real.log e / Real.log N)) with ha | ha
    · simpa only [min_eq_left ha] using ht
    · simpa only [min_eq_right ha] using hexp
  apply hcap.trans
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega))
    (by have h := capped_le_affine β (Real.log e / Real.log N); linarith)

end PaperP1.WideQuadraticKernelCount
