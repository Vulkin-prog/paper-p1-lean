module

public import PaperP1.Asymptotics.QuadraticSquarePartCount
public import PaperP1.Asymptotics.QuadraticKernelExponents
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! # Actual T5.1 counts, their minimum exponent, and a uniform affine consequence -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrescribedQuadraticKernelTheorem

open Finset PaperP1.QuadraticKernelFibres PaperP1.QuadraticKernelExponents

@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

def values (N h e : ℕ) (β : ℝ) : Finset ℕ :=
  (Icc N (2 * N)).filter fun n ↦ (N : ℝ) ^ β ≤ kernel h n ∧
    (kernel h n : ℝ) < 2 * (N : ℝ) ^ β ∧ e ∣ kernel h n

theorem mem_values (N h e n : ℕ) (β : ℝ) : n ∈ values N h e β ↔
    N ≤ n ∧ n ≤ 2 * N ∧ (N : ℝ) ^ β ≤ kernel h n ∧
      (kernel h n : ℝ) < 2 * (N : ℝ) ^ β ∧ e ∣ kernel h n := by
  simp only [values, mem_filter, mem_Icc]
  tauto

theorem size_identities (N e : ℕ) (hN : 2 ≤ N) (he : 0 < e) (β : ℝ) :
    (N : ℝ) ^ β / e = (N : ℝ) ^ (β - Real.log e / Real.log N) ∧
    Real.sqrt ((N : ℝ) ^ β) / e = (N : ℝ) ^ (β / 2 - Real.log e / Real.log N) ∧
    (N : ℝ) / Real.sqrt ((N : ℝ) ^ β) = (N : ℝ) ^ (1 - β / 2) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (N : ℝ) ≠ 1 := ne_of_gt (by exact_mod_cast (show 1 < N by omega))
  have her : (0 : ℝ) < e := by exact_mod_cast he
  have hδ : (N : ℝ) ^ (Real.log e / Real.log N) = (e : ℝ) :=
    Real.rpow_logb hNr hN1 her
  have hs : Real.sqrt ((N : ℝ) ^ β) = (N : ℝ) ^ (β / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hNr.le]
    congr 1
    ring
  rw [hs]
  exact ⟨by rw [Real.rpow_sub hNr, hδ],
    by rw [Real.rpow_sub hNr, hδ], by rw [Real.rpow_sub hNr, Real.rpow_one]⟩

theorem three_exponent_bounds (D A₀ ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ h e : ℕ, ∀ β : ℝ, 0 < h → 0 < e →
      (h : ℝ) ≤ D * (Real.log N) ^ A₀ → ∀ S : Finset ℕ,
        (∀ n ∈ S, N ≤ n ∧ n ≤ 2 * N ∧ (N : ℝ) ^ β ≤ kernel h n ∧
          (kernel h n : ℝ) < 2 * (N : ℝ) ^ β ∧ e ∣ kernel h n) →
        (S.card : ℝ) ≤ (N : ℝ) ^ (1 + ε) ∧
        (S.card : ℝ) ≤ (N : ℝ) ^ (β - Real.log e / Real.log N + ε) ∧
        (S.card : ℝ) ≤ (N : ℝ) ^
          (max (β / 2 - Real.log e / Real.log N) (1 - β / 2) + ε) := by
  obtain ⟨Nf, hNf⟩ := PaperP1.PrescribedQuadraticKernelCount.real_first_branch_count 2
    (ε / 2) (by positivity)
  obtain ⟨Ns, hNs⟩ := PaperP1.QuadraticSquarePartCount.second_branch_count D A₀ (ε / 2) (by positivity)
  obtain ⟨Nh, hNh⟩ := PaperP1.SplitQuadraticCongruenceCount.polylog_le_rpow D A₀ 1 (by norm_num)
  obtain ⟨Nc, hNc⟩ := PaperP1.UniformReal.uniformSubpolynomialOn_le_rpow
    (PaperP1.ExpSqrtLog.uniformSubpolynomialOn_const (fun _ _ : ℕ ↦ True) 2) (ε / 2) (by positivity)
  refine ⟨max 2 (max Nf (max Ns (max Nh Nc))), ?_⟩
  intro N hN h e β hh he hshift S hS
  have hNtwo : 2 ≤ N := by omega
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hp : 0 ≤ (N : ℝ) ^ (ε / 2) := Real.rpow_nonneg hn.le _
  have hpmono : (N : ℝ) ^ (ε / 2) ≤ (N : ℝ) ^ ε :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hc : (2 : ℝ) ≤ (N : ℝ) ^ (ε / 2) := (le_abs_self _).trans (hNc N (by omega) 0 trivial)
  have hhN : h ≤ N := by
    have hr := hshift.trans (hNh N (by omega))
    simpa only [Real.rpow_one, Nat.cast_le] using hr
  have htwo : 2 * N ≤ N ^ 2 := by nlinarith
  obtain ⟨hi1, hi2, hi3⟩ := size_identities N e hNtwo he β
  have hf := hNf N (by omega) (2 * N) h e ((N : ℝ) ^ β)
    (Real.rpow_nonneg hn.le _) hh he htwo (hhN.trans (by nlinarith : N ≤ N ^ 2)) S (by
      intro n hmem
      obtain ⟨hlo, hhi, _, hqhi, hdiv⟩ := hS n hmem
      exact ⟨by omega, hhi, hqhi, hdiv⟩)
  rw [hi1] at hf
  have hs := hNs N (by omega) h e ((N : ℝ) ^ β) (Real.rpow_pos_of_pos hn _) hh he hshift S hS
  rw [hi2, hi3] at hs
  have htriv : (S.card : ℝ) ≤ 2 * N := by
    apply PaperP1.QuadraticKernelRanges.positive_card (2 * N) (by positivity)
    intro n hmem
    exact ⟨by have hlo := (hS n hmem).1; omega, by exact_mod_cast (hS n hmem).2.1⟩
  refine ⟨?_, ?_, ?_⟩
  · calc
      _ ≤ 2 * (N : ℝ) := htriv
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
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hp) (Real.rpow_nonneg hn.le _)
      _ = (N : ℝ) ^ (m + ε) := by
        rw [← Real.rpow_add hn, ← Real.rpow_add hn]
        congr 1
        dsimp [m]
        ring

theorem actual_exponent_counts (D A₀ ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ h e : ℕ, ∀ β : ℝ, 0 < h → 0 < e →
      (h : ℝ) ≤ D * (Real.log N) ^ A₀ →
      ((values N h e β).card : ℝ) ≤ (N : ℝ) ^ (exponent β (Real.log e / Real.log N) + ε) ∧
      ((values N h e β).card : ℝ) ≤ (N : ℝ) ^ (capped β (Real.log e / Real.log N) + ε) ∧
      ((values N h e β).card : ℝ) ≤ (N : ℝ) ^ (affine β (Real.log e / Real.log N) + ε) := by
  obtain ⟨N₀, hN₀⟩ := three_exponent_bounds D A₀ ε hε
  refine ⟨max 2 N₀, ?_⟩
  intro N hN h e β hh he hshift
  obtain ⟨ht, hf, hs⟩ := hN₀ N (by omega) h e β hh he hshift (values N h e β)
    (by intro n hn; exact (mem_values N h e n β).mp hn)
  have hexp : ((values N h e β).card : ℝ) ≤
      (N : ℝ) ^ (exponent β (Real.log e / Real.log N) + ε) := by
    unfold exponent
    rcases le_total (β - Real.log e / Real.log N)
      (max (β / 2 - Real.log e / Real.log N) (1 - β / 2)) with ha | ha
    · simpa only [min_eq_left ha] using hf
    · simpa only [min_eq_right ha] using hs
  have hcap : ((values N h e β).card : ℝ) ≤
      (N : ℝ) ^ (capped β (Real.log e / Real.log N) + ε) := by
    unfold capped
    rcases le_total (1 : ℝ) (exponent β (Real.log e / Real.log N)) with ha | ha
    · simpa only [min_eq_left ha] using ht
    · simpa only [min_eq_right ha] using hexp
  refine ⟨hexp, hcap, hcap.trans ?_⟩
  exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega))
    (by have h := capped_le_affine β (Real.log e / Real.log N); linarith)

theorem admissible_height (N h e : ℕ) (β : ℝ) (hN : 0 < N) (hh : h ≤ N)
    (hne : (values N h e β).Nonempty) : (N : ℝ) ^ β ≤ 6 * (N : ℝ) ^ 2 := by
  obtain ⟨n, hn⟩ := hne
  obtain ⟨hlo, hhi, hqlo, _, _⟩ := (mem_values N h e n β).mp hn
  have hnpos : 0 < n := by omega
  have hp := (PaperP1.QuadraticKernelRanges.product_bounds N h n hN hlo hhi hh).2
  have hk := (kernel_le_product h n hnpos).trans hp
  exact hqlo.trans (by exact_mod_cast hk)

theorem eventual_source_comparison (D A₀ ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ h e : ℕ, ∀ β : ℝ, 0 < e →
      (h : ℝ) ≤ D * (Real.log N) ^ A₀ → (values N h e β).Nonempty →
      exponent β (Real.log e / Real.log N) ≤ affine β (Real.log e / Real.log N) + ε := by
  obtain ⟨Nh, hNh⟩ := PaperP1.SplitQuadraticCongruenceCount.polylog_le_rpow D A₀ 1 (by norm_num)
  obtain ⟨Nc, hNc⟩ := PaperP1.UniformReal.uniformSubpolynomialOn_le_rpow
    (PaperP1.ExpSqrtLog.uniformSubpolynomialOn_const (fun _ _ : ℕ ↦ True) 6) (4 * ε) (by positivity)
  refine ⟨max 2 (max Nh Nc), ?_⟩
  intro N hN h e β he hshift hne
  have hn : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hhN : h ≤ N := by
    have hr := hshift.trans (hNh N (by omega))
    simpa only [Real.rpow_one, Nat.cast_le] using hr
  have hc : (6 : ℝ) ≤ (N : ℝ) ^ (4 * ε) := (le_abs_self _).trans (hNc N (by omega) 0 trivial)
  have hbpow : (N : ℝ) ^ β ≤ (N : ℝ) ^ (2 + 4 * ε) := by
    calc
      _ ≤ 6 * (N : ℝ) ^ 2 := admissible_height N h e β (by omega) hhN hne
      _ ≤ (N : ℝ) ^ (4 * ε) * (N : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hc (sq_nonneg _)
      _ = _ := by rw [Real.rpow_add (zero_lt_one.trans hn), Real.rpow_two]; ring
  have hb : β ≤ 2 + 4 * ε := (Real.rpow_le_rpow_left_iff hn).mp hbpow
  have he1 : (1 : ℝ) ≤ e := by exact_mod_cast he
  have hδ : 0 ≤ Real.log e / Real.log N :=
    div_nonneg (Real.log_nonneg he1) (Real.log_pos hn).le
  have hcomp := exponent_le_affine_with_margin β (Real.log e / Real.log N) (4 * ε)
    (by positivity) (by linarith)
  linarith

theorem companion_T5_1_counts (D A₀ ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ h e : ℕ, ∀ β : ℝ, 0 < h → 0 < e →
      (h : ℝ) ≤ D * (Real.log N) ^ A₀ →
      ((values N h e β).card : ℝ) ≤ (N : ℝ) ^ (exponent β (Real.log e / Real.log N) + ε) ∧
      ((values N h e β).card : ℝ) ≤ (N : ℝ) ^ (capped β (Real.log e / Real.log N) + ε) ∧
      ((values N h e β).card : ℝ) ≤ (N : ℝ) ^ (affine β (Real.log e / Real.log N) + ε) ∧
      ((values N h e β).Nonempty →
        exponent β (Real.log e / Real.log N) ≤ affine β (Real.log e / Real.log N) + ε) := by
  obtain ⟨N₁, hN₁⟩ := actual_exponent_counts D A₀ ε hε
  obtain ⟨N₂, hN₂⟩ := eventual_source_comparison D A₀ ε hε
  refine ⟨max N₁ N₂, ?_⟩
  intro N hN h e β hh he hshift
  obtain ⟨hf, hc, ha⟩ := hN₁ N (by omega) h e β hh he hshift
  exact ⟨hf, hc, ha, hN₂ N (by omega) h e β he hshift⟩

end PaperP1.PrescribedQuadraticKernelTheorem
