module

public import PaperP1.Arithmetic.TranslatedKernelWindows
public import PaperP1.Asymptotics.SelectedKernelCounts
public import PaperP1.Asymptotics.TwoSmallKernelElementaryUpper
public import PaperP1.Combinatorics.FiniteCoverCount

/-! # Uniform one- and two-small-kernel counts on translated intervals -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TranslatedKernelCounts

open Finset PaperP1.TranslatedKernelWindows PaperP1.LargeOddKernel PaperP1.SelectedKernelCounts

theorem one_factor_bound {N H U : ℕ} (T : ℝ) (hH : H ≤ N) (hU : 2 ≤ U) (hUN : U ≤ N) (hT : 0 ≤ T) :
    ((oneStarts N H U T).card : ℝ) ≤ smallFactor H * (N : ℝ) ^ (1 / 2 : ℝ) * T ^ (1 / 2 : ℝ) := by
  have hfinite := one_finite_exp_bound T hH hU hUN hT
  have heq : 2 * H * Real.sqrt (3 * N) * Real.sqrt T * Real.exp (2 * Real.sqrt H) =
      (2 * Real.sqrt 3 * H * Real.exp (2 * Real.sqrt H)) *
        (N : ℝ) ^ (1 / 2 : ℝ) * T ^ (1 / 2 : ℝ) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
    simp only [Real.sqrt_eq_rpow]
    ring
  rw [heq] at hfinite
  refine hfinite.trans ?_
  unfold smallFactor
  gcongr
  exact le_add_of_nonneg_right (by norm_num)

theorem one_uniform (D ε : ℝ) (hD : 0 ≤ D) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ H U : ℕ, H ≤ N → 2 ≤ U → U ≤ N →
      (H : ℝ) ≤ D * Real.log N → ∀ T : ℝ, 0 ≤ T →
      ((oneStarts N H U T).card : ℝ) ≤ (N : ℝ) ^ (1 / 2 + ε) * T ^ (1 / 2 : ℝ) := by
  obtain ⟨N₀, hN₀⟩ := UniformReal.uniformSubpolynomialOn_le_rpow (small_factor_subpolynomial D hD) ε hε
  refine ⟨max 2 N₀, ?_⟩
  intro N hN H U hH hU hUN hlog T hT
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hf : smallFactor H ≤ (N : ℝ) ^ ε := (le_abs_self _).trans (hN₀ N (by omega) H hlog)
  refine (one_factor_bound T hH hU hUN hT).trans ?_
  calc
    _ ≤ ((N : ℝ) ^ ε * (N : ℝ) ^ (1 / 2 : ℝ)) * T ^ (1 / 2 : ℝ) := by gcongr
    _ = _ := by rw [← Real.rpow_add hn]; congr 2; ring

theorem two_uniform_budget (D ε : ℝ) (hD : 0 ≤ D) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ H U : ℕ, H ≤ N → 2 ≤ U → U ≤ N → N + 2 ≤ 2 * U →
      (H : ℝ) ≤ D * Real.log N → ∀ T : ℝ, 0 ≤ T →
      ((twoStarts N H U T).card : ℝ) ≤ (T + (N : ℝ) ^ (2 / 3 : ℝ)) * (N : ℝ) ^ ε := by
  obtain ⟨Na, _hNa, ha⟩ := TwoSmallKernelElementaryUpper.uniform_count D D 1 (ε / 2) hD (by positivity)
  obtain ⟨Np, hp⟩ := SplitQuadraticCongruenceCount.polylog_le_rpow D 1 (ε / 4) (by positivity)
  refine ⟨max 4 (max Na Np), by omega, ?_⟩
  intro N hN H U hH hU hUN hUhalf hlog T hT
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
    obtain ⟨hnpos, hnlo, hnhi, hmhi⟩ := translated_heights hU hUN hUhalf hH (mem_filter.mp hxS).1 hi hh
    exact ⟨hnpos, hnlo, hnhi, hmhi, hk₁, hk₂⟩
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

end PaperP1.TranslatedKernelCounts
