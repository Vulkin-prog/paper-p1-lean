module

public import PaperP1.Diophantine.ShiftedQuadraticValues
public import PaperP1.Asymptotics.WideQuadraticKernelCount

/-! # The uniform affine kernel count for actual shifted two-factor blocks -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ShiftedQuadraticKernelCount

open Finset PaperP1.SplitOffsetProducts PaperP1.LinearKernelFibres
open PaperP1.ShiftedQuadraticValues PaperP1.QuadraticKernelExponents

theorem ordered_pair_count (D A₀ ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ W e : ℕ, ∀ a b : ℤ, ∀ β : ℝ,
      (W : ℝ) ≤ D * (Real.log N) ^ A₀ → 0 < e → a < b → a.natAbs ≤ W → b.natAbs ≤ W →
      ∀ S : Finset ℕ,
        (∀ n ∈ S, N ≤ n ∧ n ≤ 2 * N ∧ (N : ℝ) ^ β ≤ kernel {a, b} n ∧
          (kernel {a, b} n : ℝ) < 2 * (N : ℝ) ^ β ∧ e ∣ kernel {a, b} n) →
        (S.card : ℝ) ≤ (N : ℝ) ^ (affine β (Real.log e / Real.log N) + ε) := by
  obtain ⟨Nq, hNq⟩ := PaperP1.WideQuadraticKernelCount.uniform_affine_count (2 * D) A₀ ε hε
  obtain ⟨Nw, hNw⟩ := PaperP1.SplitQuadraticCongruenceCount.polylog_le_rpow (2 * D) A₀ 1 (by norm_num)
  refine ⟨max 2 (max Nq Nw), ?_⟩
  intro N hN W e a b β hwidth he hab ha hb S hS
  have hNtwo : 2 ≤ N := by omega
  have hWNr : (2 * W : ℝ) ≤ N := by
    have hw := hNw N (by omega)
    rw [Real.rpow_one] at hw
    nlinarith
  have hWN : 2 * W ≤ N := by exact_mod_cast hWNr
  have hspos := shift_pos a b hab
  have hshift : (shift a b : ℝ) ≤ (2 * D) * (Real.log N) ^ A₀ := by
    have htri := Int.natAbs_sub_le b a
    have hnat : shift a b ≤ 2 * W := by dsimp [shift]; omega
    have hr : (shift a b : ℝ) ≤ 2 * W := by exact_mod_cast hnat
    nlinarith
  have hpos : ∀ n ∈ S, 0 < (n : ℤ) + a := by
    intro n hn
    exact (offset_bounds N n W a hNtwo hWN (hS n hn).1 (hS n hn).2.1 ha).1
  have hinj := value_injective_on S a hpos
  rw [← card_image_of_injOn hinj]
  apply hNq N (by omega) (shift a b) e β hspos he hshift (S.image fun n ↦ value n a)
  intro x hx
  obtain ⟨n, hn, rfl⟩ := mem_image.mp hx
  obtain ⟨hnlo, hnhi, hqlo, hqhi, hdiv⟩ := hS n hn
  have hdata := shifted_bounds N n W a b hNtwo hWN hnlo hnhi ha hb hab
  have hk := quadratic_block_eq n a b hab.ne hdata.2.2.2
  refine ⟨hdata.1, hdata.2.1, ?_, ?_, ?_⟩
  · rwa [← hk]
  · rwa [← hk]
  · rwa [← hk]

theorem two_factor_count (D A₀ ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ W e : ℕ, ∀ B : Finset ℤ, ∀ β : ℝ,
      (W : ℝ) ≤ D * (Real.log N) ^ A₀ → 0 < e → B.card = 2 →
      (∀ a ∈ B, a.natAbs ≤ W) → ∀ S : Finset ℕ,
        (∀ n ∈ S, N ≤ n ∧ n ≤ 2 * N ∧ (N : ℝ) ^ β ≤ kernel B n ∧
          (kernel B n : ℝ) < 2 * (N : ℝ) ^ β ∧ e ∣ kernel B n) →
        (S.card : ℝ) ≤ (N : ℝ) ^ (affine β (Real.log e / Real.log N) + ε) := by
  obtain ⟨N₀, hN₀⟩ := ordered_pair_count D A₀ ε hε
  refine ⟨N₀, ?_⟩
  intro N hN W e B β hwidth he hB hA S hS
  obtain ⟨a, b, hab, rfl⟩ := ordered_pair_representation B hB
  exact hN₀ N hN W e a b β hwidth he hab (hA a (by simp)) (hA b (by simp)) S hS

end PaperP1.ShiftedQuadraticKernelCount
