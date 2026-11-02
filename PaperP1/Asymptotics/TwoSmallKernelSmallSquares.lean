module

public import PaperP1.Arithmetic.TwoSmallKernelSquareParts
public import PaperP1.Arithmetic.PositiveProductPairs
public import PaperP1.Arithmetic.LogarithmicPrimeCount
public import PaperP1.Combinatorics.FiniteCoverCount

/-! # Uniformly summing the small square-product sector for two individually small kernels -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TwoSmallKernelSmallSquares

open Finset PaperP1.TwoSmallKernelSquareParts PaperP1.SmallPrimeBudget
  PaperP1.LargeOddKernel PaperP1.DefectCounting PaperP1.DefectivePredicate

local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem uniform_count (D ε : ℝ) (hD : 0 ≤ D) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ H h : ℕ, ∀ T P : ℝ,
      (H : ℝ) ≤ D * Real.log N → 0 < h → 0 ≤ T → 0 ≤ P →
      ∀ S : Finset ℕ, (∀ n ∈ S, 0 < n ∧ N ≤ 2 * n ∧ n ≤ 3 * N ∧ n + h ≤ 4 * N ∧
        (largeOddKernel H n : ℝ) ≤ T ∧ (largeOddKernel H (n + h) : ℝ) ≤ T ∧
        ((canonicalSquarePart n * canonicalSquarePart (n + h) : ℕ) : ℝ) ≤ P) →
      (S.card : ℝ) ≤ (24 * h * T + P) * (N : ℝ) ^ ε := by
  let η := ε / 3
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨NS, hs⟩ := LogarithmicPrimeCount.smooth_support_count_le_rpow_eventually D hD η hη
  obtain ⟨NP, hp⟩ := PositiveProductPairs.uniform_count 4 η hη
  refine ⟨max 4 (max NS NP), by omega, ?_⟩
  intro N hN H h T P hH hh hT hP S hS
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn₁ : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hrpow : 1 ≤ (N : ℝ) ^ η := Real.one_le_rpow hn₁ hη.le
  let A := (smallPrimesUpTo H).powerset
  let I := A ×ˢ A
  let F := fun w : Finset ℕ × Finset ℕ ↦ S.filter fun n ↦
    smallOddSupport H n = w.1 ∧ smallOddSupport H (n + h) = w.2
  have hcover : ∀ n ∈ S, ∃ w ∈ I, n ∈ F w := by
    intro n hnS
    exact ⟨(smallOddSupport H n, smallOddSupport H (n + h)),
      mem_product.mpr ⟨mem_powerset.mpr (smallOddSupport_subset H n),
        mem_powerset.mpr (smallOddSupport_subset H (n + h))⟩, mem_filter.mpr ⟨hnS, rfl, rfl⟩⟩
  have hF : ∀ w ∈ I, ((F w).card : ℝ) ≤ 24 * h * T + P * (N : ℝ) ^ η := by
    intro w _hw
    by_cases hne : (F w).Nonempty
    · obtain ⟨n₀, hn₀⟩ := hne
      have hparts₀ := (mem_filter.mp hn₀).2
      have hc₁ : 0 < w.1.prod id := by
        rw [← hparts₀.1]
        exact smallOddPart_pos H n₀
      have hc₂ : 0 < w.2.prod id := by
        rw [← hparts₀.2]
        exact smallOddPart_pos H (n₀ + h)
      have hTpos : 0 < T := (by exact_mod_cast largeOddKernel_pos H n₀ : (0 : ℝ) < largeOddKernel H n₀).trans_le
        (hS n₀ (mem_filter.mp hn₀).1).2.2.2.2.1
      have hfixed := fixed_smooth_parts H h (w.1.prod id) (w.2.prod id) hh hc₁ hc₂
        (N : ℝ) T hn hTpos (F w) (by
          intro n hnF
          obtain ⟨hnS, hs₁, hs₂⟩ := mem_filter.mp hnF
          obtain ⟨hnpos, hnlo, hnhi, _hmhi, hk₁, hk₂, _hprod⟩ := hS n hnS
          have hnlor : (N : ℝ) ≤ 2 * n := by exact_mod_cast hnlo
          have hnhir : (n : ℝ) ≤ 3 * N := by exact_mod_cast hnhi
          exact ⟨hnpos, by linarith only [hnlor], hnhir, congrArg (fun s : Finset ℕ ↦ s.prod id) hs₁,
            congrArg (fun s : Finset ℕ ↦ s.prod id) hs₂, hk₁, hk₂⟩)
      have hcodes : (((F w).image (code h)).card : ℝ) ≤ P * (N : ℝ) ^ η := by
        apply hp N (by omega) P hP
        intro z hz
        obtain ⟨n, hnF, rfl⟩ := mem_image.mp hz
        obtain ⟨hnpos, _hnlo, hnhi, hmhi, _hk₁, _hk₂, hprod⟩ := hS n (mem_filter.mp hnF).1
        have hmpos : 0 < n + h := by omega
        have hheight : canonicalSquarePart n * canonicalSquarePart (n + h) ≤ N ^ 4 := by
          calc
            _ ≤ n * (n + h) := Nat.mul_le_mul (square_part_le n hnpos) (square_part_le (n + h) hmpos)
            _ ≤ (3 * N) * (4 * N) := Nat.mul_le_mul hnhi hmhi
            _ = 12 * N ^ 2 := by ring
            _ ≤ N ^ 2 * N ^ 2 := Nat.mul_le_mul_right _ (by nlinarith only [show 4 ≤ N by omega])
            _ = N ^ 4 := by ring
        exact ⟨Nat.pos_of_ne_zero (SquarefreeKernelProducts.canonical_part_ne_zero n hnpos.ne'),
          Nat.pos_of_ne_zero (SquarefreeKernelProducts.canonical_part_ne_zero (n + h) hmpos.ne'), hheight, hprod⟩
      exact hfixed.trans (add_le_add (le_refl _) hcodes)
    · rw [not_nonempty_iff_eq_empty.mp hne, card_empty, Nat.cast_zero]
      positivity
  have hA : (A.card : ℝ) ≤ (N : ℝ) ^ η := hs N (by omega) H hH
  have hI : (I.card : ℝ) ≤ (N : ℝ) ^ (2 * η) := by
    calc
      _ = (A.card : ℝ) * A.card := by simp only [I, card_product, Nat.cast_mul]
      _ ≤ (N : ℝ) ^ η * (N : ℝ) ^ η := mul_le_mul hA hA (Nat.cast_nonneg _) (Real.rpow_nonneg hn.le _)
      _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring
  calc
    _ ≤ (I.card : ℝ) * (24 * h * T + P * (N : ℝ) ^ η) :=
      FiniteCoverCount.cardinal_le S I F _ hcover hF
    _ ≤ (N : ℝ) ^ (2 * η) * ((24 * h * T + P) * (N : ℝ) ^ η) := by
      apply mul_le_mul hI
      · have hhT : 0 ≤ 24 * (h : ℝ) * T := by positivity
        nlinarith only [mul_le_mul_of_nonneg_left hrpow hhT]
      · positivity
      · positivity
    _ = (24 * h * T + P) * (N : ℝ) ^ ε := by
      calc
        _ = (24 * h * T + P) * ((N : ℝ) ^ (2 * η) * (N : ℝ) ^ η) := by ring
        _ = _ := by rw [← Real.rpow_add hn]; congr 2; dsimp [η]; ring

end PaperP1.TwoSmallKernelSmallSquares
