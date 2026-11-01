module

public import PaperP1.Arithmetic.KernelExposureExponent
public import PaperP1.Asymptotics.ComparableSplitProductCount

/-! # The actual split-product exposure exponent on comparable intervals -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SplitTupleExposure

open Finset PaperP1.SplitOffsetProducts PaperP1.KernelExposureExponent
open PaperP1.PrescribedPatternDivisors

theorem product_height (C N n W : ℕ) (A : Finset ℤ)
    (hn : n ≤ C * N) (hW : W ≤ N) (hA : ∀ a ∈ A, a.natAbs ≤ W) :
    product A n ≤ ((C + 1) * N) ^ A.card := by
  have hlocal : ∀ a ∈ A, ((n : ℤ) + a).natAbs ≤ (C + 1) * N := by
    intro a ha
    have htri := Int.natAbs_add_le (n : ℤ) a
    rw [Int.natAbs_natCast] at htri
    have haW := hA a ha
    nlinarith only [htri, haW, hn, hW]
  calc
    _ ≤ ∏ _a ∈ A, (C + 1) * N := prod_le_prod hlocal
    _ = _ := by simp

theorem source_height (C : ℕ) (D A₀ : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ W n : ℕ, ∀ A : Finset ℤ,
      N ≤ C * n → n ≤ C * N → (W : ℝ) ≤ D * (Real.log N) ^ A₀ →
      (∀ a ∈ A, a.natAbs ≤ W) → 0 < product A n ∧ kernel A n ≤ ((C + 1) * N) ^ A.card := by
  obtain ⟨Nv, hNv⟩ := PaperP1.ComparableSplitProductCount.width_lt_centre C D A₀
  obtain ⟨Nw, hNw⟩ := PaperP1.SplitQuadraticCongruenceCount.polylog_le_rpow D A₀ 1 (by norm_num)
  refine ⟨max Nv Nw, ?_⟩
  intro N hN W n A hnlo hnhi hwidth hA
  have hWN : W ≤ N := by
    have hw := hNw N (by omega)
    rw [Real.rpow_one] at hw
    exact_mod_cast hwidth.trans hw
  have hpos := product_pos A n W (hNv N (by omega) n W hnlo hwidth) hA
  exact ⟨hpos, (kernel_le A n hpos).trans (product_height C N n W A hnhi hWN hA)⟩

theorem source_exposure {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (C : ℕ) (D A₀ : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ W : ℕ, ∀ A : Finset ℤ, ∀ n : ι → ℕ,
      1 ≤ A.card → (W : ℝ) ≤ D * (Real.log N) ^ A₀ → (∀ a ∈ A, a.natAbs ≤ W) →
      (∀ i, N ≤ C * n i ∧ n i ≤ C * N) → IsSquare (∏ i, product A (n i)) →
      ∃ (last : ι) (rank : ι → ℕ), Function.Injective rank ∧ (∀ i, rank i ≤ rank last) ∧
        (∀ i, prescribed (fun j ↦ kernel A (n j)) rank i ∣ kernel A (n i)) ∧
        prescribed (fun j ↦ kernel A (n j)) rank last = kernel A (n last) ∧
        (∑ i ∈ univ.erase last, cost (fun j ↦ kernel A (n j)) N A.card rank i) ≤
          Fintype.card ι / 2 + Real.log (C + 1 : ℕ) / (2 * Real.log N) := by
  obtain ⟨Nv, hNv⟩ := PaperP1.ComparableSplitProductCount.width_lt_centre C D A₀
  obtain ⟨Nw, hNw⟩ := PaperP1.SplitQuadraticCongruenceCount.polylog_le_rpow D A₀ 1 (by norm_num)
  refine ⟨max 2 (max Nv Nw), ?_⟩
  intro N hN W A n hcard hwidth hA hn hsq
  have hWN : W ≤ N := by
    have hw := hNw N (by omega)
    rw [Real.rpow_one] at hw
    exact_mod_cast hwidth.trans hw
  have hpos : ∀ i, 0 < product A (n i) := by
    intro i
    exact product_pos A (n i) W (hNv N (by omega) (n i) W (hn i).1 hwidth) hA
  have hqsq : IsSquare (∏ i, kernel A (n i)) :=
    (PaperP1.KernelTuplePatterns.split_kernel_product_square_iff univ A n
      (fun i _ ↦ hpos i)).mpr hsq
  have hq : ∀ i, Squarefree (kernel A (n i)) := fun i ↦ kernel_squarefree A (n i)
  have hheight : ∀ i, (kernel A (n i) : ℝ) ≤
      (((C + 1 : ℕ) : ℝ) * N) ^ (A.card : ℝ) := by
    intro i
    rw [Real.rpow_natCast]
    exact_mod_cast (kernel_le A (n i) (hpos i)).trans (product_height C N (n i) W A (hn i).2 hWN hA)
  obtain ⟨last, rank, hrank, hlast, hcost⟩ := exists_cost_bound
    (fun i ↦ kernel A (n i)) hq hqsq N (by omega) (C + 1 : ℕ) A.card
    (by positivity) (by exact_mod_cast (show 0 < A.card by omega)) hheight
  exact ⟨last, rank, hrank, hlast,
    fun i ↦ prescribed_dvd_coordinate _ hq hqsq rank i,
    last_kernel_fixed _ hq hqsq rank hrank last hlast, hcost⟩

end PaperP1.SplitTupleExposure
