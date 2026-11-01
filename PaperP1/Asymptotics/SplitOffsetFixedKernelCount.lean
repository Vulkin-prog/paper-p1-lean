module

public import PaperP1.Diophantine.LinearKernelFibres
public import PaperP1.Asymptotics.SplitOffsetHeightBudget

/-! # Actual fixed-kernel fibres of a split product, without an even-degree restriction -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SplitOffsetFixedKernelCount

open Finset PaperP1.SplitOffsetProducts PaperP1.DefectivePredicate
open PaperP1.LinearKernelFibres PaperP1.SplitOffsetSupports

@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

def code (a b : ℤ) (n : ℕ) : Finset ℕ × Finset ℕ :=
  (oddPrimeSupport (value n a), oddPrimeSupport (value n b))

def values (A : Finset ℤ) (N q : ℕ) : Finset ℕ :=
  (Icc N (2 * N)).filter fun n ↦ kernel A n = q

theorem mem_values (A : Finset ℤ) (N q n : ℕ) : n ∈ values A N q ↔
    N ≤ n ∧ n ≤ 2 * N ∧ kernel A n = q := by
  simp only [values, mem_filter, mem_Icc, and_assoc]

theorem code_card (a b : ℤ) (P S : Finset ℕ)
    (hS : ∀ n ∈ S, oddPrimeSupport (value n a) ⊆ P ∧ oddPrimeSupport (value n b) ⊆ P) :
    (S.image (code a b)).card ≤ 4 ^ P.card := by
  have hsub : S.image (code a b) ⊆ P.powerset ×ˢ P.powerset := by
    intro c hc
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hc
    exact mem_product.mpr ⟨mem_powerset.mpr (hS n hn).1, mem_powerset.mpr (hS n hn).2⟩
  calc
    _ ≤ (P.powerset ×ˢ P.powerset).card := card_le_card hsub
    _ = 2 ^ P.card * 2 ^ P.card := by rw [card_product, card_powerset]
    _ = _ := by rw [← mul_pow]; norm_num

theorem kernels_of_code (a b : ℤ) (n : ℕ) (U V : Finset ℕ) (heq : code a b n = (U, V)) :
    linearKernel n a = U.prod id ∧ linearKernel n b = V.prod id := by
  have hU := congrArg Prod.fst heq
  have hV := congrArg Prod.snd heq
  change oddPrimeSupport (value n a) = U at hU
  change oddPrimeSupport (value n b) = V at hV
  constructor
  · change (oddPrimeSupport (value n a)).prod id = U.prod id
    rw [hU]
  · change (oddPrimeSupport (value n b)).prod id = V.prod id
    rw [hV]

theorem finite_fibre_count (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ W q : ℕ, ∀ A : Finset ℤ,
      2 * W ≤ N → 2 ≤ A.card → (∀ a ∈ A, a.natAbs ≤ W) → ∀ S : Finset ℕ,
      (∀ n ∈ S, N ≤ n ∧ n ≤ 2 * N ∧ kernel A n = q) →
      (S.card : ℝ) ≤ (4 : ℝ) ^ (q * resultant A).primeFactors.card * (N : ℝ) ^ ε := by
  obtain ⟨Nf, hNf⟩ := fixed_linear_kernels_count ε hε
  refine ⟨max 2 Nf, ?_⟩
  intro N hN W q A hW hcard hA S hS
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp (show 1 < A.card by omega)
  let P := (q * resultant A).primeFactors
  have hsupp : ∀ n ∈ S, oddPrimeSupport (value n a) ⊆ P ∧ oddPrimeSupport (value n b) ⊆ P := by
    intro n hn
    have hWn : W < n := by have hlo := (hS n hn).1; omega
    have hvalues : ∀ d ∈ A, (n : ℤ) + d ≠ 0 :=
      fun d hd ↦ (factor_pos A n W hWn hA d hd).ne'
    have hsa := linear_support_subset A n a ha hvalues
    have hsb := linear_support_subset A n b hb hvalues
    rw [(hS n hn).2.2] at hsa hsb
    exact ⟨hsa, hsb⟩
  have hcodes : ((S.image (code a b)).card : ℝ) ≤ (4 : ℝ) ^ P.card := by
    exact_mod_cast code_card a b P S hsupp
  calc
    (S.card : ℝ) = ∑ c ∈ S.image (code a b), ((S.filter fun n ↦ code a b n = c).card : ℝ) := by
      have hi := congrArg (fun m : ℕ ↦ (m : ℝ)) (card_eq_sum_card_image (code a b) S)
      simpa only [Nat.cast_sum] using hi
    _ ≤ ∑ _c ∈ S.image (code a b), (N : ℝ) ^ ε := by
      apply sum_le_sum
      intro c _
      apply hNf N (by omega) W (c.1.prod id) (c.2.prod id) a b hW (hA a ha) (hA b hb) hab
      intro n hn
      obtain ⟨hnS, hnc⟩ := mem_filter.mp hn
      have hk := kernels_of_code a b n c.1 c.2 hnc
      exact ⟨(hS n hnS).1, (hS n hnS).2.1, hk⟩
    _ = ((S.image (code a b)).card : ℝ) * (N : ℝ) ^ ε := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hcodes (Real.rpow_nonneg (Nat.cast_nonneg N) _)

theorem growing_degree_fixed_kernel_count (c D A₀ ε : ℝ) (hc : 0 ≤ c) (hD : 1 ≤ D)
    (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ W q : ℕ, ∀ A : Finset ℤ,
      0 < W → 2 ≤ A.card → (W : ℝ) ≤ D * (Real.log N) ^ A₀ →
      (A.card : ℝ) ≤ c * Real.log (Real.log N) → (∀ a ∈ A, a.natAbs ≤ W) →
      ∀ S : Finset ℕ, (∀ n ∈ S, N ≤ n ∧ n ≤ 2 * N ∧ kernel A n = q) →
      (S.card : ℝ) ≤ (N : ℝ) ^ (2 * c * Real.log 2 + ε) := by
  obtain ⟨Nf, hNf⟩ := finite_fibre_count (ε / 2) (by positivity)
  obtain ⟨Np, hNp⟩ := PaperP1.SplitOffsetHeightBudget.actual_exponential_budget c D A₀
    (ε / 2) hc hD (by positivity) 4 (by norm_num)
  obtain ⟨Nw, hNw⟩ := PaperP1.SplitQuadraticCongruenceCount.polylog_le_rpow (2 * D) A₀ 1 (by norm_num)
  refine ⟨max 2 (max Nf (max Np Nw)), ?_⟩
  intro N hN W q A hW hcard hwidth hdegree hA S hS
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hWNr : (2 * W : ℝ) ≤ N := by
    have hb := hNw N (by omega)
    rw [Real.rpow_one] at hb
    nlinarith
  have hWN : 2 * W ≤ N := by exact_mod_cast hWNr
  by_cases hne : S.Nonempty
  · obtain ⟨n₀, hn₀⟩ := hne
    have hprime := hNp N (by omega) n₀ W A hW (hS n₀ hn₀).1 (hS n₀ hn₀).2.1 hwidth hdegree hA
    rw [(hS n₀ hn₀).2.2] at hprime
    have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
      norm_num
    calc
      _ ≤ (4 : ℝ) ^ (q * resultant A).primeFactors.card * (N : ℝ) ^ (ε / 2) :=
        hNf N (by omega) W q A hWN hcard hA S hS
      _ ≤ (N : ℝ) ^ (c * Real.log 4 + ε / 2) * (N : ℝ) ^ (ε / 2) :=
        mul_le_mul_of_nonneg_right hprime (Real.rpow_nonneg hn.le _)
      _ = _ := by
        rw [← Real.rpow_add hn, hlog4]
        congr 1
        ring
  · rw [not_nonempty_iff_eq_empty.mp hne, card_empty, Nat.cast_zero]
    exact Real.rpow_nonneg hn.le _

theorem actual_values_fixed_kernel_count (c D A₀ ε : ℝ) (hc : 0 ≤ c) (hD : 1 ≤ D)
    (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ W q : ℕ, ∀ A : Finset ℤ,
      0 < W → 2 ≤ A.card → (W : ℝ) ≤ D * (Real.log N) ^ A₀ →
      (A.card : ℝ) ≤ c * Real.log (Real.log N) → (∀ a ∈ A, a.natAbs ≤ W) →
      ((values A N q).card : ℝ) ≤ (N : ℝ) ^ (2 * c * Real.log 2 + ε) := by
  obtain ⟨N₀, hN₀⟩ := growing_degree_fixed_kernel_count c D A₀ ε hc hD hε
  refine ⟨N₀, ?_⟩
  intro N hN W q A hW hcard hwidth hdegree hA
  exact hN₀ N hN W q A hW hcard hwidth hdegree hA (values A N q)
    (by intro n hn; exact (mem_values A N q n).mp hn)

end PaperP1.SplitOffsetFixedKernelCount
