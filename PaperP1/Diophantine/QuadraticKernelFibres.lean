module

public import PaperP1.Arithmetic.SmallPrimeBudget
public import PaperP1.Diophantine.UniformQuadraticCount

/-! # Actual squarefree kernels of n(n+h) and their uniform quadratic fibres -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.QuadraticKernelFibres

open Finset PaperP1.SmallPrimeBudget PaperP1.DefectivePredicate PaperP1.LargeOddKernel

def kernel (h n : ℕ) : ℕ := squarefreeKernel (n * (n + h))
def part (h n : ℕ) : ℕ := canonicalSquarePart (n * (n + h))
def embed (h n : ℕ) : ℤ × ℤ := ((2 * n + h : ℕ), (part h n : ℕ))

theorem kernel_pos (h n : ℕ) : 0 < kernel h n := by
  unfold kernel squarefreeKernel
  apply prod_pos
  intro p hp
  exact (prime_of_mem_oddPrimeSupport hp).pos

theorem representation (h n : ℕ) (hn : 0 < n) : kernel h n * part h n ^ 2 = n * (n + h) :=
  squarefreeKernel_mul_squarePart (Nat.mul_pos hn (by omega)).ne'

theorem part_pos (h n : ℕ) (hn : 0 < n) : 0 < part h n := by
  have hr := representation h n hn
  have hnprod : 0 < n * (n + h) := Nat.mul_pos hn (by omega)
  by_contra hnot
  have hz : part h n = 0 := by omega
  rw [hz, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] at hr
  omega

theorem kernel_le_product (h n : ℕ) (hn : 0 < n) : kernel h n ≤ n * (n + h) :=
  Nat.le_of_dvd (Nat.mul_pos hn (by omega)) ⟨part h n ^ 2, (representation h n hn).symm⟩

theorem part_le_product (h n : ℕ) (hn : 0 < n) : part h n ≤ n * (n + h) := by
  have hv := part_pos h n hn
  have hq := kernel_pos h n
  have hpow : part h n ≤ part h n ^ 2 := by nlinarith
  calc
    _ ≤ part h n ^ 2 := hpow
    _ ≤ kernel h n * part h n ^ 2 := by nlinarith only [hq]
    _ = _ := representation h n hn

theorem embed_injective (h : ℕ) : Function.Injective (embed h) := by
  intro n m heq
  have hfirst := congrArg Prod.fst heq
  change ((2 * n + h : ℕ) : ℤ) = ((2 * m + h : ℕ) : ℤ) at hfirst
  have hn : 2 * n + h = 2 * m + h := by exact_mod_cast hfirst
  omega

theorem embed_equation (h n : ℕ) (hn : 0 < n) :
    PaperP1.PellInput.pellEquation 1 (4 * kernel h n) ((h : ℤ) ^ 2) (embed h n) := by
  have hr : (kernel h n : ℤ) * (part h n : ℤ) ^ 2 = (n : ℤ) * ((n + h : ℕ) : ℤ) := by
    exact_mod_cast representation h n hn
  unfold PaperP1.PellInput.pellEquation embed
  push_cast at hr ⊢
  linear_combination -4 * hr

theorem product_polynomial_height (N K h n : ℕ) (hn : n ≤ N ^ K) (hh : h ≤ N ^ K) :
    n * (n + h) ≤ 2 * N ^ (2 * K) := by
  calc
    _ ≤ N ^ K * (2 * N ^ K) := Nat.mul_le_mul hn (by omega)
    _ = _ := by rw [show 2 * K = K + K by omega, pow_add]; ring

theorem height_budget (N K : ℕ) (hN : 2 ≤ N) : 8 * N ^ (2 * K) ≤ N ^ (2 * K + 4) := by
  have hfour : 8 ≤ N ^ 4 := (by norm_num : 8 ≤ 2 ^ 4).trans (Nat.pow_le_pow_left hN 4)
  calc
    _ ≤ N ^ 4 * N ^ (2 * K) := Nat.mul_le_mul_right _ hfour
    _ = _ := by rw [← pow_add, Nat.add_comm]

theorem fixed_kernel_count (K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ X h q : ℕ, 0 < h → X ≤ N ^ K → h ≤ N ^ K →
      ∀ S : Finset ℕ, (∀ n ∈ S, 0 < n ∧ n ≤ X ∧ kernel h n = q) →
        (S.card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨Nq, hNq⟩ := PaperP1.UniformQuadraticCount.positive_count_le_rpow_eventually (2 * K + 4) ε hε
  refine ⟨max 2 Nq, ?_⟩
  intro N hN X h q hh hX hhN S hS
  have hNtwo : 2 ≤ N := by omega
  have hheight := height_budget N K hNtwo
  have hpow : N ^ K ≤ N ^ (2 * K) := Nat.pow_le_pow_right (by omega) (by omega)
  by_cases hne : S.Nonempty
  · obtain ⟨n₀, hn₀⟩ := hne
    obtain ⟨hn₀pos, hn₀X, hqeq⟩ := hS n₀ hn₀
    have hq : 0 < q := by rw [← hqeq]; exact kernel_pos h n₀
    have hqbound : q ≤ 2 * N ^ (2 * K) := by
      rw [← hqeq]
      exact (kernel_le_product h n₀ hn₀pos).trans (product_polynomial_height N K h n₀ (hn₀X.trans hX) hhN)
    have hCbound : 4 * q ≤ N ^ (2 * K + 4) := (by omega : 4 * q ≤ 8 * N ^ (2 * K)).trans hheight
    have hA : 1 ≤ N ^ (2 * K + 4) := Nat.one_le_pow _ _ (by omega)
    have hhbound : ((h : ℤ) ^ 2).natAbs ≤ N ^ (2 * K + 4) := by
      rw [Int.natAbs_pow, Int.natAbs_natCast]
      have hp : h ^ 2 ≤ N ^ (2 * K) := by
        calc
          _ ≤ (N ^ K) ^ 2 := Nat.pow_le_pow_left hhN 2
          _ = _ := by rw [← pow_mul, Nat.mul_comm]
      omega
    rw [← card_image_of_injective S (embed_injective h)]
    apply hNq N (by omega) 1 (4 * q) (N ^ (2 * K + 4)) ((h : ℤ) ^ 2)
      (by norm_num) (by positivity) (pow_ne_zero _ (by exact_mod_cast hh.ne' : (h : ℤ) ≠ 0))
      hA hCbound le_rfl hhbound
    intro z hz
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hz
    obtain ⟨hnpos, hnX, hnq⟩ := hS n hn
    have hnN := hnX.trans hX
    have hprod := product_polynomial_height N K h n hnN hhN
    have hfirst : 2 * n + h ≤ N ^ (2 * K + 4) := by omega
    have hpart : part h n ≤ N ^ (2 * K + 4) := by have hp := part_le_product h n hnpos; omega
    refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
    · have heq := embed_equation h n hnpos
      rwa [hnq] at heq
    · simpa only [embed, Int.natAbs_natCast] using hfirst
    · simpa only [embed, Int.natAbs_natCast] using hpart
    · change (0 : ℤ) < (2 * n + h : ℕ)
      exact_mod_cast (show 0 < 2 * n + h by omega)
    · change (0 : ℤ) < (part h n : ℕ)
      exact_mod_cast part_pos h n hnpos
  · rw [not_nonempty_iff_eq_empty.mp hne, card_empty, Nat.cast_zero]
    exact Real.rpow_nonneg (Nat.cast_nonneg N) _

end PaperP1.QuadraticKernelFibres
