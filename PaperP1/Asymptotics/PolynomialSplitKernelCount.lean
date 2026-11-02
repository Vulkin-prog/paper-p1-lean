module

public import PaperP1.Arithmetic.PositiveSplitProducts
public import PaperP1.Arithmetic.PolynomialPrimeFactorPowers
public import PaperP1.Diophantine.PolynomialLinearKernelFibres
public import PaperP1.Asymptotics.SplitOffsetFixedKernelCount

/-! # Moving split roots: a fixed polynomial bound on positive values suffices -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PolynomialSplitKernelCount

open Finset PaperP1.SplitOffsetProducts PaperP1.SplitOffsetSupports
  PaperP1.LinearKernelFibres PaperP1.SplitOffsetFixedKernelCount

local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem finite_code_bound (K : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ q : ℕ, ∀ A : Finset ℤ, 2 ≤ A.card →
      ∀ S : Finset ℕ,
      (∀ n ∈ S, kernel A n = q ∧ ∀ a ∈ A, 0 < (n : ℤ) + a ∧ value n a ≤ N ^ K) →
      (S.card : ℝ) ≤ (4 : ℝ) ^ (q * resultant A).primeFactors.card * (N : ℝ) ^ ε := by
  obtain ⟨NF, hf⟩ := PolynomialLinearKernelFibres.uniform_count K ε hε
  refine ⟨max 2 NF, by omega, ?_⟩
  intro N hN q A hcard S hS
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp (show 1 < A.card by omega)
  let P := (q * resultant A).primeFactors
  have hsupp : ∀ n ∈ S, DefectivePredicate.oddPrimeSupport (value n a) ⊆ P ∧
      DefectivePredicate.oddPrimeSupport (value n b) ⊆ P := by
    intro n hn
    have hvalues : ∀ c ∈ A, (n : ℤ) + c ≠ 0 := fun c hc ↦ ((hS n hn).2 c hc).1.ne'
    have hsa := linear_support_subset A n a ha hvalues
    have hsb := linear_support_subset A n b hb hvalues
    rw [(hS n hn).1] at hsa hsb
    exact ⟨hsa, hsb⟩
  have hcodes : ((S.image (code a b)).card : ℝ) ≤ (4 : ℝ) ^ P.card := by
    exact_mod_cast code_card a b P S hsupp
  have hfibre (c : Finset ℕ × Finset ℕ) :
      ((S.filter fun n ↦ code a b n = c).card : ℝ) ≤ (N : ℝ) ^ ε := by
    apply hf N (by omega) (c.1.prod id) (c.2.prod id) a b hab (S.filter fun n ↦ code a b n = c)
    intro n hn
    obtain ⟨hnS, heq⟩ := mem_filter.mp hn
    obtain ⟨hu, hv⟩ := kernels_of_code a b n c.1 c.2 heq
    exact ⟨((hS n hnS).2 a ha).1, ((hS n hnS).2 a ha).2,
      ((hS n hnS).2 b hb).1, ((hS n hnS).2 b hb).2, hu, hv⟩
  calc
    _ = ∑ c ∈ S.image (code a b), ((S.filter fun n ↦ code a b n = c).card : ℝ) := by
      exact_mod_cast card_eq_sum_card_image (code a b) S
    _ ≤ ∑ _c ∈ S.image (code a b), (N : ℝ) ^ ε := sum_le_sum (fun c _ ↦ hfibre c)
    _ = (S.image (code a b)).card * (N : ℝ) ^ ε := by rw [sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right hcodes (Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem uniform_count (K d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ q : ℕ, ∀ A : Finset ℤ, 2 ≤ A.card → A.card ≤ d →
      ∀ S : Finset ℕ,
      (∀ n ∈ S, kernel A n = q ∧ ∀ a ∈ A, 0 < (n : ℤ) + a ∧ value n a ≤ N ^ K) →
      (S.card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨NF, _hNF, hf⟩ := finite_code_bound K (ε / 2) (by positivity)
  obtain ⟨NP, _hNP, hp⟩ := PolynomialPrimeFactorPowers.uniform_four_pow (K * (d + d ^ 2)) (ε / 2) (by positivity)
  refine ⟨max 2 (max NF NP), by omega, ?_⟩
  intro N hN q A hcard hcardhi S hS
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  by_cases hne : S.Nonempty
  · obtain ⟨n₀, hn₀⟩ := hne
    have hbound := PositiveSplitProducts.kernel_resultant_bound K d N n₀ (by omega) A hcardhi
      (fun a ha ↦ ((hS n₀ hn₀).2 a ha).1) (fun a ha ↦ ((hS n₀ hn₀).2 a ha).2)
    have hpos := Nat.mul_pos (kernel_pos A n₀) (resultant_pos A)
    rw [(hS n₀ hn₀).1] at hbound hpos
    have hpower := hp N (by omega) (q * resultant A) hpos hbound
    calc
      _ ≤ (4 : ℝ) ^ (q * resultant A).primeFactors.card * (N : ℝ) ^ (ε / 2) :=
        hf N (by omega) q A hcard S hS
      _ ≤ (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / 2) :=
        mul_le_mul_of_nonneg_right hpower (Real.rpow_nonneg hn.le _)
      _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring
  · rw [not_nonempty_iff_eq_empty.mp hne, card_empty, Nat.cast_zero]
    exact Real.rpow_nonneg hn.le _

theorem single_square_equation (K d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ A : Finset ℤ, 2 ≤ A.card → A.card ≤ d →
      ∀ c : ℤ, c ≠ 0 → ∀ S : Finset ℕ,
      (∀ n ∈ S, (∀ a ∈ A, 0 < (n : ℤ) + a ∧ value n a ≤ N ^ K) ∧
        IsSquare (c * ∏ a ∈ A, ((n : ℤ) + a))) →
      (S.card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨N₀, hN₀, hN₀count⟩ := uniform_count K d ε hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN A hcard hdegree c hc S hS
  apply hN₀count N hN (SmallPrimeBudget.squarefreeKernel c.natAbs) A hcard hdegree S
  intro n hn
  exact ⟨PositiveSplitProducts.integer_square_kernel A n c hc
    (fun a ha ↦ ((hS n hn).1 a ha).1) (hS n hn).2, (hS n hn).1⟩

theorem two_square_equations (K d : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ A B : Finset ℤ,
      A.Nonempty → B.Nonempty → Disjoint A B → A.card ≤ d → B.card ≤ d →
      ∀ c e : ℤ, c ≠ 0 → e ≠ 0 → ∀ S : Finset ℕ,
      (∀ n ∈ S, (∀ a ∈ A ∪ B, 0 < (n : ℤ) + a ∧ value n a ≤ N ^ K) ∧
        IsSquare (c * ∏ a ∈ A, ((n : ℤ) + a)) ∧ IsSquare (e * ∏ b ∈ B, ((n : ℤ) + b))) →
      (S.card : ℝ) ≤ (N : ℝ) ^ ε := by
  obtain ⟨N₀, hN₀, hcount⟩ := single_square_equation K (2 * d) ε hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN A B hA hB hAB hAc hBc c e hc he S hS
  have hcard : 2 ≤ (A ∪ B).card := by
    rw [card_union_of_disjoint hAB]
    have ha := card_pos.mpr hA
    have hb := card_pos.mpr hB
    omega
  have hdegree : (A ∪ B).card ≤ 2 * d := by rw [card_union_of_disjoint hAB]; omega
  apply hcount N hN (A ∪ B) hcard hdegree (c * e) (mul_ne_zero hc he) S
  intro n hn
  refine ⟨(hS n hn).1, ?_⟩
  rw [prod_union hAB]
  convert ((hS n hn).2.1).mul ((hS n hn).2.2) using 1
  ring

end PaperP1.PolynomialSplitKernelCount
