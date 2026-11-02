module

public import PaperP1.Probability.ActivePairCount

/-! # The exact first Bonferroni correction for a positive integer-valued count -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositiveCountBonferroni

open PaperP1.Algebra PaperP1.Probability

local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem pointwise (n : ℕ) :
    0 ≤ (n : ℝ) - (if 0 < (n : ℝ) then 1 else 0) ∧
      (n : ℝ) - (if 0 < (n : ℝ) then 1 else 0) ≤ (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  by_cases hn : n = 0
  · subst n
    norm_num
  by_cases hn1 : n = 1
  · subst n
    norm_num
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
  rw [ite_eq_left (by linarith only [hn2] : (0 : ℝ) < n)]
  have hp := mul_nonneg (by linarith only [hn2] : (0 : ℝ) ≤ n - 2)
    (by linarith only [hn2] : (0 : ℝ) ≤ n - 1)
  exact ⟨by linarith only [hn2], by nlinarith only [hp]⟩

theorem finite_bound {Ω : Type*} [Fintype Ω] (P : FiniteProbability Ω) (X : Ω → ℝ)
    (hNat : ∀ ω, ∃ n : ℕ, X ω = n) :
    0 ≤ finiteExpectation P.weight X - finiteExpectation P.weight (fun ω ↦ if 0 < X ω then 1 else 0) ∧
      finiteExpectation P.weight X - finiteExpectation P.weight (fun ω ↦ if 0 < X ω then 1 else 0) ≤
        finiteExpectation P.weight (fun ω ↦ X ω * (X ω - 1)) / 2 := by
  have hlo : finiteExpectation P.weight (fun ω ↦ if 0 < X ω then 1 else 0) ≤ finiteExpectation P.weight X := by
    apply finiteExpectation_mono P
    intro ω
    obtain ⟨n, hn⟩ := hNat ω
    rw [hn]
    linarith only [(pointwise n).1]
  have hup : finiteExpectation P.weight (fun ω ↦ X ω - (if 0 < X ω then 1 else 0)) ≤
      finiteExpectation P.weight (fun ω ↦ X ω * (X ω - 1) / 2) := by
    apply finiteExpectation_mono P
    intro ω
    obtain ⟨n, hn⟩ := hNat ω
    rw [hn]
    exact (pointwise n).2
  rw [finiteExpectation_sub] at hup
  have heq : finiteExpectation P.weight (fun ω ↦ X ω * (X ω - 1) / 2) =
      finiteExpectation P.weight (fun ω ↦ X ω * (X ω - 1)) / 2 := by
    simpa only [div_eq_mul_inv] using
      finiteExpectation_mul_const P.weight (fun ω ↦ X ω * (X ω - 1)) (2 : ℝ)⁻¹
  rw [heq] at hup
  exact ⟨by linarith only [hlo], hup⟩

end PaperP1.PositiveCountBonferroni
