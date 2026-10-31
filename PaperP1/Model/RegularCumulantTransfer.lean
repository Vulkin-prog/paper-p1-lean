module

public import PaperP1.Model.RegularMomentTransfer

/-! # Transfer of the complete second factorial cumulant

κ₂ = E[Z(Z-1)] - (E Z)². Its exact ordinary-moment expression includes
the diagonal correction -E Z. No distinct-index approximation is used.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RegularCumulantTransfer

open MeasureTheory PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts
open PaperP1.Model.InfiniteRademacher PaperP1.Algebra PaperP1.Probability
open CountObservables RegularStarts RegularMomentTransfer Finset

local instance regularCumulantMeasurableF2 : MeasurableSpace F₂ := ⊤

def secondFactorialCumulant (G : Finset ℕ) (L : ℕ) : ℝ :=
  countMoment G L 2 - countMoment G L 1 - (countMoment G L 1) ^ 2

theorem factorial_second_moment_eq {N L : ℕ} {G : Finset ℕ} (hG : G ⊆ dyadicBlock N) :
    (∫ ω, (infiniteStartCount G L ω : ℝ) * ((infiniteStartCount G L ω : ℝ) - 1)
      ∂infiniteRademacherMeasure) = countMoment G L 2 - countMoment G L 1 := by
  rw [count_observable_integral_eq_finite hG (fun n ↦ (n : ℝ) * ((n : ℝ) - 1)),
    countMoment_eq_finite hG 2, countMoment_eq_finite hG 1, ← finiteExpectation_sub]
  congr 1
  funext ω
  ring

theorem secondFactorialCumulant_eq {N L : ℕ} {G : Finset ℕ} (hG : G ⊆ dyadicBlock N) :
    secondFactorialCumulant G L =
      (∫ ω, (infiniteStartCount G L ω : ℝ) * ((infiniteStartCount G L ω : ℝ) - 1)
        ∂infiniteRademacherMeasure) - (countMoment G L 1) ^ 2 := by
  rw [factorial_second_moment_eq hG]
  rfl

theorem cumulant_difference_bound {a₂ b₂ a₁ b₁ M : ℝ}
    (hb : 0 ≤ b₁) (hba : b₁ ≤ a₁) (haM : a₁ ≤ M) :
    |(a₂ - a₁ - a₁ ^ 2) - (b₂ - b₁ - b₁ ^ 2)| ≤
      |a₂ - b₂| + (1 + 2 * M) * |a₁ - b₁| := by
  have heq : (a₂ - a₁ - a₁ ^ 2) - (b₂ - b₁ - b₁ ^ 2) =
      (a₂ - b₂) - (a₁ - b₁) * (1 + a₁ + b₁) := by ring
  rw [heq]
  have hfactor : |1 + a₁ + b₁| ≤ 1 + 2 * M := by
    rw [abs_of_nonneg (by linarith)]
    linarith
  calc
    _ ≤ |a₂ - b₂| + |(a₁ - b₁) * (1 + a₁ + b₁)| := by
      simpa only [sub_zero, zero_sub, abs_neg] using
        abs_sub_le (a₂ - b₂) 0 ((a₁ - b₁) * (1 + a₁ + b₁))
    _ = |a₂ - b₂| + |1 + a₁ + b₁| * |a₁ - b₁| := by rw [abs_mul, mul_comm]
    _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_right hfactor (abs_nonneg _))

theorem regular_second_factorial_cumulant_transfer_on
    (C : ℝ) (allowed : ℕ → ℕ → Prop) (hmom : BoundedCountMomentsOn C allowed) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ, allowed N L → 0 < L →
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      |secondFactorialCumulant (dyadicBlock N) L -
        secondFactorialCumulant (regularStarts N L) L| ≤ K * (N : ℝ) ^ (-1 + ε) := by
  obtain ⟨K₁, hK₁, N₁, hN₁⟩ := regular_moment_transfer_on C allowed hmom 1 (by omega) ε hε
  obtain ⟨K₂, hK₂, N₂, hN₂⟩ := regular_moment_transfer_on C allowed hmom 2 (by omega) ε hε
  obtain ⟨M, hM, Nm, hNm⟩ := hmom 1 (by omega)
  have hfactor : 0 ≤ 1 + 2 * M := by linarith
  refine ⟨K₂ + (1 + 2 * M) * K₁, add_nonneg hK₂ (mul_nonneg hfactor hK₁),
    max Nm (max N₁ N₂), ?_⟩
  intro N hN L hallowed hL hband
  have hm := hNm N (by omega) L hallowed hL hband
  have h₁ := hN₁ N (by omega) L hallowed hL hband
  have h₂ := hN₂ N (by omega) L hallowed hL hband
  have hb := countMoment_nonneg (N := N) (L := L) (regularStarts_subset N L) 1
  have hba := countMoment_mono (N := N) (L := L) (subset_refl _) (regularStarts_subset N L) 1
  calc
    _ ≤ |countMoment (dyadicBlock N) L 2 - countMoment (regularStarts N L) L 2| +
        (1 + 2 * M) * |countMoment (dyadicBlock N) L 1 -
          countMoment (regularStarts N L) L 1| := cumulant_difference_bound hb hba hm
    _ ≤ K₂ * (N : ℝ) ^ (-1 + ε) + (1 + 2 * M) * (K₁ * (N : ℝ) ^ (-1 + ε)) :=
      add_le_add h₂ (mul_le_mul_of_nonneg_left h₁ hfactor)
    _ = _ := by ring

theorem regular_second_factorial_cumulant_transfer
    (C : ℝ) (hmom : UniformlyBoundedCountMoments C) (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ, 0 < L →
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      |secondFactorialCumulant (dyadicBlock N) L -
        secondFactorialCumulant (regularStarts N L) L| ≤ K * (N : ℝ) ^ (-1 + ε) := by
  simpa only [true_implies] using
    regular_second_factorial_cumulant_transfer_on C (fun _ _ ↦ True) hmom ε hε

theorem regular_second_factorial_cumulant_transfer_along (C : ℝ) (length : ℕ → ℕ)
    (hmom : ∀ q : ℕ, 0 < q → ∃ M : ℝ, 0 ≤ M ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      0 < length N → |(length N : ℝ) - Real.log N / Real.log 2| ≤ C →
        countMoment (dyadicBlock N) (length N) q ≤ M)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, 0 < length N →
      |(length N : ℝ) - Real.log N / Real.log 2| ≤ C →
      |secondFactorialCumulant (dyadicBlock N) (length N) -
        secondFactorialCumulant (regularStarts N (length N)) (length N)| ≤
          K * (N : ℝ) ^ (-1 + ε) := by
  have hm : BoundedCountMomentsOn C (fun N L ↦ L = length N) := by
    intro q hq
    obtain ⟨M, hM, N₀, hN₀⟩ := hmom q hq
    exact ⟨M, hM, N₀, fun N hN L heq ↦ heq.symm ▸ hN₀ N hN⟩
  obtain ⟨K, hK, N₀, hN₀⟩ := regular_second_factorial_cumulant_transfer_on C
    (fun N L ↦ L = length N) hm ε hε
  exact ⟨K, hK, N₀, fun N hN ↦ hN₀ N hN (length N) rfl⟩

end PaperP1.RegularCumulantTransfer
