module

public import PaperP1.Arithmetic.SeparatedPacking
public import PaperP1.Model.InfiniteStarts
public import PaperP1.Probability.FactorialTuples

/-! # Deterministic separation and exact support of the actual run count -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RunSeparation

open PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts
open PaperP1.Model.InfiniteRademacher PaperP1.Probability Finset

local instance runSeparationPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

theorem startEvent_separated (g : ℕ → F₂) {x y L : ℕ}
    (hx : StartEvent g x L) (hy : StartEvent g y L) (hxy : x < y) : x + L ≤ y := by
  by_contra hgap
  have hyclose : y < x + L := Nat.lt_of_not_ge hgap
  have hprev : x + (y - 1 - x) = y - 1 := by omega
  have hcurr : x + (y - x) = y := by omega
  have h₁ := hx.2 (y - 1 - x) (by omega)
  have h₂ := hx.2 (y - x) (by omega)
  rw [hprev] at h₁
  rw [hcurr] at h₂
  have hboundary := hy.1
  rw [h₁.trans h₂.symm, ← two_mul] at hboundary
  have htwo : (2 : F₂) = 0 := by decide
  rw [htwo, zero_mul] at hboundary
  exact zero_ne_one hboundary

theorem infiniteStartIndicator_separated (ω : InfiniteSample) {x y L : ℕ}
    (hx : infiniteStartIndicator x L ω = true) (hy : infiniteStartIndicator y L ω = true)
    (hxy : x < y) : x + L ≤ y := by
  have hxevent : StartEvent (infiniteValueBit ω) x L := by
    simpa only [infiniteStartIndicator, decide_eq_true_eq] using hx
  have hyevent : StartEvent (infiniteValueBit ω) y L := by
    simpa only [infiniteStartIndicator, decide_eq_true_eq] using hy
  exact startEvent_separated _ hxevent hyevent hxy

theorem infiniteStartCount_interval_support {U N L : ℕ} (hN : 0 < N) (hL : 0 < L)
    (ω : InfiniteSample) :
    infiniteStartCount (Ico U (U + N)) L ω ≤ ⌈(N : ℝ) / L⌉₊ := by
  rw [infiniteStartCount, ← card_activeSites]
  apply SeparatedPacking.card_separated_interval hN hL
    (activeSites (Ico U (U + N)) (fun x ↦ infiniteStartIndicator x L) ω)
    (filter_subset _ _)
  intro x hx y hy hxy
  exact infiniteStartIndicator_separated ω (mem_filter.mp hx).2 (mem_filter.mp hy).2 hxy

theorem dyadic_count_support {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) (ω : InfiniteSample) :
    0 ≤ infiniteStartCount (dyadicBlock N) L ω ∧
      infiniteStartCount (dyadicBlock N) L ω ≤ ⌈(N : ℝ) / L⌉₊ := by
  refine ⟨Nat.zero_le _, ?_⟩
  have h := infiniteStartCount_interval_support (U := N) (by omega : 0 < N) hL ω
  simpa only [dyadicBlock, two_mul] using h

end PaperP1.RunSeparation
