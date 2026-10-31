module

public import PaperP1.Probability.FactorialTuples
public import Mathlib.Data.Finset.Powerset

/-! # Exact unordered-subset expansion of the falling factorial count -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.Probability

open Finset

variable {Ω ι : Type*}

theorem powersetCard_activeSites (G : Finset ι) (J : ι → Ω → Bool) (ω : Ω) (j : ℕ) :
    (activeSites G J ω).powersetCard j =
      (G.powersetCard j).filter (fun I ↦ ∀ x ∈ I, J x ω = true) := by
  classical
  ext I
  rw [mem_powersetCard, mem_filter, mem_powersetCard]
  constructor
  · rintro ⟨hI, hcard⟩
    refine ⟨⟨hI.trans (filter_subset _ _), hcard⟩, ?_⟩
    intro x hx
    exact (mem_filter.mp (hI hx)).2
  · rintro ⟨⟨hIG, hcard⟩, hactive⟩
    refine ⟨?_, hcard⟩
    intro x hx
    exact mem_filter.mpr ⟨hIG hx, hactive x hx⟩

theorem sum_subset_products_eq_choose (G : Finset ι) (J : ι → Ω → Bool) (ω : Ω) (j : ℕ) :
    (∑ I ∈ G.powersetCard j, ∏ x ∈ I, (indicatorValue (J x ω) : ℝ)) =
      ((indicatorCount G J ω).choose j : ℝ) := by
  classical
  simp_rw [indicator_product_eq_indicator]
  rw [sum_boole, ← powersetCard_activeSites G J ω j, card_powersetCard, card_activeSites]

theorem factorial_subset_expansion (G : Finset ι) (J : ι → Ω → Bool) (ω : Ω) (j : ℕ) :
    ((indicatorCount G J ω).descFactorial j : ℝ) =
      (j.factorial : ℝ) * ∑ I ∈ G.powersetCard j,
        ∏ x ∈ I, (indicatorValue (J x ω) : ℝ) := by
  rw [Nat.descFactorial_eq_factorial_mul_choose, Nat.cast_mul, sum_subset_products_eq_choose]

end PaperP1.Probability
