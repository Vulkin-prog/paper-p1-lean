module

public import PaperP1.Probability.PositionalPoissonAccidents

/-! # An accidental edge or a point in a selected set has its actual union bound -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositionalPoissonBadEvents

open Finset PaperP1.PositionalFiniteLaw PaperP1.CompletedPositionalLaw
  PaperP1.PositionalPairDeletion PaperP1.PositionalPoissonObservables

variable {ι : Type*}

local instance poissonBadEventsDecidable (P : Prop) : Decidable P := Classical.propDecidable P

theorem active_or_subset_bound (G S : Finset ι) (hS : S ⊆ G) (p : ι → ℝ)
    (hp : ∀ x ∈ G, 0 ≤ p x) (E : Finset (Finset ι))
    (hE : ∀ e ∈ E, e ⊆ G ∧ e.card = 2) :
    Summable (fun v : Configuration ι ↦
      if (activeEdges E v).Nonempty ∨ 0 < subsetCount S v then
        coeff v (PositionalBernoulliProducts.poisson G p) else 0) ∧
      (∑' v : Configuration ι,
        if (activeEdges E v).Nonempty ∨ 0 < subsetCount S v then
          coeff v (PositionalBernoulliProducts.poisson G p) else 0) ≤
        (∑ e ∈ E, ∏ x ∈ e, p x) + ∑ x ∈ S, p x := by
  have ha := PositionalPoissonAccidents.any_active_bound G p hp E hE
  have hm := hasSum_subset_factorial G S hS p hp 1
  simp only [Nat.descFactorial_one, pow_one] at hm
  have hn := (poisson_isProbability G p hp).1
  have hpoint (v : Configuration ι) :
      (if (activeEdges E v).Nonempty ∨ 0 < subsetCount S v then
        coeff v (PositionalBernoulliProducts.poisson G p) else 0) ≤
      (if (activeEdges E v).Nonempty then coeff v (PositionalBernoulliProducts.poisson G p) else 0) +
        coeff v (PositionalBernoulliProducts.poisson G p) * (subsetCount S v : ℝ) := by
    by_cases he : (activeEdges E v).Nonempty
    · rw [ite_eq_left (Or.inl he), ite_eq_left he]
      exact le_add_of_nonneg_right (mul_nonneg (hn v) (Nat.cast_nonneg _))
    · rw [ite_eq_right he, zero_add]
      by_cases hs : 0 < subsetCount S v
      · rw [ite_eq_left (Or.inr hs)]
        have hc : (1 : ℝ) ≤ subsetCount S v := by exact_mod_cast Nat.succ_le_of_lt hs
        simpa only [mul_one] using mul_le_mul_of_nonneg_left hc (hn v)
      · rw [ite_eq_right (not_or.mpr ⟨he, hs⟩)]
        exact mul_nonneg (hn v) (Nat.cast_nonneg _)
  have hs := Summable.of_nonneg_of_le
    (fun v ↦ by split_ifs; exact hn v; exact le_rfl) hpoint (ha.1.add hm.summable)
  refine ⟨hs, ?_⟩
  have hh := hs.tsum_le_tsum hpoint (ha.1.add hm.summable)
  rw [ha.1.tsum_add hm.summable, hm.tsum_eq] at hh
  exact hh.trans (add_le_add ha.2 le_rfl)

end PaperP1.PositionalPoissonBadEvents
