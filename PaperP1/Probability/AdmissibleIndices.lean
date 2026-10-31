module

public import PaperP1.Probability.Convolution

/-!
# Removing zero-probability indicators without changing the law

The paper expands over the admissible set of sites with positive exact
marginal. For arbitrary finite probability spaces an indicator with zero
marginal can still be true at a zero-weight sample. The count law is unchanged
when these sites are removed; no pointwise impossibility premise is assumed.
-/

@[expose] public noncomputable section

open scoped BigOperators
open PaperP1.Algebra

namespace PaperP1.Probability

variable {Ω ι : Type*} [Fintype Ω]

def positiveMarginalSet (G : Finset ι) (P : FiniteProbability Ω)
    (J : ι → Ω → Bool) : Finset ι := by
  classical
  exact G.filter fun x => 0 < exactMarginal P J x

/-- A true indicator at a sample of positive weight has positive exact marginal. -/
theorem positive_marginal_of_positive_weight (P : FiniteProbability Ω)
    (J : ι → Ω → Bool) (x : ι) (ω : Ω) (hw : 0 < P.weight ω) (hJ : J x ω = true) :
    0 < exactMarginal P J x := by
  apply lt_of_lt_of_le hw
  unfold exactMarginal finiteExpectation
  have hnonneg : ∀ σ ∈ (Finset.univ : Finset Ω),
      0 ≤ P.weight σ * indicatorValue (J x σ) := by
    intro σ _
    cases J x σ <;> simp [indicatorValue, P.weight_nonneg]
  have hle := Finset.single_le_sum hnonneg (Finset.mem_univ ω)
  simpa [indicatorValue, hJ] using hle

/-- Deleting all zero-marginal sites preserves the entire weighted count law. -/
theorem countLaw_restrict_positiveMarginals (G : Finset ι) (P : FiniteProbability Ω)
    (J : ι → Ω → Bool) :
    countLaw G P.weight J = countLaw (positiveMarginalSet G P J) P.weight J := by
  classical
  unfold countLaw
  apply Finset.sum_congr rfl
  intro ω _
  by_cases hw : P.weight ω = 0
  · simp [hw]
  · have hwpos : 0 < P.weight ω := lt_of_le_of_ne (P.weight_nonneg ω) (Ne.symm hw)
    have hcount : indicatorCount (positiveMarginalSet G P J) J ω = indicatorCount G J ω := by
      unfold indicatorCount
      apply Finset.sum_subset (Finset.filter_subset (fun x => 0 < exactMarginal P J x) G)
      intro x hx hxnot
      have hpnot : ¬ 0 < exactMarginal P J x := by
        intro hp
        exact hxnot (Finset.mem_filter.mpr ⟨hx, hp⟩)
      have hj : J x ω = false := by
        cases h : J x ω with
        | false => rfl
        | true => exact False.elim (hpnot (positive_marginal_of_positive_weight P J x ω hwpos h))
      simp [hj]
    rw [hcount]

end PaperP1.Probability
