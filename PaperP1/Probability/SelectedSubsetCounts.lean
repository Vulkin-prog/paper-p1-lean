module

public import PaperP1.Probability.SubsetFactorials

/-! # An exact finite expectation formula for any prescribed class of active subsets -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SelectedSubsetCounts

open Finset PaperP1.Algebra PaperP1.Probability

variable {Ω ι : Type*}

def count (Q : Finset ι → Prop) [DecidablePred Q] (A : Finset ι) (r : ℕ) : ℕ := ((A.powersetCard r).filter Q).card

theorem active_filter (G : Finset ι) (J : ι → Ω → Bool) (ω : Ω) (Q : Finset ι → Prop) [DecidablePred Q] (r : ℕ) :
    ((activeSites G J ω).powersetCard r).filter Q =
      ((G.powersetCard r).filter Q).filter (fun I ↦ ∀ x ∈ I, J x ω = true) := by
  rw [powersetCard_activeSites, filter_filter, filter_filter]
  congr 1
  funext I
  exact propext and_comm

theorem count_eq_sum (G : Finset ι) (J : ι → Ω → Bool) (ω : Ω) (Q : Finset ι → Prop) [DecidablePred Q] (r : ℕ) :
    (count Q (activeSites G J ω) r : ℝ) =
      ∑ I ∈ (G.powersetCard r).filter Q, ∏ x ∈ I, (indicatorValue (J x ω) : ℝ) := by
  simp_rw [indicator_product_eq_indicator]
  rw [sum_boole]
  exact congrArg (fun n : ℕ ↦ (n : ℝ)) (congrArg Finset.card (active_filter G J ω Q r))

theorem count_le_choose (Q : Finset ι → Prop) [DecidablePred Q] (A : Finset ι) (r : ℕ) : count Q A r ≤ A.card.choose r :=
  (card_le_card (filter_subset _ _)).trans_eq (card_powersetCard r A)

variable [Fintype Ω]

theorem finite_mean (P : FiniteProbability Ω) (G : Finset ι) (J : ι → Ω → Bool)
    (Q : Finset ι → Prop) [DecidablePred Q] (r : ℕ) :
    finiteExpectation P.weight (fun ω ↦ (count Q (activeSites G J ω) r : ℝ)) =
      ∑ I ∈ (G.powersetCard r).filter Q, finiteJointMoment P J I := by
  simp_rw [count_eq_sum G J _ Q r]
  exact finiteExpectation_sum _ _ _

end PaperP1.SelectedSubsetCounts
