module

public import PaperP1.Coding.IndependentRepresentations
public import PaperP1.Coding.CoordinateRegularisation

/-! # Article Lemma 6.1: the complete disjoint-recovery conclusion -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DisjointRecoveryTheorem

open Finset PaperP1.Arithmetic PaperP1.CoordinateForms PaperP1.DisjointRecoverySubspace
open PaperP1.RecoveryLabelSupports PaperP1.IndependentRepresentations

local instance disjointRecoveryTheoremPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

variable {K U V : Type*} [Field K] [AddCommGroup U] [Module K U]
variable [Fintype V] [DecidableEq V]

local instance recoveryTheoremDualDecidableEq (M : Submodule K U) : DecidableEq (Module.Dual K M) :=
  Classical.decEq _

def RecoveryConclusion (L : V → Module.Dual K U) (M : Submodule K U)
    (d t representationBase : ℕ) : Prop :=
  ((Module.finrank K U - Module.finrank K M : ℕ) : ℝ) ≤
      2 * (Fintype.card V : ℝ) * DisjointRecoveryParameters.parameter d t ∧
  NoDisjointRecovery L M d t ∧
  (∀ α : Module.Dual K M, α ≠ 0 →
    (univ.filter fun v ↦ (L v).comp M.subtype = α).card ≤ t - 1) ∧
  (∀ j : ℕ, 1 ≤ j → j ≤ d → ∀ α : Module.Dual K M, α ≠ 0 →
    (independentRepresentations K (labels L M) j α).card ≤ j.factorial * representationBase ^ (j - 1))

theorem disjoint_recovery_sharp [FiniteDimensional K U] (L : V → Module.Dual K U)
    (d t : ℕ) (hd : 1 ≤ d) (ht : 2 ≤ t) :
    ∃ M : Submodule K U, RecoveryConclusion L M d t (t - 1) := by
  obtain ⟨M, hcost, hno⟩ := exists_small_recovery_subspace L d t hd ht
  have hlabels := noDisjointSums_of_recovery_exclusion L M d t (by omega) hno
  refine ⟨M, hcost, hno, ?_, ?_⟩
  · exact coordinate_multiplicity_le L M d t hd hno
  · intro j hj hjd α hα
    exact independentRepresentations_card_le (labels L M) d t hlabels j hj hjd α hα

theorem disjoint_recovery [FiniteDimensional K U] (L : V → Module.Dual K U)
    (d t : ℕ) (hd : 1 ≤ d) (ht : 2 ≤ t) :
    ∃ M : Submodule K U, RecoveryConclusion L M d t t := by
  obtain ⟨M, hcost, hno, hmult, hreps⟩ := disjoint_recovery_sharp L d t hd ht
  refine ⟨M, hcost, hno, hmult, ?_⟩
  intro j hj hjd α hα
  exact (hreps j hj hjd α hα).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.sub_le t 1) (j - 1)))

/-- Literal binary coordinate specialization, with every source conclusion. -/
theorem main_6_1 (R : Submodule F₂ (V → F₂)) (d t : ℕ) (hd : 1 ≤ d) (ht : 2 ≤ t) :
    ∃ M : Submodule F₂ R, RecoveryConclusion (coordinateFamily R) M d t t :=
  disjoint_recovery (coordinateFamily R) d t hd ht

end PaperP1.DisjointRecoveryTheorem
