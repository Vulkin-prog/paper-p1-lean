module

public import PaperP1.Asymptotics.PairActivity

/-! # The unconditional original-model application of main Lemma 15.1

The finite heterogeneous conversion, with a universal constant and larger domain
than the manuscript requires, is already supplied by UniversalRunConversion.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RunConversion

open Finset PaperP1.Model PaperP1.HeterogeneousRunConversion PaperP1.CountObservables

theorem main_15_1 (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ G : Finset ℕ, G ⊆ dyadicBlock N →
      (∑' k : ℕ, |(FiniteLawEmbedding.embed (reference G L) -
        QuadraticPoisson.reference (countMoment G L 1)
          (RegularCumulantTransfer.secondFactorialCumulant G L)) {k}|) ≤
        (N : ℝ) ^ (-5 / 3 + ε) :=
  PairActivity.uniform_conversion C ε hε

end PaperP1.RunConversion
