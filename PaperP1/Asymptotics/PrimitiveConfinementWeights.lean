module

public import PaperP1.Model.PrimitiveTripleWeights
public import PaperP1.Asymptotics.CriticalChannelPowers
public import PaperP1.Asymptotics.HalfCountSchedule
public import PaperP1.Asymptotics.CriticalWindowGeometry

/-! # Primitive original triples satisfy the actual beta=2 confinement weight regime -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimitiveConfinementWeights

open PaperP1.Arithmetic PaperP1.Model.InfiniteStarts PaperP1.TripleProbabilityBound

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem uniform_weights (C θ : ℝ) (hθ : 0 < θ) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ X : Fin 3 → ℕ,
      Function.Injective X → Primitive L X → 0 < X 0 → 0 < X 1 →
      Module.finrank F₂ (squareClassSpace (X 0) L) = L →
      Module.finrank F₂ (squareClassSpace (X 1) L) = L →
      (0 ≤ infiniteJointMoment L (tupleSet X) ∧ infiniteJointMoment L (tupleSet X) ≤ (N : ℝ) ^ (-2 + θ)) ∧
        (0 ≤ HomogeneousRunMass.probability L (tupleSet X) ∧
          HomogeneousRunMass.probability L (tupleSet X) ≤ (N : ℝ) ^ (-2 + θ)) := by
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption (((2 : ℝ) ^ C) ^ 2) (-2) θ hθ
  refine ⟨max 2 (max NG NF), by omega, ?_⟩
  intro N hN L hband X hinj hprim hx hy hrank0 hrank1
  have hgood := PrimitiveTripleWeights.primitive_pair_good X hinj hprim hrank0 hrank1
  have hL : 0 < L := by have hb := (hg N (by omega) L hband).2.2.1; omega
  have hnom : ((2 ^ L : ℝ)⁻¹) ^ 2 ≤ (N : ℝ) ^ (-2 + θ) :=
    (CriticalChannelPowers.nominal_square_upper (by omega) hband).trans (hf N (by omega))
  exact ⟨⟨infiniteJointMoment_nonneg L _, (triple_joint_le X hx hy hL hgood).trans hnom⟩,
    ⟨(HomogeneousRunMass.probability_pos L _).le, (PrimitiveTripleWeights.homogeneous_triple_le X hx hy hgood).trans hnom⟩⟩

end PaperP1.PrimitiveConfinementWeights
