module

public import PaperP1.Asymptotics.PlanarResidualRankHosts
public import PaperP1.Asymptotics.OrderedPrimitiveHostCount

/-! # The unrestricted primitive-host assertion of T20.8 follows from the stronger general host count -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ResidualPrimitiveHostCount

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.ManyPlanarSquareProducts
  PaperP1.PlanarResidualRankHosts

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def hosts (N L : ℕ) (C₀ η : ℝ) : Finset (Fin 3 → ℕ) :=
  (Fintype.piFinset fun _ : Fin 3 ↦ dyadicBlock N).filter fun X ↦
    RegularDirect N L X ∧ TripleProbabilityBound.Primitive L X ∧
      Residual η X L (TripleCoverRank.cutoff C₀ L)

theorem hosts_data {N L : ℕ} {C₀ η : ℝ} {X : Fin 3 → ℕ} (hX : X ∈ hosts N L C₀ η) :
    RegularDirect N L X ∧ TripleProbabilityBound.Primitive L X ∧
      Residual η X L (TripleCoverRank.cutoff C₀ L) := (mem_filter.mp hX).2

theorem all_primitive_triples (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ S : Finset (Fin 3 → ℕ),
      (∀ X ∈ S, RegularDirect N L X ∧ TripleProbabilityBound.Primitive L X) →
      (S.card : ℝ) ≤ (N : ℝ) ^ (3 / 2 + ε) := by
  obtain ⟨N₀, hN₀, hu⟩ := OrderedPrimitiveHostCount.uniform_count 3 (by omega) C ε hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband S hS
  apply hu N hN L hband (dyadicBlock N) (subset_refl _) S
  intro X hX
  have hh := hS X hX
  exact ⟨hh.1.1, fun i ↦ (hh.1.2.1 i).1, hh.2⟩

/-- No lower bound on the residual rank is needed for this unrestricted primitive count. -/
theorem source_unrestricted_assertion (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ C₀ η : ℝ,
      ((hosts N L C₀ η).card : ℝ) ≤ (N : ℝ) ^ (3 / 2 + ε) := by
  obtain ⟨N₀, hN₀, hu⟩ := all_primitive_triples C ε hε
  exact ⟨N₀, hN₀, fun N hN L hband C₀ η ↦ hu N hN L hband (hosts N L C₀ η)
    (fun _ hX ↦ ⟨(hosts_data hX).1, (hosts_data hX).2.1⟩)⟩

end PaperP1.ResidualPrimitiveHostCount
