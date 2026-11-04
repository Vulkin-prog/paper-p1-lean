module

public import PaperP1.Asymptotics.HomogeneousBoundedBlockIndependentTail
public import PaperP1.Asymptotics.CompressedBlockIndependentTail

/-! # Actual compressed source blocks with all homogeneous effective target marginals -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HomogeneousCompressedBlockIndependentTail

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.CompressedBlockIndependentTail

theorem uniform_channel (a b : ℕ) (hab : a ≤ b) (hb : 1 ≤ b) (C v r ε : ℝ)
    (hv : 0 < v) (hr : r < 2) (hε : 0 < ε) :
    ∃ s : ℕ, 2 ≤ s ∧ ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ i j : Fin (L + 1),
      HomogeneousBoundedBlockIndependentTail.mass (3 * b + 2) N L s v (shiftedBlock N a b L i j) ≤
        (N : ℝ) ^ (-r + ε) := by
  obtain ⟨s, hs, N₀, hN₀, ht⟩ := HomogeneousBoundedBlockIndependentTail.uniform_blocks (2 * b) (3 * b + 2)
    (by omega) (by omega) C v r ε hv hr hε
  refine ⟨s, hs, N₀, hN₀, ?_⟩
  intro N hN L hband i j
  exact ht N hN L hband _ (fun x hx ↦ contained (by omega) hab (mem_Ico.mp hx).1 i j)

end PaperP1.HomogeneousCompressedBlockIndependentTail
