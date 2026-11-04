module

public import PaperP1.Asymptotics.BoundedBlockIndependentTail
public import PaperP1.Asymptotics.CompressedAsymmetricCoarseProfile

/-! # Literal geometrically compressed source blocks in the independent tail

The labels are the true normalized source values. The index is shifted to the
left end of a containing complete window, without changing any physical label.
Bad normalization and nonprivate source values are allowed.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CompressedBlockIndependentTail

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.CompressedSourceBlocks
  PaperP1.DyadicEndpointPairs

def shiftedBlock (N a b L : ℕ) (i j : Fin (L + 1)) (x : ℕ) : Finset ℕ :=
  CompressedSourceBlocks.block N a b L i j (x + b * (L + 1) - 1)

theorem contained {N a b L x : ℕ} (hN : 0 < N) (hab : a ≤ b) (hx : 2 ≤ x)
    (i j : Fin (L + 1)) :
    shiftedBlock N a b L i j x ⊆ NormalizedWindowSets.values x (2 * b * (L + 1)) := by
  intro n hn
  obtain ⟨xy, hxy, hnu⟩ := mem_biUnion.mp hn
  obtain ⟨hsource, hanchor⟩ := mem_filter.mp hxy
  have hh := source_abs_bound hN hab i j hsource hnu
  rw [hanchor] at hh
  have hb := abs_le.mp hh
  have hlo : x + b * (L + 1) - 1 ≤ n + b * L := by exact_mod_cast (by linarith only [hb.1] :
    ((x + b * (L + 1) - 1 : ℕ) : ℤ) ≤ (n : ℤ) + (b * L : ℕ))
  have hhi : n ≤ x + b * (L + 1) - 1 + b * L := by exact_mod_cast (by linarith only [hb.2] :
    (n : ℤ) ≤ ((x + b * (L + 1) - 1 : ℕ) : ℤ) + (b * L : ℕ))
  rw [NormalizedWindowSets.values_eq_interval (by omega : 0 < x)]
  have hR : b * (L + 1) = b * L + b := by ring
  have hH : 2 * b * (L + 1) = 2 * (b * L) + 2 * b := by ring
  rw [hR] at hlo hhi
  rw [hH]
  apply mem_Ico.mpr
  omega

theorem anchor_centre {N a b L : ℕ} (hN : 2 ≤ N) (hLN : L ≤ N) (hb : 2 ≤ b)
    (hwidth : b * (L + 1) < N) (i j : Fin (L + 1)) {xy : ℕ × ℕ}
    (hxy : xy ∈ sourcePairs N a b L i j) :
    let x := anchor b L i xy - b * (L + 1) + 1
    x ∈ Ico 2 ((3 * b + 2) * N + 2) ∧
      shiftedBlock N a b L i j x = CompressedSourceBlocks.block N a b L i j (anchor b L i xy) := by
  dsimp only
  have hanchor := CompressedAsymmetricCoarseProfile.anchor_mem_expanded hN hLN hb i j hxy
  obtain ⟨hlo, hhi⟩ := mem_Ico.mp hanchor
  have hrecover : anchor b L i xy - b * (L + 1) + 1 + b * (L + 1) - 1 = anchor b L i xy := by omega
  refine ⟨mem_Ico.mpr ⟨by omega, ?_⟩, ?_⟩
  · have hQN : N + 3 * b * N ≤ (3 * b + 2) * N := by nlinarith
    omega
  · unfold shiftedBlock
    rw [hrecover]

theorem uniform_channel (a b : ℕ) (hab : a ≤ b) (hb : 1 ≤ b) (C v r ε : ℝ)
    (hv : 0 < v) (hr : r < 2) (hε : 0 < ε) :
    ∃ s : ℕ, 2 ≤ s ∧ ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ i j : Fin (L + 1),
      BoundedBlockIndependentTail.mass (3 * b + 2) N L s v (shiftedBlock N a b L i j) ≤
        (N : ℝ) ^ (-r + ε) := by
  obtain ⟨s, hs, N₀, hN₀, ht⟩ := BoundedBlockIndependentTail.uniform_blocks (2 * b) (3 * b + 2)
    (by omega) (by omega) C v r ε hv hr hε
  refine ⟨s, hs, N₀, hN₀, ?_⟩
  intro N hN L hband i j
  exact ht N hN L hband _ (fun x hx ↦ contained (by omega) hab (mem_Ico.mp hx).1 i j)

end PaperP1.CompressedBlockIndependentTail
