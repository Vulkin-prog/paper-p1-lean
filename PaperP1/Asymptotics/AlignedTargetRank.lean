module

public import PaperP1.Asymptotics.TargetQuotientRank
public import PaperP1.Asymptotics.DyadicMatchingArithmetic
public import PaperP1.Arithmetic.CompressedTargetAlignment

/-! # Target counts and actual quotient rank from literal compressed alignment -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AlignedTargetRank

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.FixedChannelGamma
  PaperP1.CompressedTargetAlignment PaperP1.DyadicEndpointPairs PaperP1.TargetWindowRank

def targets (D N a b t L : ℕ) : Finset ℕ := by
  classical
  exact (dyadicBlock N).filter fun z ↦ Aligned D (a * b * t) z L

def endpointSources (N a b L : ℕ) : Finset (ℕ × ℕ) :=
  exceptional N a b L ((L + 1) + 2 * (L + 1) ^ 5)

def Conclusion (D N a b L : ℕ) (ε : ℝ) : Prop :=
  (endpointSources N a b L).card ≤ (6 * (a + b) + 2) * (L + 1) ^ 7 ∧
  ∀ x y t : ℕ, x ∈ dyadicBlock N → y ∈ dyadicBlock N →
    ∀ i j : Fin (L + 1), startCompleteVertexLabel x L i = a * t →
      startCompleteVertexLabel y L j = b * t →
      (targets D N a b t L).card ≤ 6 * a * (L + 1) ^ 15 ∧
      ∀ z ∈ targets D N a b t L,
        (x + L ≤ z ∨ z + L ≤ x) → (y + L ≤ z ∨ z + L ≤ y) →
        (x, y) ∉ endpointSources N a b L →
        ∀ Q : Finset ℕ, Q ⊆ (a * b).primeFactors →
          (deficiency Q x y z L : ℝ) ≤ (gammaReal a b + ε) * L

theorem uniform_core (C ε : ℝ) (hε : 0 < ε) {a b : ℕ} (ha : 0 < a) (hb : 3 ≤ b)
    (hab : a.Coprime b) (horder : a < b) (D : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → Conclusion D N a b L ε := by
  classical
  obtain ⟨Nrank, hrank⟩ := TargetQuotientRank.bounded_affine_rank C ε hε ha hb hab horder 5
  obtain ⟨Ndyadic, hdyadic⟩ := DyadicMatchingArithmetic.uniform_core C ha hb hab horder (by norm_num : 1 ≤ 5)
  obtain ⟨Ngeom, hgeom⟩ := CriticalWindowGeometry.uniform_geometry C (2 * D)
  refine ⟨max Nrank (max Ndyadic Ngeom), ?_⟩
  intro N hN L hcrit
  obtain ⟨_, hBD, _, _, _, _⟩ := hgeom N ((le_max_right Ndyadic Ngeom).trans ((le_max_right _ _).trans hN)) L hcrit
  have hdy := hdyadic N ((le_max_left Ndyadic Ngeom).trans ((le_max_right _ _).trans hN)) L hcrit
  have hbpos : 0 < b := by omega
  refine ⟨hdy.1, ?_⟩
  intro x y t hx hy i j hbaseX hbaseY
  have hsub : targets D N a b t L ⊆ DyadicTargetCount.pool a ((L + 1) ^ 5) t := by
    intro z hz
    obtain ⟨hzdyad, hza⟩ := mem_filter.mp hz
    obtain ⟨c, d, h, hc, hd, hcop, hdH, hh, htarget⟩ := bounded_data ha hbpos hBD hza
    exact (hdy.2.2 x y z t hx hy hzdyad i j hbaseX hbaseY c d h hc hd hcop hdH hh htarget).1
  refine ⟨(card_le_card hsub).trans (hdy.2.1 t), ?_⟩
  intro z hz hsepX hsepY haway Q hQ
  obtain ⟨hzdyad, hza⟩ := mem_filter.mp hz
  obtain ⟨c, d, h, hc, hd, hcop, hdH, hh, htarget⟩ := bounded_data ha hbpos hBD hza
  exact hrank N ((le_max_left _ _).trans hN) L c d x y z t hcrit hc hd hcop hdH
    hx hy hzdyad hsepX hsepY haway i j hbaseX hbaseY h hh htarget Q hQ

end PaperP1.AlignedTargetRank
