module

public import PaperP1.Asymptotics.CriticalPolynomialScale
public import PaperP1.Arithmetic.DyadicMatchBound
public import PaperP1.Arithmetic.DyadicTargetCount

/-! # Uniform finite endpoint and target counts for the actual matching core -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DyadicMatchingArithmetic

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.ActualNormalizedMatches
  PaperP1.FixedChannelGamma PaperP1.DyadicEndpointPairs PaperP1.DyadicTargetCount

def UniformCore (N L a b J : ℕ) : Prop :=
  (exceptional N a b L ((L + 1) + 2 * (L + 1) ^ J)).card ≤
    (6 * (a + b) + 2) * (L + 1) ^ (J + 2) ∧
  (∀ t : ℕ, (pool a ((L + 1) ^ J) t).card ≤ 6 * a * (L + 1) ^ (3 * J)) ∧
  ∀ x y z t : ℕ, x ∈ dyadicBlock N → y ∈ dyadicBlock N → z ∈ dyadicBlock N →
    ∀ i j : Fin (L + 1), startCompleteVertexLabel x L i = a * t →
      startCompleteVertexLabel y L j = b * t →
      ∀ c d : ℕ, ∀ h : ℤ, 0 < c → 0 < d → c.Coprime d →
        d ≤ (L + 1) ^ J → |h| ≤ ((L + 1) ^ J : ℕ) →
        (d : ℤ) * z = (c : ℤ) * t + h →
        z ∈ pool a ((L + 1) ^ J) t ∧
        ((x, y) ∉ exceptional N a b L ((L + 1) + 2 * (L + 1) ^ J) →
          (x + L ≤ z ∨ z + L ≤ x) → (y + L ≤ z ∨ z + L ≤ y) →
          ((exactOffsets a b c d x y z L).card : ℝ) ≤ ((L + 1 : ℕ) : ℝ) * gammaReal a b + 3)

theorem uniform_core (C : ℝ) {a b J : ℕ} (ha : 0 < a) (hb : 3 ≤ b)
    (hab : a.Coprime b) (horder : a < b) (hJ : 1 ≤ J) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → UniformCore N L a b J := by
  obtain ⟨Ncore, hcore⟩ := CriticalPolynomialScale.source_size_eventually C a J
  refine ⟨max Ncore 2, ?_⟩
  intro N hN L hcrit
  have hNpos : 0 < N := by have := (le_max_right _ _).trans hN; omega
  have hbpos : 0 < b := by omega
  have hHpos : 1 ≤ (L + 1) ^ J := by have h := pow_pos (show 0 < L + 1 by omega) J; omega
  have hsize := hcore N ((le_max_left _ _).trans hN) L ((L + 1) ^ J) hcrit le_rfl
  refine ⟨PolynomialEndpointBudget.exceptional_polynomial hNpos ha hbpos hJ le_rfl,
    (fun t ↦ pool_card_polynomial (t := t) hHpos le_rfl), ?_⟩
  intro x y z t hx hy hz i j hbaseX hbaseY c d h hc hd hcop hdH hh htarget
  refine ⟨actual_target_mem_pool hNpos hx hy hz hc hd hdH hh i j hbaseX hbaseY htarget hsize, ?_⟩
  intro haway hsepX hsepY
  exact DyadicMatchBound.separated_bound hNpos ha hb hab horder hc hd hcop hx hy hz hsepX hsepY
    hdH hh i j hbaseX hbaseY htarget hsize haway

end PaperP1.DyadicMatchingArithmetic
