module

public import PaperP1.Asymptotics.CoupledPrincipalSourceCount
public import PaperP1.Model.PrincipalEdgeSpaces
public import PaperP1.Asymptotics.LogarithmicWordPowers
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-! # The literal actual principal-edge population with coupled event spaces has only N^(1+epsilon) pairs -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CoupledPrincipalEdgesCount

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.PrincipalSourcePatterns PaperP1.CriticalBandScale

local instance (P : Prop) : Decidable P := Classical.propDecidable P

abbrev Code (L : ℕ) := Σ _pq : Pattern L × Pattern L, (ℕ × ℕ) × (ℕ × ℕ)

def pool (N L : ℕ) : Finset (Code L) :=
  (univ : Finset (Pattern L × Pattern L)).sigma fun pq ↦ CoupledPrincipalSourceCount.coupled N L pq.1 pq.2

def edgePair {L : ℕ} (c : Code L) : Finset ℕ × Finset ℕ :=
  ({c.2.1.1, c.2.1.2}, {c.2.2.1, c.2.2.2})

theorem source_cover {N H L : ℕ} (hN : 0 < N) :
    PrincipalEdgeSpaces.coupledPairs N H L ⊆ (pool N L).image edgePair := by
  intro ef hef
  obtain ⟨hbox, hdep⟩ := mem_filter.mp hef
  obtain ⟨he, hf⟩ := mem_product.mp hbox
  obtain ⟨p, xy, hxy, heq⟩ := source_of_edge hN he
  obtain ⟨q, uv, huv, hfq⟩ := source_of_edge hN hf
  have hcoupled : (xy, uv) ∈ CoupledPrincipalSourceCount.coupled N L p q := by
    apply mem_filter.mpr
    refine ⟨mem_product.mpr ⟨hxy, huv⟩, ?_⟩
    simpa only [heq, hfq, PrincipalEdgeSpaces.space_pair] using hdep
  refine mem_image.mpr ⟨⟨(p, q), (xy, uv)⟩, mem_sigma.mpr ⟨mem_univ _, hcoupled⟩, ?_⟩
  exact Prod.ext heq.symm hfq.symm

theorem uniform_pool_count (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ((pool N L).card : ℝ) ≤ (N : ℝ) ^ (1 + ε) := by
  obtain ⟨NC, _hNC, hc⟩ := CoupledPrincipalSourceCount.uniform_count C (ε / 2) (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 0
  obtain ⟨NP, hp⟩ := LogarithmicWordPowers.polynomial_factor_le_rpow_eventually upperScale
    upperScale_pos.le 4 4 (ε / 2) (by positivity)
  refine ⟨max 2 (max NC (max NG NP)), by omega, ?_⟩
  intro N hN L hband
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hfactor : 4 * ((L + 1 : ℕ) : ℝ) ^ 4 ≤ (N : ℝ) ^ (ε / 2) := by
    have hh := hp N (by omega) L (hg N (by omega) L hband).2.2.2.2.2
    simpa only [Nat.cast_add, Nat.cast_one, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * (L + 1 : ℝ) ^ 4)] using hh
  calc
    _ = ∑ pq : Pattern L × Pattern L, ((CoupledPrincipalSourceCount.coupled N L pq.1 pq.2).card : ℝ) := by
      rw [pool, card_sigma, Nat.cast_sum]
    _ ≤ ∑ _pq : Pattern L × Pattern L, (N : ℝ) ^ (1 + ε / 2) :=
      sum_le_sum (fun pq _ ↦ hc N (by omega) L hband pq.1 pq.2)
    _ = (4 * ((L + 1 : ℕ) : ℝ) ^ 4) * (N : ℝ) ^ (1 + ε / 2) := by
      rw [sum_const, nsmul_eq_mul, card_univ, Fintype.card_prod, patterns_card]
      push_cast
      ring
    _ ≤ (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (1 + ε / 2) :=
      mul_le_mul_of_nonneg_right hfactor (Real.rpow_nonneg hn.le _)
    _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring

theorem uniform_count (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ((PrincipalEdgeSpaces.coupledPairs N H L).card : ℝ) ≤ (N : ℝ) ^ (1 + ε) := by
  obtain ⟨N₀, hN₀, hc⟩ := uniform_pool_count C ε hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L H hband
  have hh := (card_le_card (source_cover (H := H) (L := L) (by omega : 0 < N))).trans card_image_le
  exact (by exact_mod_cast hh : ((PrincipalEdgeSpaces.coupledPairs N H L).card : ℝ) ≤ (pool N L).card).trans
    (hc N hN L hband)

end PaperP1.CoupledPrincipalEdgesCount
