module

public import PaperP1.Asymptotics.FixedChannelPairProbability
public import PaperP1.Asymptotics.PrincipalChannelEdgesPhase
public import PaperP1.Model.PrincipalEdgeGeometry

/-! # Uniform actual principal-edge probabilities and an actual beta-squared lower scale -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrincipalEdgeProbability

open Finset PaperP1.Model.InfiniteStarts PaperP1.PrincipalChannelEdges

theorem uniform_coarse (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ e ∈ edges N H L,
      infiniteJointMoment L e ≤ (N : ℝ) ^ (-5 / 3 + ε) := by
  obtain ⟨N23, _hN23, h23⟩ := FixedChannelPairProbability.uniform_coarse
    (a := 2) (b := 3) (by decide) (by decide) (by decide) (by decide) C ε hε
  obtain ⟨N34, _hN34, h34⟩ := FixedChannelPairProbability.uniform_coarse
    (a := 3) (b := 4) (by decide) (by decide) (by decide) (by decide) C ε hε
  refine ⟨max 10 (max N23 N34), by omega, ?_⟩
  intro N hN L H hband e he
  rcases mem_union.mp he with he | he
  · obtain ⟨x, y, heq, hx, hy, hu, _hgeom⟩ := PrincipalEdgeGeometry.channel_data (by omega : 0 < N) he
    rw [heq]
    exact h23 N (by omega) L x y hband hx hy hu
  · obtain ⟨x, y, heq, hx, hy, hu, _hgeom⟩ := PrincipalEdgeGeometry.channel_data (by omega : 0 < N) he
    rw [heq]
    exact h34 N (by omega) L x y hband hx hy hu

theorem beta_squared_lower (C : ℝ) (D : ℕ) :
    ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → 8 * (L + 1) ≤ H → H ≤ D * (L + 1) →
      c * (N : ℝ) ^ (-4 / 3 : ℝ) ≤ beta N H L ^ 2 := by
  obtain ⟨c, _k, hc, _hk, NB, _hNB, hb⟩ := PrincipalChannelEdgesPhase.positive_phase C D
  obtain ⟨NG, _hNG, hg⟩ := PrincipalChannelEdgesPhase.uniform_geometry C
  refine ⟨c ^ 2, by positivity, max 2 (max NB NG), by omega, ?_⟩
  intro N hN L H hband hcut hH
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL : (1 : ℝ) ≤ L := by exact_mod_cast (hg N (by omega) L hband).1
  have hphase := (hb N (by omega) L H hband hcut hH).1
  have hbase : c * (N : ℝ) ^ (-2 / 3 : ℝ) ≤ beta N H L := by
    have hmul := mul_le_mul_of_nonneg_left hL hc.le
    exact (mul_le_mul_of_nonneg_right (by simpa only [mul_one] using hmul)
      (Real.rpow_nonneg hn.le (-2 / 3))).trans hphase
  have hpow2 : ((N : ℝ) ^ (-2 / 3 : ℝ)) ^ 2 = (N : ℝ) ^ (-4 / 3 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le]
    congr 1
    norm_num
  have hh := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ c * (N : ℝ) ^ (-2 / 3 : ℝ)) hbase 2
  rwa [mul_pow, hpow2] at hh

end PaperP1.PrincipalEdgeProbability
