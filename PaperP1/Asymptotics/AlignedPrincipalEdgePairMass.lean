module

public import PaperP1.Model.AlignedPrincipalEdgePairs
public import PaperP1.Asymptotics.PrincipalEdgeProbability

/-! # The complete aligned four-vertex principal-edge sector is negligible relative to beta squared -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AlignedPrincipalEdgePairMass

open Finset PaperP1.Model.InfiniteStarts PaperP1.PrincipalChannelEdges PaperP1.AlignedPrincipalEdgePairs

local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem source_cover (J : ℕ) (C : ℝ) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ p ∈ PrincipalEdgeSpaces.factorialPairs N H L, Disjoint p.1 p.2 →
      ∀ T : Finset ℕ, T ⊆ PaperP1.Model.dyadicBlock N → T.card = 3 → T ⊆ p.1 ∪ p.2 →
      (∃ ab ∈ PrincipalEdgeGeometry.channels, Nonempty (AllAlignedTargetTripleMass.Representation N L ab.1 ab.2 J T)) →
      p ∈ pairs N H L J := by
  obtain ⟨NR, hNR, hr⟩ := FiniteAlignedTargetTripleMass.all_actual_sources PrincipalEdgeGeometry.channels (fun _ ↦ J)
    (fun ab hab ↦ (PrincipalEdgeGeometry.channel_properties hab).1) C
  refine ⟨NR, hNR, ?_⟩
  intro N hN L H hband p hp hdis T hTsub hTcard hTunion hrep
  have hhost := hr N hN L hband T hTcard hrep
  exact mem_filter.mpr ⟨hp, hdis, T, mem_filter.mpr ⟨mem_powersetCard.mpr ⟨hTsub, hTcard⟩, hhost⟩, hTunion⟩

theorem uniform_bound (J : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → contribution N H L J ≤ (N : ℝ) ^ (-41 / 30 + ε) := by
  obtain ⟨NM, _hNM, hm⟩ := AlignedTripleExtensions.uniform_mass PrincipalEdgeGeometry.channels (fun _ ↦ J)
    (fun ab hab ↦ by
      obtain ⟨ha, hab', hb, hcop, _ha4, _hb4⟩ := PrincipalEdgeGeometry.channel_properties hab
      exact ⟨ha, hab', hb, hcop⟩) 1 C (ε / 2) (by positivity)
  obtain ⟨NG, _hNG, hg⟩ := PrincipalChannelEdgesPhase.uniform_geometry C
  obtain ⟨NA, ha⟩ := HalfCountSchedule.factor_absorption 36 (-41 / 30 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 10 (max NM (max NG NA)), by omega, ?_⟩
  intro N hN L H hband
  calc
    _ ≤ 36 * AlignedTripleExtensions.mass PrincipalEdgeGeometry.channels (fun _ ↦ J) 1 N L :=
      contribution_le_mass (by omega) (hg N (by omega) L hband).2
    _ ≤ 36 * (N : ℝ) ^ (-41 / 30 + ε / 2) :=
      mul_le_mul_of_nonneg_left (hm N (by omega) L hband) (by norm_num)
    _ ≤ (N : ℝ) ^ ((-41 / 30 + ε / 2) + ε / 2) := ha N (by omega)
    _ = _ := by congr 1; ring

theorem relative_to_beta_squared (J : ℕ) (C : ℝ) (D : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → 8 * (L + 1) ≤ H → H ≤ D * (L + 1) →
      contribution N H L J ≤ δ * beta N H L ^ 2 := by
  obtain ⟨c, hc, NB, _hNB, hb⟩ := PrincipalEdgeProbability.beta_squared_lower C D
  obtain ⟨NM, _hNM, hm⟩ := uniform_bound J C (1 / 60) (by norm_num)
  obtain ⟨NA, ha⟩ := HalfCountSchedule.factor_absorption (1 / (δ * c)) (-27 / 20) (1 / 60) (by norm_num)
  refine ⟨max 10 (max NB (max NM NA)), by omega, ?_⟩
  intro N hN L H hband hcut hH
  have hbeta := hb N (by omega) L H hband hcut hH
  have hfactor : (N : ℝ) ^ (-27 / 20 : ℝ) / (δ * c) ≤ (N : ℝ) ^ (-4 / 3 : ℝ) := by
    have hh := ha N (by omega)
    rw [show (-27 / 20 : ℝ) + 1 / 60 = -4 / 3 by norm_num] at hh
    simpa only [div_eq_mul_inv, one_div, mul_comm, one_mul, mul_one] using hh
  have herror : (N : ℝ) ^ (-27 / 20 : ℝ) ≤ δ * beta N H L ^ 2 := by
    have hh := (div_le_iff₀ (by positivity : (0 : ℝ) < δ * c)).mp hfactor
    have hlow := mul_le_mul_of_nonneg_left hbeta hδ.le
    nlinarith only [hh, hlow]
  have hmass := hm N (by omega) L H hband
  rw [show (-41 / 30 : ℝ) + 1 / 60 = -27 / 20 by norm_num] at hmass
  exact hmass.trans herror

end PaperP1.AlignedPrincipalEdgePairMass
