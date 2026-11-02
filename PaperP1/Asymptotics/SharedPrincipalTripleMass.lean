module

public import PaperP1.Model.SharedPrincipalTriples
public import PaperP1.Asymptotics.EndpointGeometricTripleMass
public import PaperP1.Asymptotics.PrincipalChannelEdgesPhase

/-! # Triples containing two principal good edges are negligible compared with the actual beta squared -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SharedPrincipalTripleMass

open Finset PaperP1.Model.InfiniteStarts PaperP1.SharedPrincipalTriples PaperP1.PrincipalChannelEdges

theorem inclusion {N H L : ℕ} (hN : 2 ≤ N) (hlarge : 29 * (L + 1) < N) :
    families N H L ⊆ EndpointGeometricTripleMass.hosts PrincipalEdgeGeometry.channels 4 N L := by
  intro T hT
  obtain ⟨hsub, hcard, _htwo⟩ := family_data hT
  obtain ⟨a, b, x, y, z, r, s, hab, hfamily, hu, hr, hr4, hs, hs4, htarget⟩ := source_data hN hlarge hT
  exact EndpointGeometricTripleMass.source_mem_hosts hsub hcard
    ⟨(a, b), hab, x, y, z, r, s, hfamily, hu, hr, hr4, hs, hs4, htarget⟩

theorem uniform_mass (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → mass N H L ≤ (N : ℝ) ^ (-41 / 30 + ε) := by
  have hchannels (ab : ℕ × ℕ) (hab : ab ∈ PrincipalEdgeGeometry.channels) :
      0 < ab.1 ∧ ab.1 < ab.2 ∧ ab.2 < 2 * ab.1 ∧ ab.1.Coprime ab.2 := by
    obtain ⟨ha, horder, hinterior, hcop, _ha4, _hb4⟩ := PrincipalEdgeGeometry.channel_properties hab
    exact ⟨ha, horder, hinterior, hcop⟩
  obtain ⟨NM, _hNM, hm⟩ := EndpointGeometricTripleMass.uniform_mass PrincipalEdgeGeometry.channels 4 hchannels C ε hε
  obtain ⟨NG, _hNG, hg⟩ := PrincipalChannelEdgesPhase.uniform_geometry C
  refine ⟨max 10 (max NM NG), by omega, ?_⟩
  intro N hN L H hband
  exact (sum_le_sum_of_subset_of_nonneg (inclusion (H := H) (by omega) (hg N (by omega) L hband).2)
    (fun T _ _ ↦ infiniteJointMoment_nonneg L T)).trans (hm N (by omega) L hband)

theorem relative_to_beta_squared (C : ℝ) (D : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → 8 * (L + 1) ≤ H → H ≤ D * (L + 1) →
      mass N H L ≤ δ * beta N H L ^ 2 := by
  obtain ⟨c, _k, hc, _hk, NB, _hNB, hb⟩ := PrincipalChannelEdgesPhase.positive_phase C D
  obtain ⟨NM, _hNM, hm⟩ := uniform_mass C (1 / 60) (by norm_num)
  obtain ⟨NG, _hNG, hg⟩ := PrincipalChannelEdgesPhase.uniform_geometry C
  obtain ⟨NA, ha⟩ := HalfCountSchedule.factor_absorption (1 / (δ * c ^ 2)) (-27 / 20) (1 / 60) (by norm_num)
  refine ⟨max 10 (max NB (max NM (max NG NA))), by omega, ?_⟩
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
  have hsq := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ c * (N : ℝ) ^ (-2 / 3 : ℝ)) hbase 2
  rw [mul_pow, hpow2] at hsq
  have hfactor : (N : ℝ) ^ (-27 / 20 : ℝ) / (δ * c ^ 2) ≤ (N : ℝ) ^ (-4 / 3 : ℝ) := by
    have hh := ha N (by omega)
    rw [show (-27 / 20 : ℝ) + 1 / 60 = -4 / 3 by norm_num] at hh
    simpa only [div_eq_mul_inv, one_div, mul_comm, mul_one, one_mul] using hh
  have hmass := hm N (by omega) L H hband
  rw [show (-41 / 30 : ℝ) + 1 / 60 = -27 / 20 by norm_num] at hmass
  calc
    mass N H L ≤ (N : ℝ) ^ (-27 / 20 : ℝ) := hmass
    _ ≤ δ * (c ^ 2 * (N : ℝ) ^ (-4 / 3 : ℝ)) := by
      have hh := (div_le_iff₀ (by positivity : (0 : ℝ) < δ * c ^ 2)).mp hfactor
      nlinarith only [hh]
    _ ≤ _ := mul_le_mul_of_nonneg_left hsq hδ.le

end PaperP1.SharedPrincipalTripleMass
