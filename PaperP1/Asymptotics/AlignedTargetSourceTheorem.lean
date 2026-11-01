module

public import PaperP1.Asymptotics.AlignedTargetRank
public import PaperP1.Arithmetic.GoodEdgeCompression
public import PaperP1.Model.CompatibleWindowOverlap

/-! # Actual source families, both orientations and compatible targets for T1.11/T2.6 -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AlignedTargetSourceTheorem

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.NormalizedUnitCount PaperP1.AlignedTargetRank PaperP1.TargetWindowRank PaperP1.FixedChannelGamma

def represented (a b x y L t : ℕ) : Prop :=
  (∃ i j : Fin (L + 1), startCompleteVertexLabel x L i = a * t ∧ startCompleteVertexLabel y L j = b * t) ∨
  (∃ i j : Fin (L + 1), startCompleteVertexLabel y L i = a * t ∧ startCompleteVertexLabel x L j = b * t)

def sourceUnits (a b x y L : ℕ) : Prop := (units a b x y L).Nonempty ∨ (units a b y x L).Nonempty

def symmetricEndpointSources (N a b L : ℕ) : Finset (ℕ × ℕ) :=
  endpointSources N a b L ∪ (endpointSources N a b L).image Prod.swap

def SourceConclusion (D N a b L : ℕ) (ε : ℝ) : Prop :=
  (symmetricEndpointSources N a b L).card ≤ (12 * (a + b) + 4) * (L + 1) ^ 7 ∧
  ∀ x y : ℕ, x ∈ dyadicBlock N → y ∈ dyadicBlock N → sourceUnits a b x y L →
    ∃ t : ℕ, 0 < t ∧ represented a b x y L t ∧ (targets D N a b t L).card ≤ 6 * a * (L + 1) ^ 15 ∧
      ∀ z ∈ targets D N a b t L,
        (x + L ≤ z ∨ z + L ≤ x) → (y + L ≤ z ∨ z + L ≤ y) →
        (x, y) ∉ symmetricEndpointSources N a b L →
        ∀ Q : Finset ℕ, Q ⊆ (a * b).primeFactors →
          (deficiency Q x y z L : ℝ) ≤ (gammaReal a b + ε) * L

def CompatibleConclusion (D N a b L : ℕ) (ε : ℝ) : Prop :=
  (symmetricEndpointSources N a b L).card ≤ (12 * (a + b) + 4) * (L + 1) ^ 7 ∧
  ∀ x y : ℕ, x ∈ dyadicBlock N → y ∈ dyadicBlock N → sourceUnits a b x y L →
    ∃ t : ℕ, 0 < t ∧ represented a b x y L t ∧ (targets D N a b t L).card ≤ 6 * a * (L + 1) ^ 15 ∧
      ∀ z ∈ targets D N a b t L, z ≠ x → z ≠ y → 0 < infiniteJointMoment L {x, y, z} →
        (x, y) ∉ symmetricEndpointSources N a b L →
        ∀ Q : Finset ℕ, Q ⊆ (a * b).primeFactors →
          (deficiency Q x y z L : ℝ) ≤ (gammaReal a b + ε) * L

theorem source_representation {a b x y L : ℕ} (ha : 0 < a) (hab : a.Coprime b)
    (hx : 2 ≤ x) (hunits : (units a b x y L).Nonempty) :
    ∃ t : ℕ, ∃ i j : Fin (L + 1), 0 < t ∧ startCompleteVertexLabel x L i = a * t ∧
      startCompleteVertexLabel y L j = b * t := by
  obtain ⟨u, hu⟩ := hunits
  obtain ⟨t, ht, hX, hY⟩ := ExactMatchCongruences.source_parameter ha hab hx u.1 u.2 (mem_units.mp hu)
  exact ⟨t, u.1, u.2, ht, hX, hY⟩

theorem symmetric_endpoint_card {N a b L : ℕ}
    (hcard : (endpointSources N a b L).card ≤ (6 * (a + b) + 2) * (L + 1) ^ 7) :
    (symmetricEndpointSources N a b L).card ≤ (12 * (a + b) + 4) * (L + 1) ^ 7 := by
  have hunion := card_union_le (endpointSources N a b L) ((endpointSources N a b L).image Prod.swap)
  have himage : ((endpointSources N a b L).image Prod.swap).card ≤ (endpointSources N a b L).card := card_image_le
  change (endpointSources N a b L ∪ (endpointSources N a b L).image Prod.swap).card ≤ _
  nlinarith only [hunion, himage, hcard]

theorem uniform_source_bounds (C ε : ℝ) (hε : 0 < ε) {a b : ℕ} (ha : 0 < a) (hb : 3 ≤ b)
    (hab : a.Coprime b) (horder : a < b) (D : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → SourceConclusion D N a b L ε := by
  obtain ⟨Ncore, hcore⟩ := AlignedTargetRank.uniform_core C ε hε ha hb hab horder D
  refine ⟨max Ncore 2, ?_⟩
  intro N hN L hcrit
  have hNtwo : 2 ≤ N := (le_max_right _ _).trans hN
  have h := hcore N ((le_max_left _ _).trans hN) L hcrit
  refine ⟨symmetric_endpoint_card h.1, ?_⟩
  intro x y hx hy hunits
  have hx2 : 2 ≤ x := hNtwo.trans (mem_Ico.mp hx).1
  have hy2 : 2 ≤ y := hNtwo.trans (mem_Ico.mp hy).1
  rcases hunits with hunits | hunits
  · obtain ⟨t, i, j, ht, hX, hY⟩ := source_representation ha hab hx2 hunits
    have hpair := h.2 x y t hx hy i j hX hY
    refine ⟨t, ht, Or.inl ⟨i, j, hX, hY⟩, hpair.1, ?_⟩
    intro z hz hsepX hsepY haway Q hQ
    have haway' : (x, y) ∉ endpointSources N a b L :=
      fun he ↦ haway (mem_union.mpr (Or.inl he))
    exact hpair.2 z hz hsepX hsepY haway' Q hQ
  · obtain ⟨t, i, j, ht, hY, hX⟩ := source_representation ha hab hy2 hunits
    have hpair := h.2 y x t hy hx i j hY hX
    refine ⟨t, ht, Or.inr ⟨i, j, hY, hX⟩, hpair.1, ?_⟩
    intro z hz hsepX hsepY haway Q hQ
    have haway' : (y, x) ∉ endpointSources N a b L := by
      intro he
      exact haway (mem_union.mpr (Or.inr (mem_image.mpr ⟨(y, x), he, rfl⟩)))
    rw [deficiency_comm Q x y z L]
    exact hpair.2 z hz hsepY hsepX haway' Q hQ

theorem compatible_of_source {D N a b L : ℕ} {ε : ℝ} (hL : 0 < L)
    (hsource : SourceConclusion D N a b L ε) : CompatibleConclusion D N a b L ε := by
  refine ⟨hsource.1, ?_⟩
  intro x y hx hy hunits
  obtain ⟨t, ht, hrep, hcount, hbound⟩ := hsource.2 x y hx hy hunits
  refine ⟨t, ht, hrep, hcount, ?_⟩
  intro z hz hzx hzy hq haway Q hQ
  obtain ⟨hqx, hqy⟩ := CompatibleWindowOverlap.triple_joint_pairs hq
  have hsepX := CompatibleWindowOverlap.compatible_pair_separated hzx.symm hL hqx
  have hsepY := CompatibleWindowOverlap.compatible_pair_separated hzy.symm hL hqy
  exact hbound z hz hsepX hsepY haway Q hQ

theorem uniform_both (C ε : ℝ) (hε : 0 < ε) {a b : ℕ} (ha : 0 < a) (hb : 3 ≤ b)
    (hab : a.Coprime b) (horder : a < b) (D : ℕ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      SourceConclusion D N a b L ε ∧ CompatibleConclusion D N a b L ε := by
  obtain ⟨Ncore, hcore⟩ := uniform_source_bounds C ε hε ha hb hab horder D
  obtain ⟨Ngeom, hgeom⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨max Ncore Ngeom, ?_⟩
  intro N hN L hcrit
  have hsource := hcore N ((le_max_left _ _).trans hN) L hcrit
  have hB := (hgeom N ((le_max_right _ _).trans hN) L hcrit).2.1
  exact ⟨hsource, compatible_of_source (by omega) hsource⟩

theorem geometric_good_source_units {H : ℝ} {N L a b x y : ℕ} (hN : 2 ≤ N)
    (ha : 0 < a) (hb : 0 < b) (hx : x ∈ dyadicBlock N) (hy : y ∈ dyadicBlock N)
    (hprivate : GoodEdgeCompression.PrivateAbove H (NormalizedWindowSets.union a b x y L))
    (hdep : ¬Disjoint (squareClassSpace x L) (squareClassSpace y L)) :
    sourceUnits a b x y L := by
  have htwo := CompressionRank.dependent_two_units ha hb (hN.trans (mem_Ico.mp hx).1)
    (hN.trans (mem_Ico.mp hy).1) hprivate.private hdep
  exact Or.inl (card_pos.mp (by omega))

theorem companion_T2_6 {a b : ℕ} (ha : 0 < a) (hb : 3 ≤ b) (hab : a.Coprime b) (horder : a < b) :
    gammaReal a b ≤ 2 / 3 ∧
    ∀ C ε : ℝ, 0 < ε → ∀ D : ℕ, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      SourceConclusion D N a b L ε ∧ CompatibleConclusion D N a b L ε :=
  ⟨gammaReal_le_two_thirds hab hb, fun C ε hε D ↦ uniform_both C ε hε ha hb hab horder D⟩

theorem companion_T1_11 :
    gammaReal 2 3 = 1 / 3 ∧ gammaReal 3 4 = 1 / 2 ∧
    ∀ C ε : ℝ, 0 < ε → ∀ D : ℕ, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      SourceConclusion D N 2 3 L ε ∧ SourceConclusion D N 3 4 L ε := by
  refine ⟨gammaReal_two_three, gammaReal_three_four, ?_⟩
  intro C ε hε D
  obtain ⟨N23, h23⟩ := uniform_source_bounds C ε hε (a := 2) (b := 3) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) D
  obtain ⟨N34, h34⟩ := uniform_source_bounds C ε hε (a := 3) (b := 4) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) D
  exact ⟨max N23 N34, fun N hN L hcrit ↦
    ⟨h23 N ((le_max_left _ _).trans hN) L hcrit, h34 N ((le_max_right _ _).trans hN) L hcrit⟩⟩

end PaperP1.AlignedTargetSourceTheorem
