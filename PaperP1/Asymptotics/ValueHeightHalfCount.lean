module

public import PaperP1.Asymptotics.EffectiveHalfCount
public import PaperP1.Asymptotics.BlockCentreHeights
public import PaperP1.Asymptotics.LogarithmicBlockGeometry

/-! # Main 10.1 with actual value heights and arbitrary finite candidate centres

Comparable centre heights are deduced for active new blocks. Empty old
blocks can be recentered without changing their full value span.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ValueHeightHalfCount

open Finset PaperP1.EffectiveWindowLists PaperP1.BlockCentreHeights

theorem article_10_1 (r s : ℕ) (a b D Cband ε : ℝ)
    (ha : 0 < a) (hD : 0 ≤ D) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ, ∀ old : Fin s → ℕ, ∀ G : Finset ℕ,
      ∀ blocks : Fin r → ℕ → Finset ℕ, ∀ oldBlocks : Fin s → Finset ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ Cband →
      (∀ i, ∀ x ∈ G, ∀ v ∈ blocks i x, a * N ≤ v ∧ (v : ℝ) ≤ b * N) →
      (∀ k, ∀ v ∈ oldBlocks k, a * N ≤ v ∧ (v : ℝ) ≤ b * N) →
      (∀ i, ∀ x ∈ G, ∀ v ∈ blocks i x,
        (((v : ℤ) - x).natAbs : ℝ) ≤ D * (L + 1 : ℕ)) →
      (∀ k, ∀ v ∈ oldBlocks k,
        (((v : ℤ) - old k).natAbs : ℝ) ≤ D * (L + 1 : ℕ)) →
      ((PaperP1.EffectiveWindowLists.lists G blocks (univ.biUnion oldBlocks)).card : ℝ) ≤
        (N : ℝ) ^ ((r : ℝ) / 2 + ε) := by
  classical
  obtain ⟨NI, hNI⟩ := PaperP1.EffectiveHalfCount.critical_centre_count r s (lower a) (upper b) D Cband ε
    (lower_pos a ha) hD hε
  obtain ⟨NB, hNB⟩ := radius_logarithmic D Cband hD
  obtain ⟨NW, hNW⟩ := logarithmic_radius a (D * PaperP1.CriticalBandScale.upperScale + 2) ha
  refine ⟨max NI (max NB NW), ?_⟩
  intro N hN L old G blocks oldBlocks hband hvalues holdValues hdist holdDist
  let W := radius D L
  have hW := hNW N (by omega) W (hNB N (by omega) L hband)
  have hcentre : ∀ x v : ℕ, a * N ≤ v ∧ (v : ℝ) ≤ b * N →
      (((v : ℤ) - x).natAbs : ℝ) ≤ D * (L + 1 : ℕ) →
      lower a * N ≤ x ∧ (x : ℝ) ≤ upper b * N := by
    intro x v hv hvdist
    exact centre_bounds a b N W x v hv (distance_le_radius D L _ hvdist) hW.1 hW.2
  let G' := G.filter fun x : ℕ ↦ lower a * N ≤ (x : ℝ) ∧ (x : ℝ) ≤ upper b * N
  let old' := fun k : Fin s ↦ if (oldBlocks k).Nonempty then old k else N
  have hold' : ∀ k, lower a * N ≤ old' k ∧ (old' k : ℝ) ≤ upper b * N := by
    intro k
    by_cases hk : (oldBlocks k).Nonempty
    · obtain ⟨v, hv⟩ := hk
      simpa only [old', ite_eq_left (show (oldBlocks k).Nonempty from ⟨v, hv⟩)] using
        hcentre (old k) v (holdValues k v hv) (holdDist k v hv)
    · simpa only [old', ite_eq_right hk] using default_bounds a b N
  have hsub : lists G blocks (univ.biUnion oldBlocks) ⊆ lists G' blocks (univ.biUnion oldBlocks) := by
    intro n hn
    obtain ⟨hnG, hinj, u, hu, hsum⟩ := (mem_lists G blocks (univ.biUnion oldBlocks) n).mp hn
    apply (mem_lists G' blocks (univ.biUnion oldBlocks) n).mpr
    refine ⟨?_, hinj, u, hu, hsum⟩
    intro i
    obtain ⟨v, hv⟩ := effective_nonempty (blocks i (n i)) (u i) (hu i).1 (hu i).2
    exact mem_filter.mpr ⟨hnG i, hcentre (n i) v (hvalues i (n i) (hnG i) v hv)
      (hdist i (n i) (hnG i) v hv)⟩
  have hG' : ∀ x ∈ G', lower a * N ≤ x ∧ (x : ℝ) ≤ upper b * N := fun x hx ↦ (mem_filter.mp hx).2
  have hdist' : ∀ i, ∀ x ∈ G', ∀ v ∈ blocks i x,
      (((v : ℤ) - x).natAbs : ℝ) ≤ D * (L + 1 : ℕ) := fun i x hx v hv ↦ hdist i x (mem_filter.mp hx).1 v hv
  have holdDist' : ∀ k, ∀ v ∈ oldBlocks k,
      (((v : ℤ) - old' k).natAbs : ℝ) ≤ D * (L + 1 : ℕ) := by
    intro k v hv
    simpa only [old', ite_eq_left (show (oldBlocks k).Nonempty from ⟨v, hv⟩)] using holdDist k v hv
  exact (show ((lists G blocks (univ.biUnion oldBlocks)).card : ℝ) ≤
    ((lists G' blocks (univ.biUnion oldBlocks)).card : ℝ) by exact_mod_cast card_le_card hsub).trans
    (hNI N (by omega) L old' G' blocks oldBlocks hband hG' hold' hdist' holdDist')

theorem uniform_logarithmic_count (r s : ℕ) (a b E ε : ℝ)
    (ha : 0 < a) (hE : 0 ≤ E) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ old : Fin s → ℕ, ∀ G : Finset ℕ,
      ∀ blocks : Fin r → ℕ → Finset ℕ, ∀ oldBlocks : Fin s → Finset ℕ,
      (∀ i, ∀ x ∈ G, ∀ v ∈ blocks i x, a * N ≤ v ∧ (v : ℝ) ≤ b * N) →
      (∀ k, ∀ v ∈ oldBlocks k, a * N ≤ v ∧ (v : ℝ) ≤ b * N) →
      (∀ i, ∀ x ∈ G, ∀ v ∈ blocks i x, (((v : ℤ) - x).natAbs : ℝ) ≤ E * Real.log N) →
      (∀ k, ∀ v ∈ oldBlocks k, (((v : ℤ) - old k).natAbs : ℝ) ≤ E * Real.log N) →
      ((PaperP1.EffectiveWindowLists.lists G blocks (univ.biUnion oldBlocks)).card : ℝ) ≤
        (N : ℝ) ^ ((r : ℝ) / 2 + ε) := by
  obtain ⟨NI, hNI⟩ := article_10_1 r s a b (E / PaperP1.CriticalBandScale.lowerScale) 1 ε
    ha (div_nonneg hE PaperP1.CriticalBandScale.lowerScale_pos.le) hε
  obtain ⟨NT, hNT⟩ := PaperP1.LogarithmicBlockGeometry.width_transfer E hE
  refine ⟨max NI NT, ?_⟩
  intro N hN old G blocks oldBlocks hvalues holdValues hdist holdDist
  have htransfer := hNT N (by omega)
  exact hNI N (by omega) (PaperP1.LogarithmicBlockGeometry.length N) old G blocks oldBlocks
    htransfer.1 hvalues holdValues
    (fun i x hx v hv ↦ (hdist i x hx v hv).trans htransfer.2)
    (fun k v hv ↦ (holdDist k v hv).trans htransfer.2)

end PaperP1.ValueHeightHalfCount
