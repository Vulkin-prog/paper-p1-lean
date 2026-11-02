module

public import PaperP1.Arithmetic.CompressedTargetAlignment
public import PaperP1.Asymptotics.EnlargedFiniteAlignedTargetTripleMass
public import Mathlib.Data.Finset.Powerset

/-! # Every geometrically aligned compressed target above a fixed finite source family -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CompressedAlignedTripleMass

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def Witness (F : Finset (ℕ × ℕ)) (D L : ℕ) (T : Finset ℕ) : Prop :=
  ∃ ab ∈ F, ∃ x y z t : ℕ, ∃ i : Fin (L + 1), T = {x, y, z} ∧
    startCompleteVertexLabel x L i = ab.1 * t ∧ EnlargedPairGeometry.Geometric ab.1 ab.2 x y L ∧
    CompressedTargetAlignment.Aligned D (ab.1 * ab.2 * t) z L

def hosts (F : Finset (ℕ × ℕ)) (D N L : ℕ) : Finset (Finset ℕ) :=
  ((dyadicBlock N).powersetCard 3).filter (Witness F D L)

def mass (F : Finset (ℕ × ℕ)) (D N L : ℕ) : ℝ :=
  ∑ T ∈ hosts F D N L, infiniteJointMoment L T

theorem host_data {F : Finset (ℕ × ℕ)} {D N L : ℕ} {T : Finset ℕ} (hT : T ∈ hosts F D N L) :
    T ⊆ dyadicBlock N ∧ T.card = 3 ∧ Witness F D L T := by
  obtain ⟨hp, hw⟩ := mem_filter.mp hT
  exact ⟨(mem_powersetCard.mp hp).1, (mem_powersetCard.mp hp).2, hw⟩

theorem source_mem_hosts {F : Finset (ℕ × ℕ)} {D N L a b x y z t : ℕ}
    (hab : (a, b) ∈ F) (hcard : ({x, y, z} : Finset ℕ).card = 3)
    (hx : x ∈ dyadicBlock N) (hy : y ∈ dyadicBlock N) (hz : z ∈ dyadicBlock N)
    (i : Fin (L + 1)) (hbase : startCompleteVertexLabel x L i = a * t)
    (hsource : EnlargedPairGeometry.Geometric a b x y L)
    (htarget : CompressedTargetAlignment.Aligned D (a * b * t) z L) : {x, y, z} ∈ hosts F D N L := by
  apply mem_filter.mpr
  refine ⟨mem_powersetCard.mpr ⟨?_, hcard⟩, (a, b), hab, x, y, z, t, i, rfl, hbase, hsource, htarget⟩
  exact insert_subset_iff.mpr ⟨hx, insert_subset_iff.mpr ⟨hy, singleton_subset_iff.mpr hz⟩⟩

theorem uniform_inclusion (F : Finset (ℕ × ℕ)) (D : ℕ)
    (hF : ∀ ab ∈ F, 0 < ab.1 ∧ 0 < ab.2) (C : ℝ) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      hosts F D N L ⊆ EnlargedFiniteAlignedTargetTripleMass.hosts F (fun _ ↦ 5) N L := by
  obtain ⟨NR, _hNR, hu⟩ := EnlargedFiniteAlignedTargetTripleMass.all_actual_sources F (fun _ ↦ 5)
    (fun ab hab ↦ (hF ab hab).1) C
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C (2 * D)
  refine ⟨max 10 (max NR NG), by omega, ?_⟩
  intro N hN L hband T hT
  obtain ⟨hsub, hcard, ab, hab, x, y, z, t, i, hfamily, hbase, hsource, htarget⟩ := host_data hT
  have hx : x ∈ dyadicBlock N := hsub (by rw [hfamily]; simp)
  have hy : y ∈ dyadicBlock N := hsub (by rw [hfamily]; simp)
  have hz : z ∈ dyadicBlock N := hsub (by rw [hfamily]; simp)
  obtain ⟨c, d, h, hc, hd, hcd, hdH, hh, heq⟩ := CompressedTargetAlignment.bounded_data
    (hF ab hab).1 (hF ab hab).2 (hg N (by omega) L hband).2.1 htarget
  let rep : EnlargedAllAlignedTargetTripleMass.Representation N L ab.1 ab.2 5 T :=
    ⟨x, y, z, t, c, d, i, h, hfamily, hx, hy, hz, hc, hd, hcd, hdH, hh, hbase, hsource, heq⟩
  exact hu N (by omega) L hband T hcard ⟨ab, hab, ⟨rep⟩⟩

theorem uniform_mass (F : Finset (ℕ × ℕ)) (D : ℕ)
    (hF : ∀ ab ∈ F, 0 < ab.1 ∧ ab.1 < ab.2 ∧ ab.2 < 2 * ab.1 ∧ ab.1.Coprime ab.2)
    (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → mass F D N L ≤ (N : ℝ) ^ (-41 / 30 + ε) := by
  obtain ⟨NI, _hNI, hi⟩ := uniform_inclusion F D (fun ab hab ↦
    ⟨(hF ab hab).1, (hF ab hab).1.trans (hF ab hab).2.1⟩) C
  obtain ⟨NM, _hNM, hm⟩ := EnlargedFiniteAlignedTargetTripleMass.uniform_mass F (fun _ ↦ 5) hF C ε hε
  refine ⟨max 10 (max NI NM), by omega, ?_⟩
  intro N hN L hband
  exact (sum_le_sum_of_subset_of_nonneg (hi N (by omega) L hband)
    (fun T _ _ ↦ infiniteJointMoment_nonneg L T)).trans (hm N (by omega) L hband)

end PaperP1.CompressedAlignedTripleMass
