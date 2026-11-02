module

public import PaperP1.Arithmetic.GeometricAlignedTargetData
public import PaperP1.Asymptotics.EnlargedFiniteAlignedTargetTripleMass
public import Mathlib.Data.Finset.Powerset

/-! # Actual triples in two geometric rational channels need no affine representation premise -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GeometricAlignedTripleMass

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def Witness (F : Finset (ℕ × ℕ)) (Q L : ℕ) (T : Finset ℕ) : Prop :=
  ∃ ab ∈ F, ∃ x y z r s : ℕ, T = {x, y, z} ∧ 0 < r ∧ r ≤ Q ∧ 0 < s ∧ s ≤ Q ∧
    EnlargedPairGeometry.Geometric ab.1 ab.2 x y L ∧ EnlargedPairGeometry.Geometric r s x z L

def hosts (F : Finset (ℕ × ℕ)) (Q N L : ℕ) : Finset (Finset ℕ) :=
  ((dyadicBlock N).powersetCard 3).filter (Witness F Q L)

def mass (F : Finset (ℕ × ℕ)) (Q N L : ℕ) : ℝ :=
  ∑ T ∈ hosts F Q N L, infiniteJointMoment L T

theorem host_data {F : Finset (ℕ × ℕ)} {Q N L : ℕ} {T : Finset ℕ} (hT : T ∈ hosts F Q N L) :
    T ⊆ dyadicBlock N ∧ T.card = 3 ∧ Witness F Q L T := by
  obtain ⟨hp, hw⟩ := mem_filter.mp hT
  exact ⟨(mem_powersetCard.mp hp).1, (mem_powersetCard.mp hp).2, hw⟩

theorem source_mem_hosts {F : Finset (ℕ × ℕ)} {Q N L a b x y z r s : ℕ}
    (hab : (a, b) ∈ F) (hcard : ({x, y, z} : Finset ℕ).card = 3)
    (hx : x ∈ dyadicBlock N) (hy : y ∈ dyadicBlock N) (hz : z ∈ dyadicBlock N)
    (hr : 0 < r) (hrQ : r ≤ Q) (hs : 0 < s) (hsQ : s ≤ Q)
    (hsource : EnlargedPairGeometry.Geometric a b x y L)
    (htarget : EnlargedPairGeometry.Geometric r s x z L) : {x, y, z} ∈ hosts F Q N L := by
  apply mem_filter.mpr
  refine ⟨mem_powersetCard.mpr ⟨?_, hcard⟩, (a, b), hab, x, y, z, r, s, rfl, hr, hrQ, hs, hsQ, hsource, htarget⟩
  exact insert_subset_iff.mpr ⟨hx, insert_subset_iff.mpr ⟨hy, singleton_subset_iff.mpr hz⟩⟩

theorem uniform_inclusion (F : Finset (ℕ × ℕ)) (Q : ℕ) (hF : ∀ ab ∈ F, 0 < ab.1) (C : ℝ) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      hosts F Q N L ⊆ EnlargedFiniteAlignedTargetTripleMass.hosts F (fun _ ↦ 2) N L := by
  obtain ⟨NR, _hNR, hu⟩ := EnlargedFiniteAlignedTargetTripleMass.all_actual_sources F (fun _ ↦ 2) hF C
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C (max (3 * Q) (F.sup Prod.fst + 1))
  refine ⟨max 10 (max NR NG), by omega, ?_⟩
  intro N hN L hband T hT
  obtain ⟨hsub, hcard, ab, hab, x, y, z, r, s, hfamily, hr, hrQ, hs, hsQ, hsource, htarget⟩ := host_data hT
  have hx : x ∈ dyadicBlock N := hsub (by rw [hfamily]; simp)
  have hy : y ∈ dyadicBlock N := hsub (by rw [hfamily]; simp)
  have hz : z ∈ dyadicBlock N := hsub (by rw [hfamily]; simp)
  have hBmin := (hg N (by omega) L hband).2.1
  have hsup : ab.1 ≤ F.sup Prod.fst := Finset.le_sup hab
  have haB : ab.1 < L + 1 := by omega
  obtain ⟨t, i, hbase⟩ := EnlargedSourceTargetGeometry.exists_source_vertex (hF ab hab)
    (by have := (mem_Ico.mp hx).1; omega : 0 < x) haB
  obtain ⟨c, d, h, hc, hd, hcd, hdH, hh, heq⟩ := GeometricAlignedTargetData.bounded_height
    (hF ab hab) hr hs hrQ hsQ (by omega : 3 * Q ≤ L + 1)
    (by have := (mem_Ico.mp hx).1; omega : 0 < x) htarget i hbase
  let rep : EnlargedAllAlignedTargetTripleMass.Representation N L ab.1 ab.2 2 T :=
    ⟨x, y, z, t, c, d, i, h, hfamily, hx, hy, hz, hc, hd, hcd, hdH, hh, hbase, hsource, heq⟩
  exact hu N (by omega) L hband T hcard ⟨ab, hab, ⟨rep⟩⟩

theorem uniform_mass (F : Finset (ℕ × ℕ)) (Q : ℕ)
    (hF : ∀ ab ∈ F, 0 < ab.1 ∧ ab.1 < ab.2 ∧ ab.2 < 2 * ab.1 ∧ ab.1.Coprime ab.2)
    (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → mass F Q N L ≤ (N : ℝ) ^ (-41 / 30 + ε) := by
  obtain ⟨NI, _hNI, hi⟩ := uniform_inclusion F Q (fun ab hab ↦ (hF ab hab).1) C
  obtain ⟨NM, _hNM, hm⟩ := EnlargedFiniteAlignedTargetTripleMass.uniform_mass F (fun _ ↦ 2) hF C ε hε
  refine ⟨max 10 (max NI NM), by omega, ?_⟩
  intro N hN L hband
  exact (sum_le_sum_of_subset_of_nonneg (hi N (by omega) L hband)
    (fun T _ _ ↦ infiniteJointMoment_nonneg L T)).trans (hm N (by omega) L hband)

theorem uniform_polynomial_inclusion (F : Finset (ℕ × ℕ)) (K : ℕ) (hF : ∀ ab ∈ F, 0 < ab.1) (C : ℝ) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      hosts F ((L + 1) ^ K) N L ⊆ EnlargedFiniteAlignedTargetTripleMass.hosts F (fun _ ↦ K + 2) N L := by
  obtain ⟨NR, _hNR, hu⟩ := EnlargedFiniteAlignedTargetTripleMass.all_actual_sources F (fun _ ↦ K + 2) hF C
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C (max 3 (F.sup Prod.fst + 1))
  refine ⟨max 10 (max NR NG), by omega, ?_⟩
  intro N hN L hband T hT
  obtain ⟨hsub, hcard, ab, hab, x, y, z, r, s, hfamily, hr, hrQ, hs, hsQ, hsource, htarget⟩ := host_data hT
  have hx : x ∈ dyadicBlock N := hsub (by rw [hfamily]; simp)
  have hy : y ∈ dyadicBlock N := hsub (by rw [hfamily]; simp)
  have hz : z ∈ dyadicBlock N := hsub (by rw [hfamily]; simp)
  have hBmin := (hg N (by omega) L hband).2.1
  have hsup : ab.1 ≤ F.sup Prod.fst := Finset.le_sup hab
  have haB : ab.1 < L + 1 := by omega
  obtain ⟨t, i, hbase⟩ := EnlargedSourceTargetGeometry.exists_source_vertex (hF ab hab)
    (by have := (mem_Ico.mp hx).1; omega : 0 < x) haB
  obtain ⟨c, d, h, hc, hd, hcd, hdH, hh, heq⟩ := GeometricAlignedTargetData.bounded_polynomial_height
    (hF ab hab) hr hs hrQ hsQ (by omega : 3 ≤ L + 1)
    (by have := (mem_Ico.mp hx).1; omega : 0 < x) htarget i hbase
  let rep : EnlargedAllAlignedTargetTripleMass.Representation N L ab.1 ab.2 (K + 2) T :=
    ⟨x, y, z, t, c, d, i, h, hfamily, hx, hy, hz, hc, hd, hcd, hdH, hh, hbase, hsource, heq⟩
  exact hu N (by omega) L hband T hcard ⟨ab, hab, ⟨rep⟩⟩

theorem uniform_polynomial_mass (F : Finset (ℕ × ℕ)) (K : ℕ)
    (hF : ∀ ab ∈ F, 0 < ab.1 ∧ ab.1 < ab.2 ∧ ab.2 < 2 * ab.1 ∧ ab.1.Coprime ab.2)
    (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → mass F ((L + 1) ^ K) N L ≤ (N : ℝ) ^ (-41 / 30 + ε) := by
  obtain ⟨NI, _hNI, hi⟩ := uniform_polynomial_inclusion F K (fun ab hab ↦ (hF ab hab).1) C
  obtain ⟨NM, _hNM, hm⟩ := EnlargedFiniteAlignedTargetTripleMass.uniform_mass F (fun _ ↦ K + 2) hF C ε hε
  refine ⟨max 10 (max NI NM), by omega, ?_⟩
  intro N hN L hband
  exact (sum_le_sum_of_subset_of_nonneg (hi N (by omega) L hband)
    (fun T _ _ ↦ infiniteJointMoment_nonneg L T)).trans (hm N (by omega) L hband)

end PaperP1.GeometricAlignedTripleMass
