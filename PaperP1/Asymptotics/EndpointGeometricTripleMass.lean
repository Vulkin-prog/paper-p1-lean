module

public import PaperP1.Asymptotics.FiniteAlignedTargetTripleMass
public import PaperP1.Arithmetic.GeometricAlignedTargetData
public import PaperP1.Arithmetic.ExactMatchCongruences
public import Mathlib.Data.Finset.Powerset

/-! # A bounded geometric target of either endpoint of an exact source pair has sharp actual mass -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.EndpointGeometricTripleMass

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def Witness (F : Finset (ℕ × ℕ)) (Q L : ℕ) (T : Finset ℕ) : Prop :=
  ∃ ab ∈ F, ∃ x y z r s : ℕ, T = {x, y, z} ∧
    (NormalizedUnitCount.units ab.1 ab.2 x y L).Nonempty ∧
    0 < r ∧ r ≤ Q ∧ 0 < s ∧ s ≤ Q ∧
    (EnlargedPairGeometry.Geometric r s x z L ∨ EnlargedPairGeometry.Geometric r s y z L)

def hosts (F : Finset (ℕ × ℕ)) (Q N L : ℕ) : Finset (Finset ℕ) :=
  ((dyadicBlock N).powersetCard 3).filter (Witness F Q L)

def mass (F : Finset (ℕ × ℕ)) (Q N L : ℕ) : ℝ :=
  ∑ T ∈ hosts F Q N L, infiniteJointMoment L T

theorem host_data {F : Finset (ℕ × ℕ)} {Q N L : ℕ} {T : Finset ℕ} (hT : T ∈ hosts F Q N L) :
    T ⊆ dyadicBlock N ∧ T.card = 3 ∧ Witness F Q L T := by
  obtain ⟨hp, hw⟩ := mem_filter.mp hT
  exact ⟨(mem_powersetCard.mp hp).1, (mem_powersetCard.mp hp).2, hw⟩

theorem source_mem_hosts {F : Finset (ℕ × ℕ)} {Q N L : ℕ} {T : Finset ℕ}
    (hsub : T ⊆ dyadicBlock N) (hcard : T.card = 3) (hw : Witness F Q L T) : T ∈ hosts F Q N L :=
  mem_filter.mpr ⟨mem_powersetCard.mpr ⟨hsub, hcard⟩, hw⟩

theorem uniform_inclusion (F : Finset (ℕ × ℕ)) (Q : ℕ)
    (hF : ∀ ab ∈ F, 0 < ab.1 ∧ 0 < ab.2 ∧ ab.1.Coprime ab.2) (C : ℝ) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      hosts F Q N L ⊆ FiniteAlignedTargetTripleMass.hosts F (fun _ ↦ 2) N L := by
  obtain ⟨NR, _hNR, hu⟩ := FiniteAlignedTargetTripleMass.all_actual_sources F (fun _ ↦ 2)
    (fun ab hab ↦ (hF ab hab).1) C
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C (3 * Q)
  refine ⟨max 10 (max NR NG), by omega, ?_⟩
  intro N hN L hband T hT
  obtain ⟨hsub, hcard, ab, hab, x, y, z, r, s, hfamily, hunit, hr, hrQ, hs, hsQ, htarget⟩ := host_data hT
  have hx : x ∈ dyadicBlock N := hsub (by rw [hfamily]; simp)
  have hy : y ∈ dyadicBlock N := hsub (by rw [hfamily]; simp)
  have hz : z ∈ dyadicBlock N := hsub (by rw [hfamily]; simp)
  obtain ⟨ha, hb, hcop⟩ := hF ab hab
  obtain ⟨ij, hij⟩ := hunit
  obtain ⟨t, _ht, hbaseX, hbaseY⟩ := ExactMatchCongruences.source_parameter ha hcop
    (by have := (mem_Ico.mp hx).1; omega : 2 ≤ x) ij.1 ij.2 (NormalizedUnitCount.mem_units.mp hij)
  have hB := (hg N (by omega) L hband).2.1
  have hdata : ∃ c d : ℕ, ∃ h : ℤ, 0 < c ∧ 0 < d ∧ c.Coprime d ∧ d ≤ (L + 1) ^ 2 ∧
      |h| ≤ ((L + 1) ^ 2 : ℕ) ∧ (d : ℤ) * z = (c : ℤ) * t + h := by
    rcases htarget with hxz | hyz
    · exact GeometricAlignedTargetData.bounded_height ha hr hs hrQ hsQ hB
        (by have := (mem_Ico.mp hx).1; omega : 0 < x) hxz ij.1 hbaseX
    · exact GeometricAlignedTargetData.bounded_height hb hr hs hrQ hsQ hB
        (by have := (mem_Ico.mp hy).1; omega : 0 < y) hyz ij.2 hbaseY
  obtain ⟨c, d, h, hc, hd, hcd, hdH, hh, heq⟩ := hdata
  let rep : AllAlignedTargetTripleMass.Representation N L ab.1 ab.2 2 T :=
    ⟨x, y, z, t, c, d, ij.1, ij.2, h, hfamily, hx, hy, hz, hc, hd, hcd, hdH, hh, hbaseX, hbaseY, heq⟩
  exact hu N (by omega) L hband T hcard ⟨ab, hab, ⟨rep⟩⟩

theorem uniform_mass (F : Finset (ℕ × ℕ)) (Q : ℕ)
    (hF : ∀ ab ∈ F, 0 < ab.1 ∧ ab.1 < ab.2 ∧ ab.2 < 2 * ab.1 ∧ ab.1.Coprime ab.2)
    (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → mass F Q N L ≤ (N : ℝ) ^ (-41 / 30 + ε) := by
  obtain ⟨NI, _hNI, hi⟩ := uniform_inclusion F Q (fun ab hab ↦
    ⟨(hF ab hab).1, (hF ab hab).1.trans (hF ab hab).2.1, (hF ab hab).2.2.2⟩) C
  obtain ⟨NM, _hNM, hm⟩ := FiniteAlignedTargetTripleMass.uniform_mass F (fun _ ↦ 2) hF C ε hε
  refine ⟨max 10 (max NI NM), by omega, ?_⟩
  intro N hN L hband
  exact (sum_le_sum_of_subset_of_nonneg (hi N (by omega) L hband)
    (fun T _ _ ↦ infiniteJointMoment_nonneg L T)).trans (hm N (by omega) L hband)

end PaperP1.EndpointGeometricTripleMass
