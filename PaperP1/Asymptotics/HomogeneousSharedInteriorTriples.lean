module

public import PaperP1.Model.FiniteInteriorUnitEdges
public import PaperP1.Arithmetic.GeometricAlignedTargetData
public import PaperP1.Asymptotics.HomogeneousEnlargedTripleMass

/-! # Separated homogeneous triples with two actual bounded interior unit edges -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HomogeneousSharedInteriorTriples

open Finset PaperP1.Model PaperP1.Arithmetic PaperP1.FiniteInteriorUnitEdges

local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem uniform_mass (Q : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ P : Finset (Finset ℕ),
      (∀ T ∈ P, T ⊆ dyadicBlock N ∧ T.card = 3 ∧ SeparatedHomogeneousMass.Separated L T ∧
        2 ≤ ((edges N L Q).filter fun e ↦ e ⊆ T).card) →
      (∑ T ∈ P, HomogeneousRunMass.probability L T) ≤ (N : ℝ) ^ (-41 / 30 + ε) := by
  obtain ⟨NR, _hNR, hu⟩ := EnlargedFiniteAlignedTargetTripleMass.all_actual_sources (channels Q) (fun _ ↦ 2)
    (fun ab hab ↦ (channel_data hab).1) C
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C (3 * Q)
  obtain ⟨NM, _hNM, hm⟩ := HomogeneousEnlargedTripleMass.finite_uniform_mass (channels Q) (fun _ ↦ 2)
    (fun ab hab ↦ ⟨(channel_data hab).1, (channel_data hab).2.1,
      (channel_data hab).2.2.1, (channel_data hab).2.2.2.1⟩) C ε hε
  refine ⟨max 10 (max NR (max NG NM)), by omega, ?_⟩
  intro N hN L hcrit P hP
  have hsub : P ⊆ (EnlargedFiniteAlignedTargetTripleMass.hosts (channels Q) (fun _ ↦ 2) N L).filter
      (SeparatedHomogeneousMass.Separated L) := by
    intro T hT
    obtain ⟨hTG, hcard, hsep, htwo⟩ := hP T hT
    obtain ⟨a, b, x, y, z, r, s, hab, hfamily, hunit, hr, hrQ, hs, hsQ, htarget⟩ :=
      triple_source (by omega : 0 < N) hcard htwo
    have hx : x ∈ dyadicBlock N := hTG (by rw [hfamily]; simp)
    have hy : y ∈ dyadicBlock N := hTG (by rw [hfamily]; simp)
    have hz : z ∈ dyadicBlock N := hTG (by rw [hfamily]; simp)
    obtain ⟨ha, horder, _hinterior, hcop, _haQ, _hbQ⟩ := channel_data hab
    obtain ⟨ij, hij⟩ := hunit
    obtain ⟨t, _ht, hbaseX, hbaseY⟩ := ExactMatchCongruences.source_parameter ha hcop
      (by have := (mem_Ico.mp hx).1; omega : 2 ≤ x) ij.1 ij.2 (NormalizedUnitCount.mem_units.mp hij)
    have hB := (hg N (by omega) L hcrit).2.1
    have hdata : ∃ c d : ℕ, ∃ h : ℤ, 0 < c ∧ 0 < d ∧ c.Coprime d ∧ d ≤ (L + 1) ^ 2 ∧
        |h| ≤ ((L + 1) ^ 2 : ℕ) ∧ (d : ℤ) * z = (c : ℤ) * t + h := by
      rcases htarget with hxz | hyz
      · exact GeometricAlignedTargetData.bounded_height ha hr hs hrQ hsQ hB
          (by have := (mem_Ico.mp hx).1; omega : 0 < x) hxz ij.1 hbaseX
      · exact GeometricAlignedTargetData.bounded_height (ha.trans horder) hr hs hrQ hsQ hB
          (by have := (mem_Ico.mp hy).1; omega : 0 < y) hyz ij.2 hbaseY
    obtain ⟨c, d, h, hc, hd, hcd, hdH, hh, heq⟩ := hdata
    have hgeom : EnlargedPairGeometry.Geometric a b x y L := by
      have hh' := FixedChannelLinearCount.unit_alignment (a := a) (b := b) (L := L) (by omega : 0 < N)
        (xy := (x, y)) (mem_filter.mpr ⟨mem_product.mpr ⟨hx, hy⟩, ⟨ij, hij⟩⟩)
      simpa only [EnlargedPairGeometry.Geometric, Nat.cast_mul] using hh'
    let rep : EnlargedAllAlignedTargetTripleMass.Representation N L a b 2 T :=
      ⟨x, y, z, t, c, d, ij.1, h, hfamily, hx, hy, hz, hc, hd, hcd, hdH, hh, hbaseX, hgeom, heq⟩
    exact mem_filter.mpr ⟨hu N (by omega) L hcrit T hcard ⟨(a, b), hab, ⟨rep⟩⟩, hsep⟩
  exact (sum_le_sum_of_subset_of_nonneg hsub
    (fun T _ _ ↦ (HomogeneousRunMass.probability_pos L T).le)).trans (hm N (by omega) L hcrit)

end PaperP1.HomogeneousSharedInteriorTriples
