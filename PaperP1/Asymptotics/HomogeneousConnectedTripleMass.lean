module

public import PaperP1.Asymptotics.HomogeneousEnlargedTripleMass
public import PaperP1.Asymptotics.HomogeneousCompressedNonalignedMass
public import PaperP1.Asymptotics.ConnectedCompressedTripleMass

/-! # Homogeneous mass of regular separated connected triples above a fixed unit channel -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HomogeneousConnectedTripleMass

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.HomogeneousRunMass

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def hosts (N a b L : ℕ) : Finset (Finset ℕ) :=
  (ConnectedCompressedTripleMass.hosts N a b L).filter fun T ↦
    T ⊆ RegularStarts.regularStarts N L

def nonalignedHosts (N a b L : ℕ) : Finset (Finset ℕ) :=
  univ.biUnion fun ij : Fin (L + 1) × Fin (L + 1) ↦
    (HomogeneousCompressedNonalignedMass.points N a b L ij.1 ij.2).image
      ConnectedCompressedTripleMass.family

def mass (N a b L : ℕ) : ℝ := SeparatedHomogeneousMass.mass L (hosts N a b L)

theorem nonaligned_mass_le (N a b L : ℕ) :
    (∑ T ∈ nonalignedHosts N a b L, probability L T) ≤
      HomogeneousCompressedNonalignedMass.channelMass N a b L := by
  calc
    _ ≤ ∑ ij : Fin (L + 1) × Fin (L + 1),
        ∑ T ∈ (HomogeneousCompressedNonalignedMass.points N a b L ij.1 ij.2).image
          ConnectedCompressedTripleMass.family, probability L T :=
      GraphStarWeights.sum_biUnion_le_nonneg univ _ _ (fun T ↦ (probability_pos L T).le)
    _ ≤ _ := sum_le_sum fun _ _ ↦ sum_image_le_of_nonneg (fun T _ ↦ (probability_pos L T).le)

theorem finite_cover {N a b L : ℕ} (hN : 2 ≤ N) (ha : 0 < a) (hab : a < b)
    (hcop : a.Coprime b) (hlarge : (a + b) * (L + 1) < N) :
    (hosts N a b L).filter (SeparatedHomogeneousMass.Separated L) ⊆
      (CompressedAlignedTripleMass.hosts {(a, b)} b N L).filter (SeparatedHomogeneousMass.Separated L) ∪
        nonalignedHosts N a b L := by
  intro T hT
  obtain ⟨hhost, hsep⟩ := mem_filter.mp hT
  obtain ⟨hconn, hreg⟩ := mem_filter.mp hhost
  rcases mem_union.mp (ConnectedCompressedTripleMass.finite_cover hN ha hab hcop hlarge hconn) with hA | hB
  · exact mem_union_left _ (mem_filter.mpr ⟨hA, hsep⟩)
  · obtain ⟨ij, hij, himage⟩ := mem_biUnion.mp hB
    obtain ⟨p, hp, hpT⟩ := mem_image.mp himage
    have hzT : p.2 ∈ T := (le_of_eq hpT) (by simp [ConnectedCompressedTripleMass.family])
    exact mem_union_right _ (mem_biUnion.mpr ⟨ij, hij, mem_image.mpr
      ⟨p, mem_filter.mpr ⟨hp, hreg hzT⟩, hpT⟩⟩)

theorem finite_mass {N a b L : ℕ} (hN : 2 ≤ N) (ha : 0 < a) (hab : a < b)
    (hcop : a.Coprime b) (hlarge : (a + b) * (L + 1) < N) :
    mass N a b L ≤ SeparatedHomogeneousMass.mass L (CompressedAlignedTripleMass.hosts {(a, b)} b N L) +
      HomogeneousCompressedNonalignedMass.channelMass N a b L := by
  have h0 := sum_le_sum_of_subset_of_nonneg (finite_cover hN ha hab hcop hlarge)
    (fun T _ _ ↦ (probability_pos L T).le)
  have h1 := GraphStarWeights.sum_union_le_nonneg
    ((CompressedAlignedTripleMass.hosts {(a, b)} b N L).filter (SeparatedHomogeneousMass.Separated L))
    (nonalignedHosts N a b L) (probability L) (fun T ↦ (probability_pos L T).le)
  have h2 := nonaligned_mass_le N a b L
  change mass N a b L ≤ _ at h0
  change _ ≤ SeparatedHomogeneousMass.mass L (CompressedAlignedTripleMass.hosts {(a, b)} b N L) + _ at h1
  linarith only [h0, h1, h2]

theorem uniform_mass (a b : ℕ) (ha : 0 < a) (hab : a < b) (hb2a : b < 2 * a)
    (hcop : a.Coprime b) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → mass N a b L ≤ (N : ℝ) ^ (-4 / 3 + ε) := by
  obtain ⟨Nn, _hNn, hn⟩ := HomogeneousCompressedNonalignedMass.uniform_mass
    a b ha hab hcop (by omega) C (ε / 2) (by positivity)
  obtain ⟨Na, _hNa, haM⟩ := HomogeneousEnlargedTripleMass.compressed_uniform_mass {(a, b)} b
    (by intro ab hab'; have heq := mem_singleton.mp hab'; subst ab; exact ⟨ha, hab, hb2a, hcop⟩)
    C (ε / 2) (by positivity)
  obtain ⟨Nw, hw⟩ := CriticalPolynomialScale.polynomial_lt_scale C ((a + b : ℕ) : ℝ) (Nat.cast_nonneg _) 1
  obtain ⟨Nf, hf⟩ := HalfCountSchedule.factor_absorption 2 (-4 / 3 + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 4 (max Na (max Nw (max Nf Nn))), by omega, ?_⟩
  intro N hN L hcrit
  have hlarge : (a + b) * (L + 1) < N := by
    have hh := hw N (by omega) L hcrit
    simp only [pow_one] at hh
    exact_mod_cast hh
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hA := (haM N (by omega) L hcrit).trans
    (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith : (-41 / 30 : ℝ) + ε / 2 ≤ -4 / 3 + ε / 2))
  have hN := hn N (by omega) L hcrit
  calc
    _ ≤ 2 * (N : ℝ) ^ (-4 / 3 + ε / 2) := by
      have hh := finite_mass (by omega : 2 ≤ N) ha hab hcop hlarge
      linarith only [hh, hA, hN]
    _ ≤ _ := by
      simpa only [show (-4 / 3 + ε / 2) + ε / 2 = -4 / 3 + ε by ring] using hf N (by omega)

end PaperP1.HomogeneousConnectedTripleMass
