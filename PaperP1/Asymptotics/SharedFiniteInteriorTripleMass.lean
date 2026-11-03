module

public import PaperP1.Model.FiniteInteriorUnitEdges
public import PaperP1.Asymptotics.EndpointGeometricTripleMass

/-! # Two actual unit edges in any fixed finite interior channel set have joint triple mass N⁻⁴¹ᐟ³⁰ -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SharedFiniteInteriorTripleMass

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.FiniteInteriorUnitEdges

theorem uniform_mass (Q : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ F : Finset (Finset ℕ),
      (∀ T ∈ F, T ⊆ dyadicBlock N ∧ T.card = 3 ∧
        2 ≤ ((edges N L Q).filter fun e ↦ e ⊆ T).card) →
      (∑ T ∈ F, infiniteJointMoment L T) ≤ (N : ℝ) ^ (-41 / 30 + ε) := by
  classical
  have hchannels (ab : ℕ × ℕ) (hab : ab ∈ channels Q) :
      0 < ab.1 ∧ ab.1 < ab.2 ∧ ab.2 < 2 * ab.1 ∧ ab.1.Coprime ab.2 := by
    obtain ⟨ha, hlt, hint, hcop, _haQ, _hbQ⟩ := channel_data hab
    exact ⟨ha, hlt, hint, hcop⟩
  obtain ⟨N₀, hN₀, h⟩ := EndpointGeometricTripleMass.uniform_mass (channels Q) Q hchannels C ε hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L hband F hF
  have hsub : F ⊆ EndpointGeometricTripleMass.hosts (channels Q) Q N L := by
    intro T hT
    obtain ⟨hTG, hcard, htwo⟩ := hF T hT
    obtain ⟨a, b, x, y, z, r, s, hab, hfamily, hu, hr, hrQ, hs, hsQ, hgeom⟩ :=
      triple_source (by omega : 0 < N) hcard htwo
    exact EndpointGeometricTripleMass.source_mem_hosts hTG hcard
      ⟨(a, b), hab, x, y, z, r, s, hfamily, hu, hr, hrQ, hs, hsQ, hgeom⟩
  exact (sum_le_sum_of_subset_of_nonneg hsub (fun T _ _ ↦ infiniteJointMoment_nonneg L T)).trans
    (h N hN L hband)

end PaperP1.SharedFiniteInteriorTripleMass
