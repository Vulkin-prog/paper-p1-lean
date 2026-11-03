module

public import PaperP1.Asymptotics.StrongAlignedUnitChannels
public import PaperP1.Model.FiniteInteriorUnitEdges
public import PaperP1.Asymptotics.CriticalPolynomialScale

/-! # Every strongly aligned nonboundary pair belongs to a fixed finite interior unit-channel population -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.StrongAlignedInteriorEdges

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts

theorem uniform_edges (θ : ℝ) (hθ : 0 < θ) :
    ∃ Q : ℕ, 1 ≤ Q ∧ ∀ C : ℝ, ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ x y : ℕ,
      x ∈ dyadicBlock N → y ∈ dyadicBlock N → x < y →
      θ * L < (Module.finrank F₂ ↥(squareClassSpace x L ⊓ squareClassSpace y L) : ℝ) →
      CompressedTargetAlignment.Aligned 1 x y L →
      ({x, y} : Finset ℕ) ∉ BoundaryAlignedPairs.channel N L 1 1 →
      ({x, y} : Finset ℕ) ∉ BoundaryAlignedPairs.channel N L 1 2 →
      ({x, y} : Finset ℕ) ∈ FiniteInteriorUnitEdges.edges N L Q := by
  classical
  obtain ⟨Q, hQ, h⟩ := StrongAlignedUnitChannels.bounded_coprime_channels θ hθ
  refine ⟨Q, hQ, fun C ↦ ?_⟩
  obtain ⟨NU, _hNU, hu⟩ := h C
  obtain ⟨NG, hg⟩ := CriticalPolynomialScale.source_size_eventually C (2 * Q) 0
  refine ⟨3 + NU + NG, by omega, ?_⟩
  intro N hN L hband x y hx hy hxy hstrong halign hnotOne hnotTwo
  obtain ⟨a, b, ha, hab, hbQ, hcop, hunit⟩ := hu N (by omega) L hband x y hx hy hstrong halign
  have hsmall : (a + b) * (L + 1) < N := by
    have hg := hg N (by omega) L 1 hband (by simp)
    have hbound := Nat.mul_le_mul_right (L + 1) (show a + b ≤ 2 * Q by omega)
    nlinarith only [hg, hbound]
  have hpair : ({x, y} : Finset ℕ) ∈ (dyadicBlock N).powersetCard 2 :=
    mem_powersetCard.mpr ⟨by simp only [insert_subset_iff, singleton_subset_iff]; exact ⟨hx, hy⟩,
      card_pair hxy.ne⟩
  have hgeometry (a b u v : ℕ) (hu : u ∈ dyadicBlock N) (hv : v ∈ dyadicBlock N)
      (hunit : (NormalizedUnitCount.units a b u v L).Nonempty) :
      EnlargedPairGeometry.Geometric a b u v L := by
    have h := FixedChannelLinearCount.unit_alignment (a := a) (b := b) (L := L) (by omega : 0 < N)
      (xy := (u, v)) (mem_filter.mpr ⟨mem_product.mpr ⟨hu, hv⟩, hunit⟩)
    simpa only [EnlargedPairGeometry.Geometric, Nat.cast_mul] using h
  have hone (a b : ℕ) (heq : a = b) (hcop : a.Coprime b)
      (hg : EnlargedPairGeometry.Geometric a b x y L) : False := by
    have ha1 : a = 1 := by simpa only [heq, Nat.Coprime, Nat.gcd_self] using hcop
    have hb1 : b = 1 := by omega
    subst a; subst b
    exact hnotOne (mem_filter.mpr ⟨hpair, x, y, rfl, hxy, hg⟩)
  rcases hunit with hunit | hunit
  · have hgxy := hgeometry a b x y hx hy hunit
    have hlt : a < b := lt_of_le_of_ne hab (fun heq ↦ hone a b heq hcop hgxy)
    have hinter := AllAlignedPairs.interior (mem_Ico.mp hx).1 (mem_Ico.mp hy).2 hgxy hsmall
    have hstrict : b < 2 * a := by
      by_contra hn
      have heq : b = 2 * a := by omega
      have ha1 : a = 1 := by simpa only [Nat.Coprime, heq, Nat.gcd_mul_left_right] using hcop
      have hb2 : b = 2 := by omega
      subst a; subst b
      exact hnotTwo (mem_filter.mpr ⟨hpair, x, y, rfl, hxy, hgxy⟩)
    have hchannel : (a, b) ∈ FiniteInteriorUnitEdges.channels Q :=
      mem_filter.mpr ⟨mem_product.mpr ⟨mem_Icc.mpr ⟨ha, hab.trans hbQ⟩,
        mem_Icc.mpr ⟨ha.trans_le hab, hbQ⟩⟩, hlt, hstrict, hcop⟩
    exact mem_filter.mpr ⟨hpair, (a, b), hchannel, x, y, rfl, hunit⟩
  · have hgxy : EnlargedPairGeometry.Geometric b a x y L :=
      (EnlargedPairGeometry.geometric_swap a b y x L).mp (hgeometry a b y x hy hx hunit)
    have hsmall' : (b + a) * (L + 1) < N := by simpa only [Nat.add_comm b a] using hsmall
    have hba := AllAlignedPairs.orientation (mem_Ico.mp hx).1 hxy hgxy hsmall'
    exact False.elim (hone b a (by omega) hcop.symm hgxy)

end PaperP1.StrongAlignedInteriorEdges
