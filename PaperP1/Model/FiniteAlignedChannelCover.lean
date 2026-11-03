module

public import PaperP1.Model.PrincipalAlignedCover
public import Mathlib.Data.Nat.GCD.Basic

/-! # An actual finite-channel cover at every fixed retained height -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FiniteAlignedChannelCover

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.EnlargedPairGeometry PaperP1.NormalizedUnitCount

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def channels (Q : ℕ) : Finset (ℕ × ℕ) :=
  ((range (Q + 1)) ×ˢ (range (Q + 1))).filter fun ab ↦
    0 < ab.1 ∧ ab.1 < ab.2 ∧ ab.2 < 2 * ab.1 ∧ ab.1.Coprime ab.2 ∧ 3 ≤ ab.2

def privatePairs (Q N H L : ℕ) : Finset (Finset ℕ) :=
  (channels Q).biUnion fun ab ↦ PrivateChannelActivity.pairs N H ab.1 ab.2 L

def defectivePairs (Q N H L : ℕ) : Finset (Finset ℕ) :=
  (channels Q).biUnion fun ab ↦ NormalizedDefectPairActivity.pairs N H ab.1 ab.2 L

theorem channel_data {Q : ℕ} {ab : ℕ × ℕ} (hab : ab ∈ channels Q) :
    0 < ab.1 ∧ ab.1 < ab.2 ∧ ab.2 < 2 * ab.1 ∧ ab.1.Coprime ab.2 ∧ 3 ≤ ab.2 ∧ ab.2 ≤ Q := by
  obtain ⟨hmem, ha, hlt, hint, hcop, hb⟩ := mem_filter.mp hab
  exact ⟨ha, hlt, hint, hcop, hb, by have h := mem_range.mp (mem_product.mp hmem).2; omega⟩

theorem classification {Q N L : ℕ} (hlarge : 2 * (L + 1) ^ 4 < N)
    {e : Finset ℕ} (he : e ∈ AllAlignedPairs.families N L) :
    e ∈ BoundaryAlignedPairs.channel N L 1 1 ∨
    e ∈ BoundaryAlignedPairs.channel N L 1 2 ∨
    (∃ ab ∈ channels Q, e ∈ BoundaryAlignedPairs.channel N L ab.1 ab.2) ∨
    e ∈ AlignedChannelFamilies.families N L (Q + 1) := by
  have heN := (mem_filter.mp he).1
  obtain ⟨x, y, a, b, hx, hy, rfl, hxy, ha, hb, hcop, hheight, hg⟩ := AllAlignedPairs.data he
  have haB := (le_max_left a b).trans hheight
  have hbB := (le_max_right a b).trans hheight
  have hsmall : (a + b) * (L + 1) < N := by
    calc
      _ ≤ (2 * (L + 1) ^ 3) * (L + 1) := Nat.mul_le_mul_right _ (by omega)
      _ = 2 * (L + 1) ^ 4 := by ring
      _ < _ := hlarge
  have hab := AllAlignedPairs.orientation (mem_Ico.mp hx).1 hxy hg hsmall
  by_cases heq : a = b
  · subst b
    have ha1 : a = 1 := by simpa only [Nat.Coprime, Nat.gcd_self] using hcop
    subst a
    exact Or.inl (mem_filter.mpr ⟨heN, x, y, rfl, hxy, hg⟩)
  have hablt : a < b := by omega
  have hinterior := AllAlignedPairs.interior (mem_Ico.mp hx).1 (mem_Ico.mp hy).2 hg hsmall
  by_cases hboundary : b = 2 * a
  · have ha1 : a = 1 := Nat.eq_one_of_dvd_coprimes hcop dvd_rfl ⟨2, by omega⟩
    subst a
    have hb2 : b = 2 := by omega
    subst b
    exact Or.inr (Or.inl (mem_filter.mpr ⟨heN, x, y, rfl, hxy, hg⟩))
  have hbint : b < 2 * a := by omega
  by_cases hQ : Q + 1 ≤ b
  · right; right; right
    exact mem_filter.mpr ⟨heN, (a, b), mem_filter.mpr ⟨mem_product.mpr
      ⟨mem_range.mpr (by omega), mem_range.mpr (by omega)⟩, ha, hablt, hcop, hQ⟩,
      x, y, rfl, hxy, hg⟩
  · right; right; left
    refine ⟨(a, b), mem_filter.mpr ⟨mem_product.mpr ⟨mem_range.mpr (by omega), mem_range.mpr (by omega)⟩,
      ha, hablt, hbint, hcop, by omega⟩, ?_⟩
    exact mem_filter.mpr ⟨heN, x, y, rfl, hxy, hg⟩

theorem nonzero_cover {Q N H L : ℕ} (hN : 2 ≤ N) (hL : 0 < L)
    (hheight : Q ≤ (L + 1) ^ 3) (hlarge : 2 * (L + 1) ^ 4 < N)
    {e : Finset ℕ} (he : e ∈ AllAlignedPairs.families N L)
    (hn : infiniteCenteredCoefficient L e ≠ 0) :
    e ∈ BoundaryAlignedPairs.channel N L 1 1 ∨
    e ∈ BoundaryAlignedPairs.channel N L 1 2 ∨
    e ∈ privatePairs Q N H L ∨ e ∈ defectivePairs Q N H L ∨
    e ∈ AlignedChannelFamilies.zeroFamilies N L ∨
    e ∈ AlignedChannelFamilies.families N L (Q + 1) := by
  rcases classification (Q := Q) hlarge he with h1 | h2 | ⟨ab, hab, heab⟩ | htail
  · exact Or.inl h1
  · exact Or.inr (Or.inl h2)
  · obtain ⟨ha, hlt, _, hcop, _, hbQ⟩ := channel_data hab
    have hcover := PrincipalAlignedCover.channel_nonzero_cover (H := H) hN ha hlt hcop (hbQ.trans hheight) hL heab hn
    rcases mem_union.mp hcover with h | hz
    · rcases mem_union.mp h with hp | hd
      · exact Or.inr (Or.inr (Or.inl (mem_biUnion.mpr ⟨ab, hab, hp⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (mem_biUnion.mpr ⟨ab, hab, hd⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hz))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr htail))))

end PaperP1.FiniteAlignedChannelCover
