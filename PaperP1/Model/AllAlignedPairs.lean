module

public import PaperP1.Model.BoundaryAlignedPairs
public import PaperP1.Model.PrincipalChannelEdges
public import PaperP1.Arithmetic.CompressedTargetAlignment

/-! # The literal source alignment splits into boundary, principal and high channels -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AllAlignedPairs

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.EnlargedPairGeometry PaperP1.BoundaryAlignedPairs

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def families (N L : ℕ) : Finset (Finset ℕ) :=
  ((dyadicBlock N).powersetCard 2).filter fun e ↦ ∃ x y : ℕ,
    e = {x, y} ∧ x < y ∧ CompressedTargetAlignment.Aligned 1 x y L

def nonaligned (N L : ℕ) : Finset (Finset ℕ) := (dyadicBlock N).powersetCard 2 \ families N L

theorem orientation {N L a b x y : ℕ} (hx : N ≤ x) (hxy : x < y)
    (hg : Geometric a b x y L) (hsmall : (a + b) * (L + 1) < N) : a ≤ b := by
  by_contra hab
  have hcoef : b * x + x ≤ a * x := by
    have h := Nat.mul_le_mul_right x (show b + 1 ≤ a by omega)
    nlinarith only [h]
  have hmon := Nat.mul_le_mul_left a hxy.le
  have hcI : (b : ℤ) * x + x ≤ (a : ℤ) * x := by exact_mod_cast hcoef
  have hmI : (a : ℤ) * x ≤ (a : ℤ) * y := by exact_mod_cast hmon
  have hxI : (N : ℤ) ≤ x := by exact_mod_cast hx
  have hsI : ((a + b : ℕ) : ℤ) * ((L + 1 : ℕ) : ℤ) < N := by exact_mod_cast hsmall
  have hl := (abs_le.mp hg).1
  nlinarith only [hcI, hmI, hxI, hsI, hl]

theorem interior {N L a b x y : ℕ} (hx : N ≤ x) (hy : y < 2 * N)
    (hg : Geometric a b x y L) (hsmall : (a + b) * (L + 1) < N) : b ≤ 2 * a := by
  by_contra hb
  have hlo : 2 * a * N + N ≤ b * x := by
    have h := Nat.mul_le_mul (show 2 * a + 1 ≤ b by omega) hx
    nlinarith only [h]
  have hhi : a * y ≤ 2 * a * N := by
    have h := Nat.mul_le_mul_left a hy.le
    nlinarith only [h]
  have hloI : 2 * (a : ℤ) * N + N ≤ (b : ℤ) * x := by exact_mod_cast hlo
  have hhiI : (a : ℤ) * y ≤ 2 * (a : ℤ) * N := by exact_mod_cast hhi
  have hsI : ((a + b : ℕ) : ℤ) * ((L + 1 : ℕ) : ℤ) < N := by exact_mod_cast hsmall
  have hu := (abs_le.mp hg).2
  nlinarith only [hloI, hhiI, hsI, hu]

theorem data {N L : ℕ} {e : Finset ℕ} (he : e ∈ families N L) :
    ∃ x y a b : ℕ, x ∈ dyadicBlock N ∧ y ∈ dyadicBlock N ∧ e = {x, y} ∧ x < y ∧
      0 < a ∧ 0 < b ∧ a.Coprime b ∧ max a b ≤ (L + 1) ^ 3 ∧ Geometric a b x y L := by
  obtain ⟨heN, x, y, rfl, hxy, a, b, ha, hb, hcop, haB, hbB, hg⟩ := mem_filter.mp he
  have heSub := (mem_powersetCard.mp heN).1
  refine ⟨x, y, a, b, heSub (mem_insert_self _ _), heSub (mem_insert_of_mem (mem_singleton_self _)),
    rfl, hxy, ha, hb, hcop, max_le haB hbB, ?_⟩
  simpa only [Geometric, one_mul, abs_sub_comm] using hg

theorem classification {N L : ℕ} (hlarge : 2 * (L + 1) ^ 4 < N) {e : Finset ℕ}
    (he : e ∈ families N L) :
    e ∈ channel N L 1 1 ∨ e ∈ channel N L 1 2 ∨ e ∈ channel N L 2 3 ∨
      e ∈ channel N L 3 4 ∨ e ∈ AlignedChannelFamilies.families N L 5 := by
  have heN := (mem_filter.mp he).1
  obtain ⟨x, y, a, b, hx, hy, rfl, hxy, ha, hb, hcop, hheight, hg⟩ := data he
  have haB := (le_max_left a b).trans hheight
  have hbB := (le_max_right a b).trans hheight
  have hsmall : (a + b) * (L + 1) < N := by
    calc
      _ ≤ (2 * (L + 1) ^ 3) * (L + 1) := Nat.mul_le_mul_right _ (by omega)
      _ = 2 * (L + 1) ^ 4 := by ring
      _ < _ := hlarge
  have hab := orientation (mem_Ico.mp hx).1 hxy hg hsmall
  by_cases heq : a = b
  · subst b
    have ha1 : a = 1 := by simpa only [Nat.Coprime, Nat.gcd_self] using hcop
    subst a
    exact Or.inl (mem_filter.mpr ⟨heN, x, y, rfl, hxy, hg⟩)
  have hablt : a < b := by omega
  have hint := interior (mem_Ico.mp hx).1 (mem_Ico.mp hy).2 hg hsmall
  by_cases hfive : 5 ≤ b
  · right; right; right; right
    exact mem_filter.mpr ⟨heN, (a, b), mem_filter.mpr ⟨mem_product.mpr
      ⟨mem_range.mpr (by omega), mem_range.mpr (by omega)⟩, ha, hablt, hcop, hfive⟩,
      x, y, rfl, hxy, hg⟩
  have hcases : (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 3) ∨ (a = 2 ∧ b = 4) ∨ (a = 3 ∧ b = 4) := by omega
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inr (Or.inl (mem_filter.mpr ⟨heN, x, y, rfl, hxy, hg⟩))
  · exact Or.inr (Or.inr (Or.inl (mem_filter.mpr ⟨heN, x, y, rfl, hxy, hg⟩)))
  · norm_num at hcop
  · exact Or.inr (Or.inr (Or.inr (Or.inl (mem_filter.mpr ⟨heN, x, y, rfl, hxy, hg⟩))))

theorem private_channel_subset {N H L a b : ℕ} (hN : 2 ≤ N) (ha : 0 < a) (hab : a < b)
    (hcop : a.Coprime b) (hheight : b ≤ (L + 1) ^ 3) (hlarge : (a + b) * (L + 1) < N) :
    PrivateChannelActivity.pairs N H a b L ⊆ families N L := by
  intro e he
  have heN := PrivateChannelActivity.pair_data hN hab hlarge he
  obtain ⟨xy, hxy, rfl⟩ := mem_image.mp he
  obtain ⟨hx, hy, _, _⟩ := PrivateChannelSources.mem_goodSources.mp hxy
  have hg : Geometric a b xy.1 xy.2 L := by
    have h := FixedChannelLinearCount.unit_alignment (by omega : 0 < N)
      (PrivateChannelSources.good_sources_subset_unitSources N H a b L hxy)
    simpa only [Geometric, Nat.cast_mul] using h
  exact mem_filter.mpr ⟨mem_powersetCard.mpr heN, xy.1, xy.2, rfl,
    PrivateChannelSources.good_sources_order hN hab hlarge hxy,
    CompressedTargetAlignment.of_geometric ha (ha.trans hab) hcop (hab.le.trans hheight) hheight hg⟩

theorem principal_subset {N H L : ℕ} (hN : 2 ≤ N) (hheight : 4 ≤ (L + 1) ^ 3)
    (hlarge : 29 * (L + 1) < N) : PrincipalChannelEdges.edges N H L ⊆ families N L := by
  intro e he
  rcases mem_union.mp he with he | he
  · exact private_channel_subset hN (by decide : 0 < 2) (by decide : 2 < 3) (by decide) (by omega) (by omega) (mem_filter.mp he).1
  · exact private_channel_subset hN (by decide : 0 < 3) (by decide : 3 < 4) (by decide) hheight (by omega) (mem_filter.mp he).1

end PaperP1.AllAlignedPairs
