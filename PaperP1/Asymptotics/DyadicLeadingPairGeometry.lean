module

public import PaperP1.Asymptotics.DyadicRationalCodeGeometry
public import PaperP1.Asymptotics.CriticalPolynomialScale
public import PaperP1.Model.UnsignedUnitFourierAggregate

/-! # Exact dyadic leading orientations and rational unit support

Every enlarged2:3 pair is eventually separated. The1:3 and3:1
channels are absent in the dyadic interior, including zero-unit pairs.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DyadicLeadingPairGeometry

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.EnlargedPairGeometry
  PaperP1.NormalizedUnitCount PaperP1.DyadicAlignedPairMasks PaperP1.UnsignedUnitFourierAggregate

@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem geometric_separated {x y L : ℕ} (hlarge : 7 * (L + 1) < x) (hg : Geometric 2 3 x y L) :
    x + L < y := by
  have hh := (abs_le.mp hg).2
  have hx : (7 : ℤ) * ((L + 1 : ℕ) : ℤ) < x := by exact_mod_cast hlarge
  norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at hh hx
  have hi : (x : ℤ) + L < y := by omega
  exact_mod_cast hi

theorem one_three_absent {N L x y : ℕ} (hlarge : 4 * (L + 1) < N)
    (hx : x ∈ dyadicBlock N) (hy : y ∈ dyadicBlock N) : ¬Geometric 1 3 x y L := by
  intro hg
  have hh := (abs_le.mp hg).2
  have hxlo := (mem_Ico.mp hx).1
  have hyhi := (mem_Ico.mp hy).2
  norm_num only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, one_mul] at hh
  omega

theorem uniform_separation (C : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ xy ∈ channel N L 2 3, xy.1 + L < xy.2 := by
  obtain ⟨N₀, h⟩ := PaperP1.CriticalPolynomialScale.polynomial_lt_scale C 7 (by norm_num) 1
  refine ⟨N₀, ?_⟩
  intro N hN L hcrit xy hxy
  obtain ⟨hblock, hg⟩ := mem_filter.mp hxy
  have hxlo := (mem_Ico.mp (mem_product.mp hblock).1).1
  have hh := h N (by omega) L hcrit
  simp only [pow_one] at hh
  have hlarge : 7 * (L + 1) < N := by exact_mod_cast hh
  exact geometric_separated (hlarge.trans_le hxlo) hg

theorem uniform_symmetric_sum (C : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      leading N L = channel N L 2 3 ∪ channel N L 3 2 ∧
      Disjoint (channel N L 2 3) (channel N L 3 2) ∧
      ∀ f : ℕ × ℕ → ℝ, (∀ xy, f xy = f xy.swap) →
        (∑ xy ∈ leading N L, f xy) = 2 * ∑ xy ∈ channel N L 2 3, f xy := by
  obtain ⟨N₀, h⟩ := uniform_separation C
  refine ⟨N₀, ?_⟩
  intro N hN L hcrit
  have hf := h N hN L hcrit
  have hr : ∀ xy ∈ channel N L 3 2, xy.2 + L < xy.1 := by
    intro xy hxy
    have hswap : xy.swap ∈ channel N L 2 3 := by
      obtain ⟨hblock, hg⟩ := mem_filter.mp hxy
      obtain ⟨hx, hy⟩ := mem_product.mp hblock
      exact mem_filter.mpr ⟨mem_product.mpr ⟨hy, hx⟩, (geometric_swap 3 2 xy.1 xy.2 L).mp hg⟩
    exact hf xy.swap hswap
  have heq : leading N L = channel N L 2 3 ∪ channel N L 3 2 := by
    apply filter_eq_self.mpr
    intro xy hxy
    rcases mem_union.mp hxy with hxy | hxy
    · have hh := hf xy hxy
      unfold Nat.dist
      omega
    · have hh := hr xy hxy
      unfold Nat.dist
      omega
  have hdis : Disjoint (channel N L 2 3) (channel N L 3 2) := by
    apply disjoint_left.mpr
    intro xy hxy hyx
    have hh := hf xy hxy
    have hk := hr xy hyx
    omega
  refine ⟨heq, hdis, ?_⟩
  intro f hsym
  have hsum : (∑ xy ∈ channel N L 3 2, f xy) = ∑ xy ∈ channel N L 2 3, f xy := by
    rw [← channel_swap N L 2 3, sum_image]
    · exact sum_congr rfl (fun xy _ ↦ (hsym xy).symm)
    · intro xy _ uv _ hh
      have hk := congrArg Prod.swap hh
      simpa only [Prod.swap_swap] using hk
  rw [heq, sum_union hdis, hsum]
  ring


theorem rational_forward_sum {N L : ℕ} (hN : 2 ≤ N) :
    (∑ xy ∈ channel N L 2 3, unitWeight 2 3 xy.1 xy.2 L) =
      ∑ x ∈ dyadicBlock N, ∑ y ∈ dyadicBlock N, unitWeight 2 3 x y L := by
  rw [← sum_product (dyadicBlock N) (dyadicBlock N) (fun xy : ℕ × ℕ ↦ unitWeight 2 3 xy.1 xy.2 L)]
  apply sum_subset (filter_subset _ _)
  intro xy hxy hn
  obtain ⟨hx, hy⟩ := mem_product.mp hxy
  have hnot : ¬(units 2 3 xy.1 xy.2 L).Nonempty := by
    intro hu
    exact hn (mem_filter.mpr ⟨hxy, PaperP1.ExactUnitGeometric.of_nonempty
      (by have := (mem_Ico.mp hx).1; omega) (by have := (mem_Ico.mp hy).1; omega) hu⟩)
  have hz : (units 2 3 xy.1 xy.2 L).card = 0 := card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp hnot)
  exact unitWeight_zero_of_card_le_one (by omega)

theorem uniform_one_three_absent (C : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → channel N L 1 3 = ∅ ∧ channel N L 3 1 = ∅ := by
  obtain ⟨N₀, h⟩ := PaperP1.CriticalPolynomialScale.polynomial_lt_scale C 4 (by norm_num) 1
  refine ⟨N₀, ?_⟩
  intro N hN L hcrit
  have hh := h N (by omega) L hcrit
  simp only [pow_one] at hh
  have hlarge : 4 * (L + 1) < N := by exact_mod_cast hh
  have heq : channel N L 1 3 = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro xy hxy
    obtain ⟨hblock, hg⟩ := mem_filter.mp hxy
    obtain ⟨hx, hy⟩ := mem_product.mp hblock
    exact one_three_absent hlarge hx hy hg
  refine ⟨heq, ?_⟩
  rw [← channel_swap N L 1 3, heq, image_empty]

end PaperP1.DyadicLeadingPairGeometry
