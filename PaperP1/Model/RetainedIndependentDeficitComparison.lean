module

public import PaperP1.Model.RetainedDeficitGrouping
public import PaperP1.Model.IndependentExtensionDeficit
public import PaperP1.Model.OrdinaryIndependentDeficit
public import PaperP1.Model.PrivateChannelActivity

/-! # The literal retained independent deficits are exactly ordinary and source-relative product-weight masses -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RetainedIndependentDeficitComparison

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.RetainedReferenceTheorem PaperP1.RetainedDeficitNorm PaperP1.RetainedReferenceIdentity
  PaperP1.GoodEdgeCompression PaperP1.PrivateChannelSources

local instance retainedIndependentDeficitComparisonPrimeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

theorem first_eq (N L : ℕ) : firstMass N L =
    OrdinaryIndependentDeficit.mass (RegularStarts.regularStarts N L) L (fun x ↦ 2 * infiniteMarginal x L) := by
  unfold firstMass directMass OrdinaryIndependentDeficit.mass OrdinaryIndependentDeficit.families
  apply sum_congr rfl
  intro I _
  rw [prod_mul_distrib, prod_const]

theorem direct_source_iff_compressed (L : ℕ) (e A : Finset ℕ) (hdis : Disjoint e A) :
    IndependentExtensionDeficit.Direct (SubspaceFamilyRank.span (fun x ↦ squareClassSpace x L) e) L A ↔
      RetainedDependence.Compressed (fun x ↦ squareClassSpace x L) e (e ∪ A) := by
  let : Fintype (SubspaceFamilyRank.span (fun x ↦ squareClassSpace x L) e) :=
    MinimalRelativeRelations.spanFintype _ e
  rw [IndependentExtensionDeficit.direct_iff_nullity]
  exact MinimalRelativeRelations.zero_iff_compressed _ e A hdis

theorem failed_eq (G : Finset ℕ) (L : ℕ) (e : Finset ℕ) :
    failedExtensions (fun x ↦ squareClassSpace x L) G e =
      IndependentExtensionDeficit.families (G \ e) (SubspaceFamilyRank.span (fun x ↦ squareClassSpace x L) e) L := by
  classical
  ext A
  rw [IndependentExtensionDeficit.mem_families]
  simp only [failedExtensions, mem_filter, mem_powerset]
  apply and_congr_right
  intro hA
  have hdis : Disjoint e A := disjoint_left.mpr (fun x he hx ↦ (mem_sdiff.mp (hA hx)).2 he)
  exact not_congr (direct_source_iff_compressed L e A hdis).symm

theorem second_eq (H : ℝ) (N L : ℕ) : secondMass H N L =
    4 * ∑ e ∈ goodEdges H N L, infiniteJointMoment L e *
      IndependentExtensionDeficit.deficit (RegularStarts.regularStarts N L) e
        (SubspaceFamilyRank.span (fun x ↦ squareClassSpace x L) e) L 2 := by
  unfold secondMass compressedMass
  rw [mul_sum]
  apply sum_congr rfl
  intro e _
  rw [failed_eq, IndependentExtensionDeficit.deficit_eq_product_weights, mul_sum, mul_sum]
  apply sum_congr rfl
  intro A _
  rw [prod_mul_distrib, prod_const, pow_add]
  norm_num
  ring

theorem privateAbove_zero {H : ℝ} {S : Finset ℕ} (h : PrivateAbove H S) : PrivateAbove 0 S := by
  intro n hn
  obtain ⟨p, hp, _, hpn, hrest⟩ := h n hn
  exact ⟨p, hp, by exact_mod_cast hp.pos, hpn, hrest⟩

theorem good_subset_zero_channels {N L : ℕ} (hN : 2 ≤ N) (H : ℝ) : goodEdges H N L ⊆
    PrivateChannelActivity.pairs N 0 2 3 L ∪ PrivateChannelActivity.pairs N 0 3 4 L := by
  classical
  intro e he
  obtain ⟨xy, hxy, rfl⟩ := mem_image.mp he
  obtain ⟨hx, hy, _hxy, _hpos, hdep, a, b, hlead, hprivate⟩ := (mem_filter.mp hxy).2
  obtain ⟨ha, hb, _hcop, _hle, _hb4⟩ := leading_properties hlead
  have htwo := CompressionRank.dependent_two_units ha hb
    (hN.trans (mem_Ico.mp hx).1) (hN.trans (mem_Ico.mp hy).1) hprivate.private hdep
  have hpair : ({xy.1, xy.2} : Finset ℕ) ∈ PrivateChannelActivity.pairs N 0 a b L :=
    mem_image.mpr ⟨xy, mem_goodSources.mpr ⟨hx, hy, htwo,
      by simpa only [Nat.cast_zero] using privateAbove_zero hprivate⟩, rfl⟩
  rcases hlead with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact mem_union_left _ hpair
  · exact mem_union_right _ hpair

end PaperP1.RetainedIndependentDeficitComparison
