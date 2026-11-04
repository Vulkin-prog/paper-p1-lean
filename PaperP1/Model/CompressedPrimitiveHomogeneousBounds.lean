module

public import PaperP1.Model.PairCompressedPrimitiveTransport
public import PaperP1.Model.OneBlockFullSupport
public import PaperP1.Model.HomogeneousBlockIntersection
public import PaperP1.Model.CompressedPairCoefficient

/-! # Actual primitive compressed weights have a homogeneous majorant at every order

The old block may have internal relations. All original centered terms and
the separately centered compressed block are retained.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CompressedPrimitiveHomogeneousBounds

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.FiniteFamilyEnumeration

theorem full_support (L : ℕ) (e A U : Finset ℕ)
    (hspace : FiniteEvenSquareClasses.space U = FixedPairExtensions.sourceSpace e L)
    (hp : PairPrimitiveCompression.Primitive L e A) : OneBlockFullSupport.FullSupport L U A := by
  let W := FixedPairExtensions.sourceSpace e L
  let : Fintype W := MinimalRelativeRelations.spanFintype (fun x ↦ squareClassSpace x L) e
  obtain ⟨u, hu, hsum⟩ := MinimalRelativeRelations.exists_relation W
    (fun x ↦ squareClassSpace x L) A hp.2.2.1 hp.2.2.2
  let v : FiniteEvenSquareClasses.space U :=
    ⟨-(∑ i : A, (u i).val), hspace.symm ▸ W.neg_mem hsum⟩
  have hv : v ≠ 0 := by
    intro hv
    have hsum0 : (∑ i : A, (u i).val) = 0 := by
      have hh := congrArg Subtype.val hv
      change -(∑ i : A, (u i).val) = 0 at hh
      exact neg_eq_zero.mp hh
    have hinj := (CompressedBlocks.direct_family_iff_zero_nullity
      (fun x ↦ squareClassSpace x L) A).mpr hp.2.1
    have hu0 : u = 0 := hinj (hsum0.trans (map_zero _).symm)
    obtain ⟨x, hx⟩ := PairPrimitiveCompression.nonempty L e A hp
    exact hu ⟨x, hx⟩ (congrFun hu0 ⟨x, hx⟩)
  exact ⟨v, hv, u, hu, neg_add_cancel _⟩

theorem probability_upper {N L : ℕ} (hN : 0 < N) (xy : ℕ × ℕ) (A : Finset ℕ)
    (hA : A ⊆ RegularStarts.regularStarts N L)
    (hp : PairPrimitiveCompression.Primitive L {xy.1, xy.2} A) :
    HomogeneousRunMass.probability L ({xy.1, xy.2} ∪ A) ≤
      HomogeneousRunMass.probability L {xy.1, xy.2} * ((2 ^ L : ℝ)⁻¹) ^ A.card * (2 ^ L : ℝ) := by
  let z := centres A rfl
  have hz : ∀ i, z i ∈ RegularStarts.regularStarts N L := centres_mem _ A rfl hA
  have hset : tupleSet z = A := centres_tupleSet A rfl
  have hprim := PairCompressedPrimitiveTransport.indexed_primitive xy z (centres_injective A rfl)
    (by rw [hset]; exact hp)
  have hcard : 0 < A.card := (PairPrimitiveCompression.nonempty L {xy.1, xy.2} A hp).card_pos
  let i : Fin A.card := ⟨0, hcard⟩
  have hpos : 0 < z i := hN.trans_le
    (mem_Ico.mp (RegularStarts.regularStarts_subset N L (hz i))).1
  have hrank := PairCompressedPrimitiveFamilies.primitive_nullity_le xy z hprim i hpos
  have hfamily : PairCompressedPrimitiveFamilies.family xy z = {xy.1, xy.2} ∪ A := by
    change {xy.1, xy.2} ∪ tupleSet z = _
    rw [hset]
  rw [← hfamily, PairCompressedPrimitiveFamilies.weight_factor xy z hz]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hrank)
    (mul_nonneg (HomogeneousRunMass.probability_pos L _).le (by positivity))

theorem regular_weight {N L : ℕ} (hN : 0 < N) (hL : 0 < L) (I : Finset ℕ)
    (hI : I ⊆ RegularStarts.regularStarts N L) :
    PrimitiveWindowMass.weight L I = HomogeneousRunMass.probability L I := by
  rw [HomogeneousRunMass.regular_weight hI, PrimitiveWindowMass.weight, PrimitiveNominalMass.weight]
  congr 1
  calc
    _ = ∏ _x ∈ I, (2 ^ L : ℝ)⁻¹ := by
      apply prod_congr rfl
      intro x hx
      exact RegularStarts.marginal_on_regular
        (hN.trans_le (mem_Ico.mp (RegularStarts.regularStarts_subset N L (hI hx))).1) hL (hI hx)
    _ = _ := by rw [prod_const]

theorem regular_product {N L : ℕ} (hN : 0 < N) (hL : 0 < L) (A : Finset ℕ)
    (hA : A ⊆ RegularStarts.regularStarts N L) (w : ℝ) :
    (∏ x ∈ A, w * infiniteMarginal x L) = w ^ A.card * ((2 ^ L : ℝ)⁻¹) ^ A.card := by
  rw [prod_mul_distrib, prod_const]
  congr 1
  calc
    _ = ∏ _x ∈ A, (2 ^ L : ℝ)⁻¹ := by
      apply prod_congr rfl
      intro x hx
      exact RegularStarts.marginal_on_regular
        (hN.trans_le (mem_Ico.mp (RegularStarts.regularStarts_subset N L (hA hx))).1) hL (hA hx)
    _ = _ := by rw [prod_const]

theorem point_upper {N L : ℕ} (hN : 0 < N) (hL : 0 < L) (xy : ℕ × ℕ) (A : Finset ℕ)
    (hA : A ⊆ RegularStarts.regularStarts N L)
    (hp : PairPrimitiveCompression.Primitive L {xy.1, xy.2} A)
    (w R : ℝ) (hw : 0 ≤ w) (hR : HomogeneousRunMass.probability L {xy.1, xy.2} ≤ R) :
    w ^ (A.card + 2) * HomogeneousRunMass.probability L ({xy.1, xy.2} ∪ A) ≤
      (w * R * (2 ^ L : ℝ) ^ 2) *
        ((w * (2 ^ L : ℝ)⁻¹) * ∏ x ∈ A, w * infiniteMarginal x L) := by
  have hprob := (probability_upper hN xy A hA hp).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hR (by positivity)) (by positivity))
  calc
    _ ≤ w ^ (A.card + 2) * (R * ((2 ^ L : ℝ)⁻¹) ^ A.card * (2 ^ L : ℝ)) :=
      mul_le_mul_of_nonneg_left hprob (pow_nonneg hw _)
    _ = _ := by
      rw [regular_product hN hL A hA w, pow_add, pow_two, inv_pow]
      field_simp

theorem product_le (L : ℕ) (E A : Finset ℕ) :
    HomogeneousRunMass.probability L E * HomogeneousRunMass.probability L A ≤
      HomogeneousRunMass.probability L (E ∪ A) := by
  rw [HomogeneousBlockIntersection.exact]
  exact le_mul_of_one_le_right
    (mul_nonneg (HomogeneousRunMass.probability_pos L E).le (HomogeneousRunMass.probability_pos L A).le)
    (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))

theorem three_mass_upper {N L : ℕ} (hN : 2 ≤ N) (hL : 0 < L) (e A : Finset ℕ)
    (he : e.card = 2) (hreg : e ∪ A ⊆ RegularStarts.regularStarts N L)
    (hp : PairPrimitiveCompression.Primitive L e A) :
    infiniteJointMoment L (e ∪ A) + |CompressedPairCoefficient.value L e A| +
      |infiniteCenteredCoefficient L (e ∪ A)| ≤ 4 * HomogeneousRunMass.probability L (e ∪ A) := by
  have hA : A ⊆ RegularStarts.regularStarts N L := subset_union_right.trans hreg
  have hz : relativeNullityOn (fun x ↦ squareClassSpace x L) A = 0 := hp.2.1
  have hprod : (∏ x ∈ A, infiniteMarginal x L) = HomogeneousRunMass.probability L A := by
    rw [HomogeneousRunMass.regular_weight hA, PrimitiveNominalMass.weight, hz, pow_zero, mul_one]
    have hh := regular_weight (by omega : 0 < N) hL A hA
    rw [HomogeneousRunMass.regular_weight hA, PrimitiveNominalMass.weight, hz,
      pow_zero, mul_one, PrimitiveWindowMass.weight, hz, pow_zero, mul_one] at hh
    exact hh
  have hsource : infiniteJointMoment L e * (∏ x ∈ A, infiniteMarginal x L) ≤
      HomogeneousRunMass.probability L (e ∪ A) := by
    rw [hprod]
    exact (mul_le_mul_of_nonneg_right (HomogeneousRunMass.actual_joint_le L hL e)
      (HomogeneousRunMass.probability_pos L A).le).trans (product_le L e A)
  have hq := HomogeneousRunMass.actual_joint_le L hL (e ∪ A)
  have hhat := CompressedPairCoefficient.primitive_abs_bound L hL e A he hp
  have hne : (e ∪ A).Nonempty := by
    obtain ⟨x, hx⟩ := card_pos.mp (show 0 < e.card by omega)
    exact ⟨x, mem_union_left A hx⟩
  have hc := PrimitiveWindowMass.centered_le_weight L hL (e ∪ A) hne (by
    intro x hx
    rw [RegularStarts.marginal_on_regular
      (by have hh := (mem_Ico.mp (RegularStarts.regularStarts_subset N L (hreg hx))).1; omega)
      hL (hreg hx)]
    positivity)
  rw [regular_weight (by omega) hL (e ∪ A) hreg] at hc
  linarith only [hq, hhat, hsource, hc]

end PaperP1.CompressedPrimitiveHomogeneousBounds
