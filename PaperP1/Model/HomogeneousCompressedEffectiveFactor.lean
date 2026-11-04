module

public import PaperP1.Model.HomogeneousEffectiveWeights
public import PaperP1.Model.PairCompressedTwoTargetData

/-! # A compressed source and arbitrary effective original targets

The exact product contains each target's own homogeneous marginal. No
nominal or regular replacement is made.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HomogeneousCompressedEffectiveFactor

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.SubspaceFamilyRank
  PaperP1.PairCompressedPrimitiveFamilies PaperP1.FiniteFamilyEnumeration

theorem rank_add_nullity {t L : ℕ} (xy : ℕ × ℕ) (z : Fin t → ℕ) :
    rank (fun x ↦ squareClassSpace x L) (family xy z) + nullity xy L z =
      Module.finrank F₂ ↥(squareClassSpace xy.1 L ⊔ squareClassSpace xy.2 L) +
        ∑ i, Module.finrank F₂ (squareClassSpace (z i) L) := by
  have h := rank_add_nullity_on (spaces xy L z) univ
  rw [show rank (spaces xy L z) univ =
      rank (fun x ↦ squareClassSpace x L) (family xy z) by rw [rank, span_eq]; rfl] at h
  rw [Fin.sum_univ_succ] at h
  exact h

theorem factor {t L : ℕ} (xy : ℕ × ℕ) (z : Fin t → ℕ) :
    HomogeneousRunMass.probability L (family xy z) =
      HomogeneousRunMass.probability L {xy.1, xy.2} *
        (∏ i, HomogeneousRunMass.probability L {z i}) * (2 ^ nullity xy L z : ℝ) := by
  have hdim := rank_add_nullity (L := L) xy z
  have hpower : (2 ^ rank (fun x ↦ squareClassSpace x L) (family xy z) : ℝ) *
      (2 ^ nullity xy L z : ℝ) =
      (2 ^ Module.finrank F₂ ↥(squareClassSpace xy.1 L ⊔ squareClassSpace xy.2 L) : ℝ) *
        (2 ^ (∑ i, Module.finrank F₂ (squareClassSpace (z i) L)) : ℝ) := by
    rw [← pow_add, hdim, pow_add]
  simp_rw [HomogeneousEffectiveWeights.singleton_rank]
  rw [prod_inv_distrib, prod_pow_eq_pow_sum, HomogeneousRunMass.probability_rank,
    HomogeneousRunMass.probability_rank, rank, rank, PaperP1.RetainedNullity.span_pair]
  field_simp
  exact hpower.symm

theorem probability_upper {N L : ℕ} (hN : 0 < N) (xy : ℕ × ℕ) (A : Finset ℕ)
    (hA : A ⊆ dyadicBlock N) (hp : PairPrimitiveCompression.Primitive L {xy.1, xy.2} A) :
    HomogeneousRunMass.probability L ({xy.1, xy.2} ∪ A) ≤
      HomogeneousRunMass.probability L {xy.1, xy.2} *
        (∏ x ∈ A, HomogeneousRunMass.probability L {x}) * (2 ^ L : ℝ) := by
  let z := centres A rfl
  have hz : ∀ i, z i ∈ dyadicBlock N := centres_mem _ A rfl hA
  have hset : tupleSet z = A := centres_tupleSet A rfl
  have hprim := PairCompressedPrimitiveTransport.indexed_primitive xy z (centres_injective A rfl)
    (by rw [hset]; exact hp)
  let i : Fin A.card := ⟨0, (PairPrimitiveCompression.nonempty L {xy.1, xy.2} A hp).card_pos⟩
  have hpos : 0 < z i := hN.trans_le (mem_Ico.mp (hz i)).1
  have hrank := PairCompressedPrimitiveFamilies.primitive_nullity_le xy z hprim i hpos
  have hprod : (∏ i, HomogeneousRunMass.probability L {z i}) =
      ∏ x ∈ A, HomogeneousRunMass.probability L {x} := by
    calc
      _ = ∏ x : A, HomogeneousRunMass.probability L {x.val} :=
        (enumeration A rfl).prod_comp (fun x : A ↦ HomogeneousRunMass.probability L {x.val})
      _ = _ := prod_coe_sort A (fun x : ℕ ↦ HomogeneousRunMass.probability L {x})
  have hfamily : family xy z = {xy.1, xy.2} ∪ A := by
    change {xy.1, xy.2} ∪ tupleSet z = _
    rw [hset]
  rw [← hfamily, factor, hprod]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hrank)
    (mul_nonneg (HomogeneousRunMass.probability_pos L _).le
      (prod_nonneg fun x _ ↦ (HomogeneousRunMass.probability_pos L {x}).le))

theorem point_upper {N L : ℕ} (hN : 0 < N) (xy : ℕ × ℕ) (A : Finset ℕ)
    (hA : A ⊆ dyadicBlock N) (hp : PairPrimitiveCompression.Primitive L {xy.1, xy.2} A)
    (w R : ℝ) (hw : 0 ≤ w) (hR : HomogeneousRunMass.probability L {xy.1, xy.2} ≤ R) :
    w ^ (A.card + 2) * HomogeneousRunMass.probability L ({xy.1, xy.2} ∪ A) ≤
      (w * R * (2 ^ L : ℝ) ^ 2) *
        ((w * (2 ^ L : ℝ)⁻¹) * ∏ x ∈ A, w * HomogeneousRunMass.probability L {x}) := by
  have hprob := (probability_upper hN xy A hA hp).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hR
      (prod_nonneg fun x _ ↦ (HomogeneousRunMass.probability_pos L {x}).le)) (by positivity))
  calc
    _ ≤ w ^ (A.card + 2) *
        (R * (∏ x ∈ A, HomogeneousRunMass.probability L {x}) * (2 ^ L : ℝ)) :=
      mul_le_mul_of_nonneg_left hprob (pow_nonneg hw _)
    _ = _ := by
      rw [prod_mul_distrib, prod_const, pow_add, pow_two]
      field_simp

theorem two_target_factor {L : ℕ} (xy : ℕ × ℕ) (z : Fin 2 → ℕ) (hp : Primitive xy L z) :
    HomogeneousRunMass.probability L (family xy z) =
      HomogeneousRunMass.probability L {xy.1, xy.2} *
        (HomogeneousRunMass.probability L {z 0} * HomogeneousRunMass.probability L {z 1} *
          (2 ^ Module.finrank F₂ (PaperP1.TwoTargetWindowSections.Kernel (z 0) (z 1) L
            (squareClassSpace xy.1 L ⊔ squareClassSpace xy.2 L)) : ℝ)) := by
  rw [factor, Fin.prod_univ_two, (PairCompressedTwoTargetData.primitive_data xy z hp).2.2.2]
  ring

end PaperP1.HomogeneousCompressedEffectiveFactor
