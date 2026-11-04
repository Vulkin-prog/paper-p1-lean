module

public import PaperP1.Model.SignedMaximalFootprint
public import PaperP1.Model.SignedTypeWeightSums
public import PaperP1.Model.SignedLocalJointMass

/-! # The full signed cost is bounded after summing all heterogeneous type weights -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SignedCostEnvelope

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.SignedPrivateField
  PaperP1.SignedMaximalFootprint PaperP1.SignedExactWords PaperP1.Probability

local instance (P : Prop) : Decidable P := Classical.propDecidable P

variable {M Y L E : ℕ} {J : Finset ℕ}

def Close (L E j k : ℕ) : Prop := j < k + (L + E + 2) ∧ k < j + (L + E + 2)

def envelope (D : Data M Y L E J) (j k : J) : ℝ :=
  (if j = k then 1 else 0) + 2 * (if k ∈ siteFootprint D j then 1 else 0) +
    4 * (if Close L E j.val k.val then 1 else 0) +
      (if Close L E j.val k.val then 0 else
        (2 ^ RawPairRelationRank.fullRank (j.val + 1) (k.val + 1) (L + E + 1) : ℝ) - 1)

theorem envelope_nonneg (D : Data M Y L E J) (j k : J) : 0 ≤ envelope D j k := by
  have hp : (1 : ℝ) ≤ 2 ^ RawPairRelationRank.fullRank (j.val + 1) (k.val + 1) (L + E + 1) :=
    one_le_pow₀ (by norm_num)
  unfold envelope
  split_ifs <;> linarith only [hp]

theorem envelope_diagonal (D : Data M Y L E J) (j : J) : 1 ≤ envelope D j j := by
  have hc : Close L E j.val j.val := by constructor <;> omega
  simp only [envelope, ite_eq_left hc]
  split_ifs <;> norm_num

theorem offsite_bound (D : Data M Y L E J) (hY : 2 * (L + E + 2) ≤ Y)
    (a b : Index J E) (hb : b ∈ (univ.erase a) ∩ footprint D a) :
    signedMarkRate L a.2.1.val * signedMarkRate L b.2.1.val +
      ForcingCoordinateCost.joint (cylinderProbability M) (indicator M L) a b ≤
        signedMarkRate L a.2.1.val * signedMarkRate L b.2.1.val * envelope D a.1 b.1 := by
  have hab : a ≠ b := (mem_erase.mp (mem_inter.mp hb).1).1.symm
  have hhit := actual_subset D a b (mem_inter.mp hb).2
  have hr : 0 ≤ signedMarkRate L a.2.1.val * signedMarkRate L b.2.1.val :=
    mul_nonneg (signedMarkRate_pos _ _).le (signedMarkRate_pos _ _).le
  have hd : (0 : ℝ) ≤ if a.1 = b.1 then 1 else 0 := by split_ifs <;> norm_num
  by_cases hc : Close L E a.1.val b.1.val
  · have hj := SignedLocalJointMass.joint_le_four_of_close D hY a b hab hc.1 hc.2
    simp only [envelope, ite_eq_left hhit, ite_eq_left hc]
    nlinarith only [hj, hr, mul_nonneg hr hd]
  · have hj := SignedRawJointMass.joint_le_maximal D a b
    simp only [envelope, ite_eq_left hhit, ite_eq_right hc]
    nlinarith only [hj, hr, mul_nonneg hr hd]

theorem cost_le_envelope (D : Data M Y L E J) (hY : 2 * (L + E + 2) ≤ Y) :
    cost D ≤ ((2 ^ L : ℝ)⁻¹) ^ 2 * (∑ j : J, ∑ k : J, envelope D j k) := by
  have hnon (a b : Index J E) :
      0 ≤ signedMarkRate L a.2.1.val * signedMarkRate L b.2.1.val * envelope D a.1 b.1 :=
    mul_nonneg (mul_nonneg (signedMarkRate_pos _ _).le (signedMarkRate_pos _ _).le)
      (envelope_nonneg D _ _)
  have hone (a : Index J E) : (signedMarkRate L a.2.1.val) ^ 2 +
      (∑ b ∈ (univ.erase a) ∩ footprint D a,
        (signedMarkRate L a.2.1.val * signedMarkRate L b.2.1.val +
          ForcingCoordinateCost.joint (cylinderProbability M) (indicator M L) a b)) ≤
      ∑ b : Index J E,
        signedMarkRate L a.2.1.val * signedMarkRate L b.2.1.val * envelope D a.1 b.1 := by
    have hs : (∑ b ∈ (univ.erase a) ∩ footprint D a,
        (signedMarkRate L a.2.1.val * signedMarkRate L b.2.1.val +
          ForcingCoordinateCost.joint (cylinderProbability M) (indicator M L) a b)) ≤
        ∑ b ∈ univ.erase a,
          signedMarkRate L a.2.1.val * signedMarkRate L b.2.1.val * envelope D a.1 b.1 := by
      calc
        _ ≤ ∑ b ∈ (univ.erase a) ∩ footprint D a,
            signedMarkRate L a.2.1.val * signedMarkRate L b.2.1.val * envelope D a.1 b.1 :=
          sum_le_sum (fun b hb ↦ offsite_bound D hY a b hb)
        _ ≤ _ := sum_le_sum_of_subset_of_nonneg inter_subset_left (fun b _ _ ↦ hnon a b)
    have hd : (signedMarkRate L a.2.1.val) ^ 2 ≤
        (signedMarkRate L a.2.1.val) ^ 2 * envelope D a.1 a.1 := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (envelope_diagonal D a.1)
        (sq_nonneg (signedMarkRate L a.2.1.val))
    calc
      _ ≤ (signedMarkRate L a.2.1.val) ^ 2 * envelope D a.1 a.1 +
          ∑ b ∈ univ.erase a,
            signedMarkRate L a.2.1.val * signedMarkRate L b.2.1.val * envelope D a.1 b.1 :=
        add_le_add hd hs
      _ = _ := by
        simpa only [pow_two] using add_sum_erase univ
          (fun b : Index J E ↦ signedMarkRate L a.2.1.val * signedMarkRate L b.2.1.val * envelope D a.1 b.1)
          (mem_univ a)
  calc
    _ ≤ _ := cost_footprint_upper D
    _ = ∑ a : Index J E, ((signedMarkRate L a.2.1.val) ^ 2 +
        ∑ b ∈ (univ.erase a) ∩ footprint D a,
          (signedMarkRate L a.2.1.val * signedMarkRate L b.2.1.val +
            ForcingCoordinateCost.joint (cylinderProbability M) (indicator M L) a b)) :=
      sum_add_distrib.symm
    _ ≤ ∑ a : Index J E, ∑ b : Index J E,
        signedMarkRate L a.2.1.val * signedMarkRate L b.2.1.val * envelope D a.1 b.1 :=
      sum_le_sum (fun a _ ↦ hone a)
    _ ≤ _ := SignedTypeWeightSums.sum_pairs_le L E (envelope D) (envelope_nonneg D)

end PaperP1.SignedCostEnvelope
