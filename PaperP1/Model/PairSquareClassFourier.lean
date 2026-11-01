module

public import PaperP1.Model.SquareClassFourier
public import PaperP1.Model.InfiniteJointMoments
public import PaperP1.Affine.PairFourierIntersection

/-! # Actual pair covariance as a sum over nonzero common square classes

The local affine witnesses may be chosen separately. No joint compatibility
is imposed, and heterogeneous marginals are retained.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PairSquareClassFourier

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.Algebra PaperP1.PairFourierIntersection

local instance pairSquareClassFourierPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two
local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem full_support_at {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M L : ℕ) (g : ι → ℕ) (hL : 0 < L) (hcut : ∀ i, g i + L ≤ M)
    (a : ι → SampleSpace M) (hstart : ∀ i, startSystem M (g i) L (a i) = startRhs L) :
    infiniteFamilyCenteredMoment L g = (∏ i, infiniteMarginal (g i) L) *
      ∑ s : (i : ι) → squareClassFamilySpace L g i,
        if IsFullSupportRelation (squareClassFamilySpace L g) s then
          squareClassTupleSign M L g a s else 0 := by
  have hp : ∀ i, 0 < infiniteMarginal (g i) L := fun i ↦
    (infiniteMarginal_pos_iff_compatible hL (hcut i)).mpr ⟨a i, hstart i⟩
  rw [squareClass_full_support_formula M L g hL hcut hp]
  congr 1
  apply sum_congr rfl
  intro s _
  by_cases hs : IsFullSupportRelation (squareClassFamilySpace L g) s
  · simp only [ite_eq_left hs, squareClassTupleSign]
    apply prod_congr rfl
    intro i _
    apply squareClassAffineSign_independent_of_solution
    exact (affineWitness_solves _ _ (infiniteAdmissibleCompatibility M L g hL hcut hp i)).trans
      (hstart i).symm
  · simp only [ite_eq_right hs]

def centres (x y : ℕ) : Bool → ℕ
  | false => x
  | true => y

theorem pair_common_formula {M x y L : ℕ} (hL : 0 < L)
    (hcutX : x + L ≤ M) (hcutY : y + L ≤ M) (ωx ωy : SampleSpace M)
    (hstartX : startSystem M x L ωx = startRhs L)
    (hstartY : startSystem M y L ωy = startRhs L) :
    infiniteFamilyCenteredMoment L (centres x y) =
      (infiniteMarginal x L * infiniteMarginal y L) *
        ∑ z : ↥(squareClassSpace x L ⊓ squareClassSpace y L),
          if z ≠ 0 then realCharacter (parityPairing M z.val) ωx *
            realCharacter (parityPairing M z.val) ωy else 0 := by
  let a : Bool → SampleSpace M := fun i ↦ if i then ωy else ωx
  have hcut : ∀ i, centres x y i + L ≤ M := by intro i; cases i <;> assumption
  have hstart : ∀ i, startSystem M (centres x y i) L (a i) = startRhs L := by
    intro i; cases i <;> assumption
  rw [full_support_at M L (centres x y) hL hcut a hstart]
  simp only [Fintype.prod_bool, centres, squareClassTupleSign, a, Bool.false_eq_true, ite_false, ite_true]
  rw [mul_comm (infiniteMarginal y L) (infiniteMarginal x L)]
  congr 1
  have h := full_support_family_sum (squareClassFamilySpace L (centres x y))
    (fun u v ↦ realCharacter (parityPairing M u) ωx * realCharacter (parityPairing M v) ωy)
  convert h using 1
  · apply sum_congr rfl
    intro s _
    split_ifs <;> ring
  · apply Fintype.sum_equiv (Equiv.refl _)
    intro z
    simp only [Equiv.refl_apply]
    by_cases hz : z ≠ 0
    · exact (ite_eq_left hz).trans (ite_eq_left hz).symm
    · exact (ite_eq_right hz).trans (ite_eq_right hz).symm

theorem pair_moment_covariance {x y L : ℕ} (hxy : x ≠ y) :
    infiniteFamilyCenteredMoment L (centres x y) =
      infiniteJointMoment L {x, y} - infiniteMarginal x L * infiniteMarginal y L := by
  have hproduct : infiniteFamilyCenteredMoment L (centres x y) =
      infiniteCenteredCoefficient L {x, y} := by
    unfold infiniteFamilyCenteredMoment infiniteCenteredCoefficient
    congr 1
    funext ω
    simp only [Fintype.prod_bool, centres, prod_pair hxy]
    ring
  rw [hproduct, infiniteCenteredCoefficient_eq_transform (max x y + L) L {x, y}
    (by intro z hz; simp only [mem_insert, mem_singleton] at hz; rcases hz with rfl | rfl <;> omega)]
  apply centeredCoefficient_pair_eq_covariance _ _ hxy
  · exact infiniteJointMoment_empty L
  · simp only [infiniteJointMoment, prod_singleton, infiniteMarginal]
  · simp only [infiniteJointMoment, prod_singleton, infiniteMarginal]

theorem covariance_common_formula {M x y L : ℕ} (hxy : x ≠ y) (hL : 0 < L)
    (hcutX : x + L ≤ M) (hcutY : y + L ≤ M) (ωx ωy : SampleSpace M)
    (hstartX : startSystem M x L ωx = startRhs L)
    (hstartY : startSystem M y L ωy = startRhs L) :
    infiniteJointMoment L {x, y} - infiniteMarginal x L * infiniteMarginal y L =
      (infiniteMarginal x L * infiniteMarginal y L) *
        ∑ z : ↥(squareClassSpace x L ⊓ squareClassSpace y L),
          if z ≠ 0 then realCharacter (parityPairing M z.val) ωx *
            realCharacter (parityPairing M z.val) ωy else 0 := by
  rw [← pair_moment_covariance hxy]
  exact pair_common_formula hL hcutX hcutY ωx ωy hstartX hstartY

end PaperP1.PairSquareClassFourier
