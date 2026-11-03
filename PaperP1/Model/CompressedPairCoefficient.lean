module

public import PaperP1.Model.PairPrimitiveCompression
public import PaperP1.Model.HeterogeneousDirectMaximum
public import PaperP1.Model.CompressedJointMoments
public import PaperP1.Model.DependentPairJointActivity

/-! # The actual centered compressed-pair coefficient, including incompatible and zero-marginal cases -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CompressedPairCoefficient

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Algebra PaperP1.Probability
  PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.PairPrimitiveCompression

/-- Center the source indicator as one block, and center each target at its own exact marginal. -/
def value (L : ℕ) (e A : Finset ℕ) : ℝ :=
  ∑ B ∈ A.powerset, (-1 : ℝ) ^ (A.card - B.card) *
    (infiniteJointMoment L (e ∪ B) - infiniteJointMoment L e * infiniteJointMoment L B) *
      ∏ x ∈ A \ B, infiniteMarginal x L

theorem zero_joint (L : ℕ) (I : Finset ℕ) (x : ℕ) (hx : x ∈ I) (hz : infiniteMarginal x L = 0) :
    infiniteJointMoment L I = 0 := by
  have h := MissingBlockProbabilities.infiniteJointMoment_antitone L (singleton_subset_iff.mpr hx)
  rw [InfiniteTripleCancellation.singleton_joint, hz] at h
  exact le_antisymm h (infiniteJointMoment_nonneg L I)

theorem compressed_joint_factor (L : ℕ) (hL : 0 < L) (e A : Finset ℕ) (he : e.card = 2)
    (hdis : Disjoint e A) (hz : nullity L e A = 0) :
    infiniteJointMoment L (e ∪ A) = infiniteJointMoment L e * ∏ x ∈ A, infiniteMarginal x L := by
  classical
  have hcomp := (MinimalRelativeRelations.zero_iff_compressed (fun x ↦ squareClassSpace x L) e A hdis).mp hz
  by_cases hp : ∀ x ∈ e ∪ A, 0 < infiniteMarginal x L
  · have h := CompressedJointMoments.compressed_joint_factor L hL e (e ∪ A) he hp hcomp
    have hdiff : (e ∪ A) \ e = A := union_sdiff_cancel_left hdis
    simpa only [hdiff] using h
  · push Not at hp
    obtain ⟨x, hx, hnp⟩ := hp
    have hzero : infiniteMarginal x L = 0 := le_antisymm hnp
      (MissingBlockProbabilities.infiniteMarginal_nonneg x L)
    rw [zero_joint L (e ∪ A) x hx hzero]
    rcases mem_union.mp hx with hxe | hxa
    · rw [zero_joint L e x hxe hzero, zero_mul]
    · rw [prod_eq_zero hxa hzero, mul_zero]

theorem primitive_identity (L : ℕ) (hL : 0 < L) (e A : Finset ℕ) (he : e.card = 2)
    (h : Primitive L e A) :
    value L e A = infiniteJointMoment L (e ∪ A) - infiniteJointMoment L e * ∏ x ∈ A, infiniteMarginal x L := by
  classical
  rw [value]
  have hA := HeterogeneousDirectMaximum.direct_joint_factor L hL A h.2.1
  calc
    _ = (-1 : ℝ) ^ (A.card - A.card) *
        (infiniteJointMoment L (e ∪ A) - infiniteJointMoment L e * infiniteJointMoment L A) *
          ∏ x ∈ A \ A, infiniteMarginal x L := by
      apply sum_eq_single A
      · intro B hB hne
        have hBA : B ⊂ A := Finset.ssubset_iff_subset_ne.mpr ⟨mem_powerset.mp hB, hne⟩
        have hdis : Disjoint e B := h.1.mono_right (mem_powerset.mp hB)
        have hdirect : runRelativeNullity L B = 0 := by
          have hm := relativeNullityOn_mono (fun x ↦ squareClassSpace x L) (mem_powerset.mp hB)
          change runRelativeNullity L B ≤ runRelativeNullity L A at hm
          have hz := h.2.1
          omega
        rw [compressed_joint_factor L hL e B he hdis (h.2.2.2 B hBA),
          HeterogeneousDirectMaximum.direct_joint_factor L hL B hdirect, sub_self, mul_zero, zero_mul]
      · simp
    _ = _ := by simp only [Nat.sub_self, pow_zero, one_mul, sdiff_self, bot_eq_empty, prod_empty, mul_one, hA]

theorem primitive_abs_bound (L : ℕ) (hL : 0 < L) (e A : Finset ℕ) (he : e.card = 2)
    (h : Primitive L e A) :
    |value L e A| ≤ infiniteJointMoment L (e ∪ A) + infiniteJointMoment L e * ∏ x ∈ A, infiniteMarginal x L := by
  rw [primitive_identity L hL e A he h]
  exact (abs_sub _ _).trans_eq (by rw [abs_of_nonneg (infiniteJointMoment_nonneg L (e ∪ A)),
    abs_of_nonneg (mul_nonneg (infiniteJointMoment_nonneg L e)
      (prod_nonneg fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L))])

theorem finite_interpretation (M L : ℕ) (e A : Finset ℕ) (hdis : Disjoint e A)
    (hcut : ∀ x ∈ e ∪ A, x + L ≤ M) :
    value L e A = finiteExpectation (cylinderProbability M).weight (fun ω ↦
      ((∏ x ∈ e, (indicatorValue (startIndicator x L ω) : ℝ)) - infiniteJointMoment L e) *
        ∏ x ∈ A, ((indicatorValue (startIndicator x L ω) : ℝ) - infiniteMarginal x L)) := by
  classical
  simp_rw [centered_product_inclusion_exclusion, mul_sum]
  rw [finiteExpectation_sum]
  unfold value
  apply sum_congr rfl
  intro B hB
  have hBA := mem_powerset.mp hB
  have hdisB := hdis.mono_right hBA
  have hcutB : ∀ x ∈ B, x + L ≤ M := fun x hx ↦ hcut x (mem_union_right e (hBA hx))
  have hcutE : ∀ x ∈ e, x + L ≤ M := fun x hx ↦ hcut x (mem_union_left A hx)
  have hcutEB : ∀ x ∈ e ∪ B, x + L ≤ M := fun x hx ↦ by
    rcases mem_union.mp hx with hx | hx
    · exact hcutE x hx
    · exact hcutB x hx
  rw [infiniteJointMoment_eq_finite M L (e ∪ B) hcutEB, infiniteJointMoment_eq_finite M L B hcutB]
  change _ = finiteExpectation (cylinderProbability M).weight _
  calc
    _ = finiteExpectation (cylinderProbability M).weight (fun ω ↦
        (-1 : ℝ) ^ (A.card - B.card) *
          (((∏ x ∈ e, (indicatorValue (startIndicator x L ω) : ℝ))) *
            (∏ x ∈ B, (indicatorValue (startIndicator x L ω) : ℝ)) -
              infiniteJointMoment L e * ∏ x ∈ B, (indicatorValue (startIndicator x L ω) : ℝ)) *
                ∏ x ∈ A \ B, infiniteMarginal x L) := by
      rw [finiteExpectation_mul_const, finiteExpectation_const_mul, finiteExpectation_sub,
        finiteExpectation_const_mul]
      congr 2
      unfold finiteJointMoment
      simp_rw [prod_union hdisB]
    _ = _ := by congr 1; funext ω; ring

end PaperP1.CompressedPairCoefficient
