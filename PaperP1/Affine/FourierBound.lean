module

public import PaperP1.Affine.RelativeNullity
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# The full-support centered bound

The signed character sum is bounded by its number of terms. For a nonempty
family, all these terms belong to the relative-relation kernel with its zero
tuple removed. This gives the sharper factor `2^ρ - 1` and existence of a
relation meeting every block whenever the centered moment is nonzero.
-/

@[expose] public noncomputable section

open scoped BigOperators
open PaperP1.Algebra PaperP1.Probability

namespace PaperP1.Affine

local instance (P : Prop) : Decidable P := Classical.propDecidable P
local instance : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

variable {V ι : Type*} [AddCommGroup V] [Module 𝔽₂ V]
variable [Fintype ι] [DecidableEq ι]
variable (S : ι → Submodule 𝔽₂ (V →ₗ[𝔽₂] 𝔽₂)) [∀ i, Fintype (S i)]

omit [DecidableEq ι] [∀ i, Fintype (S i)] in
theorem abs_affineTupleSign (a : ι → V) (s : (i : ι) → S i) :
    |affineTupleSign S a s| = 1 := by
  simp [affineTupleSign, Finset.abs_prod, abs_realCharacter]

omit [DecidableEq ι] in
theorem effectiveRate_product_nonneg : 0 ≤ ∏ i, effectiveRate (S i) := by
  exact Finset.prod_nonneg fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _)

theorem abs_full_support_sum_le_card (a : ι → V) :
    |∑ s : (i : ι) → S i,
        if IsFullSupportRelation S s then affineTupleSign S a s else 0| ≤
      ((fullSupportRelations S).card : ℝ) := by
  classical
  change |∑ s ∈ Finset.univ, if IsFullSupportRelation S s then _ else 0| ≤ _
  rw [← Finset.sum_filter]
  calc
    _ ≤ ∑ s ∈ fullSupportRelations S, |affineTupleSign S a s| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = _ := by simp [abs_affineTupleSign]

theorem abs_full_support_sum_bound [Nonempty ι] (a : ι → V) :
    |∑ s : (i : ι) → S i,
        if IsFullSupportRelation S s then affineTupleSign S a s else 0| ≤
      (2 ^ relativeNullity S : ℝ) - 1 := by
  refine (abs_full_support_sum_le_card S a).trans ?_
  have hp : 1 ≤ 2 ^ relativeNullity S := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have h := Nat.cast_le (α := ℝ).mpr (card_fullSupportRelations_le S)
  simpa only [Nat.cast_sub hp, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one] using h

variable [Fintype V]

def effectiveCenteredMoment (a : ι → V) : ℝ :=
  finiteExpectation (uniformFiniteProbability V).weight
    (fun v => ∏ i, (effectiveIndicator (S i) (a i) v - effectiveRate (S i)))

theorem effectiveCenteredMoment_bound [Nonempty ι] (a : ι → V) :
    |effectiveCenteredMoment S a| ≤
      (∏ i, effectiveRate (S i)) * ((2 ^ relativeNullity S : ℝ) - 1) := by
  rw [effectiveCenteredMoment, effective_full_support_formula, abs_mul,
    abs_of_nonneg (effectiveRate_product_nonneg S)]
  exact mul_le_mul_of_nonneg_left (abs_full_support_sum_bound S a)
    (effectiveRate_product_nonneg S)

theorem effectiveCenteredMoment_coarse_bound [Nonempty ι] (a : ι → V) :
    |effectiveCenteredMoment S a| ≤
      (∏ i, effectiveRate (S i)) * (2 ^ relativeNullity S : ℝ) := by
  refine (effectiveCenteredMoment_bound S a).trans ?_
  exact mul_le_mul_of_nonneg_left (sub_le_self _ zero_le_one)
    (effectiveRate_product_nonneg S)

theorem fullSupportRelation_of_centeredMoment_ne_zero (a : ι → V)
    (hc : effectiveCenteredMoment S a ≠ 0) :
    ∃ s : (i : ι) → S i, IsFullSupportRelation S s := by
  classical
  by_contra hn
  push Not at hn
  have hsum : (∑ s : (i : ι) → S i,
      if IsFullSupportRelation S s then affineTupleSign S a s else 0) = 0 := by
    exact Finset.sum_eq_zero fun s _ => ite_eq_right (hn s)
  apply hc
  rw [effectiveCenteredMoment, effective_full_support_formula, hsum, mul_zero]

end PaperP1.Affine
