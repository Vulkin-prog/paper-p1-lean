module

public import PaperP1.Model.RawKernelRestriction
public import PaperP1.Model.SignedPrivateField
public import PaperP1.Arithmetic.RawPairRelationRank
public import Mathlib.Data.Fin.Embedding

/-! # Actual unequal signed words are bounded by the maximal unrestricted raw kernel -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SignedRawJointMass

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Affine PaperP1.PrivateValueSystem
  PaperP1.SignedExactWords PaperP1.SignedPrivateField PaperP1.Probability

local instance (P : Prop) : Decidable P := Classical.propDecidable P

def values (j k S T : ℕ) : Fin S ⊕ Fin T → ℕ :=
  Sum.elim (fun i ↦ j + i.val) (fun i ↦ k + i.val)

theorem kernel_le_maximal {j k S T Q : ℕ} (hS : S ≤ Q + 1) (hT : T ≤ Q + 1) :
    Module.finrank F₂ (LinearMap.ker (RawValueLaw.columnMap (values j k S T))) ≤
      RawPairRelationRank.fullRank (j + 1) (k + 1) Q := by
  let e : Fin S ⊕ Fin T ↪ Fin (Q + 1) ⊕ Fin (Q + 1) :=
    Function.Embedding.sumMap (Fin.castLEEmb hS) (Fin.castLEEmb hT)
  have hh : ∀ i, twoStartCompleteVertexLabel (j + 1) (k + 1) Q (e i) = values j k S T i := by
    intro i
    cases i with
    | inl i => simp [e, values, twoStartCompleteVertexLabel,
        startCompleteVertexLabel_eq_offset (by omega : 0 < j + 1)]
    | inr i => simp [e, values, twoStartCompleteVertexLabel,
        startCompleteVertexLabel_eq_offset (by omega : 0 < k + 1)]
  exact RawKernelRestriction.finrank_le e _ _ hh

variable {M Y L E : ℕ} {J : Finset ℕ}

theorem joint_eq_mass (D : Data M Y L E J) (a b : Index J E) :
    ForcingCoordinateCost.joint (cylinderProbability M) (indicator M L) a b =
      uniformSolutionMass
        (valueSystem M (values a.1.val b.1.val (L + a.2.1.val + 2) (L + b.2.1.val + 2)))
        (Sum.elim (signedExactWord L a.2.1.val a.2.2) (signedExactWord L b.2.1.val b.2.2)) := by
  have hevent (ω : SampleSpace M) :
      valueSystem M (values a.1.val b.1.val (L + a.2.1.val + 2) (L + b.2.1.val + 2)) ω =
        Sum.elim (signedExactWord L a.2.1.val a.2.2) (signedExactWord L b.2.1.val b.2.2) ↔
      SignedExactMark (valueBit ω) (a.1.val + 1) L a.2.1.val a.2.2 ∧
        SignedExactMark (valueBit ω) (b.1.val + 1) L b.2.1.val b.2.2 := by
    rw [← finite_signedWord_iff D.length_pos, ← finite_signedWord_iff D.length_pos]
    constructor
    · intro h
      exact ⟨funext (fun i ↦ congrFun h (Sum.inl i)), funext (fun i ↦ congrFun h (Sum.inr i))⟩
    · rintro ⟨ha, hb⟩
      funext i
      cases i with
      | inl i => exact congrFun ha i
      | inr i => exact congrFun hb i
  unfold ForcingCoordinateCost.joint uniformSolutionMass
  congr 1
  funext ω
  rw [hevent]
  by_cases ha : SignedExactMark (valueBit ω) (a.1.val + 1) L a.2.1.val a.2.2
  all_goals
    by_cases hb : SignedExactMark (valueBit ω) (b.1.val + 1) L b.2.1.val b.2.2
    all_goals simp [indicator, indicatorValue, ha, hb]

theorem joint_le_maximal (D : Data M Y L E J) (a b : Index J E) :
    ForcingCoordinateCost.joint (cylinderProbability M) (indicator M L) a b ≤
      signedMarkRate L a.2.1.val * signedMarkRate L b.2.1.val *
        (2 ^ RawPairRelationRank.fullRank (a.1.val + 1) (b.1.val + 1) (L + E + 1) : ℝ) := by
  let v := values a.1.val b.1.val (L + a.2.1.val + 2) (L + b.2.1.val + 2)
  have hp : ∀ i, 0 < v i := by
    intro i
    cases i with
    | inl i => dsimp [v, values]; have := D.boundary_pos a.1.val a.1.property; omega
    | inr i => dsimp [v, values]; have := D.boundary_pos b.1.val b.1.property; omega
  have hc : ∀ i, v i ≤ M := by
    intro i
    cases i with
    | inl i => dsimp [v, values]; have := actual_cutoff D a; have := i.isLt; omega
    | inr i => dsimp [v, values]; have := actual_cutoff D b; have := i.isLt; omega
  rw [joint_eq_mass D a b]
  have hm := RawValueLaw.mass_le v hp hc
    (Sum.elim (signedExactWord L a.2.1.val a.2.2) (signedExactWord L b.2.1.val b.2.2))
  simp only [Fintype.card_sum, Fintype.card_fin] at hm
  have hr := kernel_le_maximal
    (j := a.1.val) (k := b.1.val)
    (by have := a.2.1.isLt; omega : L + a.2.1.val + 2 ≤ L + E + 1 + 1)
    (by have := b.2.1.isLt; omega : L + b.2.1.val + 2 ≤ L + E + 1 + 1)
  have hw := pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hr
  have hden : (0 : ℝ) < 2 ^ ((L + a.2.1.val + 2) + (L + b.2.1.val + 2)) := by positivity
  have ht := hm.trans (div_le_div_of_nonneg_right hw hden.le)
  simpa only [v, pow_add, div_eq_mul_inv,
    mul_inv_rev, signedMarkRate, mul_assoc, mul_comm, mul_left_comm] using ht

end PaperP1.SignedRawJointMass
