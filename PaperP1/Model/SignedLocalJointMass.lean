module

public import PaperP1.Model.RawPrivateSelectedValues
public import PaperP1.Model.SignedMarkLocalGeometry
public import PaperP1.Model.SignedRawJointMass

/-! # Close distinct signed marks cost at most four times their exact marginal product -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SignedLocalJointMass

open Finset PaperP1.Algebra PaperP1.Arithmetic PaperP1.Model PaperP1.Affine PaperP1.PrivateValueSystem
  PaperP1.SignedExactWords PaperP1.SignedPrivateField PaperP1.Probability
  PaperP1.SignedMarkLocalGeometry PaperP1.OddPrimePivot

local instance (P : Prop) : Decidable P := Classical.propDecidable P

variable {M Y L E : ℕ} {J : Finset ℕ}

theorem joint_comm (a b : Index J E) :
    ForcingCoordinateCost.joint (cylinderProbability M) (indicator M L) a b =
      ForcingCoordinateCost.joint (cylinderProbability M) (indicator M L) b a := by
  unfold ForcingCoordinateCost.joint
  congr 1
  funext ω
  exact mul_comm _ _

theorem joint_zero_of_incompatible (a b : Index J E)
    (h : ∀ ω : SampleSpace M, ¬ (SignedExactMark (valueBit ω) (a.1.val + 1) L a.2.1.val a.2.2 ∧
      SignedExactMark (valueBit ω) (b.1.val + 1) L b.2.1.val b.2.2)) :
    ForcingCoordinateCost.joint (cylinderProbability M) (indicator M L) a b = 0 := by
  unfold ForcingCoordinateCost.joint
  have hz : (fun ω : SampleSpace M ↦ indicatorValue (indicator M L a ω) *
      indicatorValue (indicator M L b ω)) = fun _ ↦ (0 : ℝ) := by
    funext ω
    by_cases ha : SignedExactMark (valueBit ω) (a.1.val + 1) L a.2.1.val a.2.2
    · have hb : ¬ SignedExactMark (valueBit ω) (b.1.val + 1) L b.2.1.val b.2.2 :=
        fun hb ↦ h ω ⟨ha, hb⟩
      simp [indicator, indicatorValue, hb]
    · simp [indicator, indicatorValue, ha]
  rw [hz]
  simp [finiteExpectation]

theorem joint_zero_same_boundary (a b : Index J E) (hab : a ≠ b) (hsite : a.1 = b.1) :
    ForcingCoordinateCost.joint (cylinderProbability M) (indicator M L) a b = 0 := by
  apply joint_zero_of_incompatible
  rintro ω ⟨ha, hb⟩
  rw [← hsite] at hb
  obtain ⟨he, hs⟩ := type_unique ha hb
  apply hab
  exact Prod.ext hsite (Prod.ext (Fin.ext he) hs)

theorem ordered_joint_le_four (D : Data M Y L E J) (hY : 2 * (L + E + 2) ≤ Y)
    (a b : Index J E) (horder : a.1.val < b.1.val)
    (hnear : b.1.val < a.1.val + (L + E + 2)) :
    ForcingCoordinateCost.joint (cylinderProbability M) (indicator M L) a b ≤
      4 * signedMarkRate L a.2.1.val * signedMarkRate L b.2.1.val := by
  by_cases hgap : a.1.val + (L + a.2.1.val) ≤ b.1.val
  · let f := trimmedPositions horder.le (by omega : a.1.val + (L + a.2.1.val + 2) ≤ b.1.val + 2)
      hnear (by have := a.2.1.isLt; omega : L + a.2.1.val + 2 ≤ L + E + 2)
      (by have := b.2.1.isLt; omega : L + b.2.1.val + 2 ≤ L + E + 2)
    let v := fun i ↦ a.1.val + (f i).val
    let w : Fin (L + a.2.1.val + 2) ⊕ Fin (L + b.2.1.val) → F₂ :=
      Sum.elim (signedExactWord L a.2.1.val a.2.2)
        (fun i ↦ signedExactWord L b.2.1.val b.2.2 ⟨i.val + 2, by have := i.isLt; omega⟩)
    have hv (i) : v i = Sum.elim (fun i : Fin (L + a.2.1.val + 2) ↦ a.1.val + i.val)
        (fun i : Fin (L + b.2.1.val) ↦ b.1.val + 2 + i.val) i :=
      trimmed_value _ _ _ _ _ i
    have hc : ∀ i, v i ≤ M := by
      intro i
      rw [hv]
      cases i with
      | inl i => dsimp; have := actual_cutoff D a; have := i.isLt; omega
      | inr i => dsimp; have := actual_cutoff D b; have := i.isLt; omega
    have hg : ∀ i, Y < largestOddPrime (v i) := by
      intro i
      rw [hv]
      cases i with
      | inl i => exact actual_good D a i
      | inr i =>
        have hh := actual_good D b (⟨i.val + 2, by have := i.isLt; omega⟩ : Fin (L + b.2.1.val + 2))
        simpa only [Sum.elim_inr, Nat.add_assoc, Nat.add_comm 2] using hh
    have hm := RawPrivateSelectedValues.mass_le f (D.boundary_pos a.1.val a.1.property) hc
      (by intro i; change 1 < largestOddPrime (v i); have := hg i; have := D.length_pos; omega)
      (by intro i; exact hY.trans (hg i).le) w
    have hmono : ForcingCoordinateCost.joint (cylinderProbability M) (indicator M L) a b ≤
        uniformSolutionMass (valueSystem M v) w := by
      unfold ForcingCoordinateCost.joint uniformSolutionMass
      apply finiteExpectation_mono (cylinderProbability M)
      intro ω
      by_cases ha : SignedExactMark (valueBit ω) (a.1.val + 1) L a.2.1.val a.2.2
      · by_cases hb : SignedExactMark (valueBit ω) (b.1.val + 1) L b.2.1.val b.2.2
        · have hw : valueSystem M v ω = w := by
            funext i
            change valueBit ω (v i) = w i
            rw [hv]
            cases i with
            | inl i => exact congrFun ((finite_signedWord_iff D.length_pos _ ω).mpr ha) i
            | inr i =>
              have hh := congrFun ((finite_signedWord_iff D.length_pos _ ω).mpr hb)
                (⟨i.val + 2, by have := i.isLt; omega⟩ : Fin (L + b.2.1.val + 2))
              simpa only [valueSystem_apply, w, Sum.elim_inr, Nat.add_assoc, Nat.add_comm 2] using hh
          simp [indicator, indicatorValue, ha, hb, hw]
        · simp [indicator, indicatorValue, hb]
          split <;> norm_num
      · simp [indicator, indicatorValue, ha]
        split <;> norm_num
    have h := hmono.trans hm
    have he : (L + a.2.1.val + 2) + (L + b.2.1.val + 2) =
        ((L + a.2.1.val + 2) + (L + b.2.1.val)) + 2 := by omega
    have hnorm : (2 ^ Fintype.card (Fin (L + a.2.1.val + 2) ⊕ Fin (L + b.2.1.val)) : ℝ)⁻¹ =
        4 * signedMarkRate L a.2.1.val * signedMarkRate L b.2.1.val := by
      simp only [Fintype.card_sum, Fintype.card_fin, signedMarkRate]
      rw [mul_assoc (4 : ℝ), ← mul_inv, ← pow_add, he,
        pow_add (2 : ℝ) ((L + a.2.1.val + 2) + (L + b.2.1.val)) 2]
      norm_num
      ring
    rwa [hnorm] at h
  · rw [joint_zero_of_incompatible a b (fun ω h ↦ hgap (ordered_gap horder h.1 h.2))]
    exact mul_nonneg (mul_nonneg (by norm_num) (signedMarkRate_pos _ _).le) (signedMarkRate_pos _ _).le

theorem joint_le_four_of_close (D : Data M Y L E J) (hY : 2 * (L + E + 2) ≤ Y)
    (a b : Index J E) (hab : a ≠ b)
    (hleft : a.1.val < b.1.val + (L + E + 2))
    (hright : b.1.val < a.1.val + (L + E + 2)) :
    ForcingCoordinateCost.joint (cylinderProbability M) (indicator M L) a b ≤
      4 * signedMarkRate L a.2.1.val * signedMarkRate L b.2.1.val := by
  rcases lt_trichotomy a.1.val b.1.val with h | h | h
  · exact ordered_joint_le_four D hY a b h hright
  · rw [joint_zero_same_boundary a b hab (Subtype.ext h)]
    exact mul_nonneg (mul_nonneg (by norm_num) (signedMarkRate_pos _ _).le) (signedMarkRate_pos _ _).le
  · rw [joint_comm a b]
    have hh := ordered_joint_le_four D hY b a h hleft
    nlinarith only [hh]

end PaperP1.SignedLocalJointMass
