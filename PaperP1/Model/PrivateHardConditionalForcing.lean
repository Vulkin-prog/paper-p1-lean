/-
Adapted from Vulkin-prog/paper-c-lean, PaperCPrel8/HardConditionalForcing.lean,
commit b9fa9ba490f201b408a302a86f1594ee620b228b, Apache-2.0,
Git blob b0023a3aa605913a42c03124dc87565ff74115e3.
Changes: actual P1 normalized averages and the existing P1 small-prime trace.
Positive conditioning-event mass is retained explicitly in the main theorem.
-/
module

public import PaperP1.Model.PrivatePrimeForcing
public import PaperP1.Model.SmallPrimeConditioning

/-! # Full private-forcing laws after actual small-prime conditioning

The weight may be any function of the entire small-prime trace, including a
soft tilt. An arbitrary positive-probability event of that trace is allowed.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrivateHardConditionalForcing

open PaperP1.Arithmetic PaperP1.Model PaperP1.PrivateValueSystem
  PaperP1.PrivatePivotGeometry PaperP1.PrivatePrimeForcing PaperP1.UniformFubini
  PaperP1.SmallPrimeConditioning

local instance privateHardConditionalForcingDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

variable {M Y : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem smallTrace_unchanged (v : ι → ℕ) (q : ι → PrimeUpTo M)
    (hqY : ∀ a, Y < (q a).val.val) (word : ι → F₂) (ω : SampleSpace M) :
    smallBits M Y (forceWord v q word ω) = smallBits M Y ω := by
  funext p
  exact forceWord_preserves_small v q word ω Y hqY p.val p.property

theorem weighted_conditional_identity (v : ι → ℕ) (q : ι → PrimeUpTo M)
    (hq : ∀ a, valueSystem M v (Pi.single (q a) 1) = Pi.single a 1)
    (hqY : ∀ a, Y < (q a).val.val) (word : ι → F₂)
    (weight : ({p : PrimeUpTo M // p.val.val ≤ Y} → F₂) → ℝ)
    (f : SampleSpace M → ℝ) :
    average (fun ω ↦ weight (smallBits M Y ω) * f (forceWord v q word ω)) =
      average (fun ω ↦ if valueSystem M v ω = word then
        weight (smallBits M Y ω) * f ω else 0) / (Fintype.card (ι → F₂) : ℝ)⁻¹ := by
  have h := uniform_conditional_expectation v q hq word
    (fun ω ↦ weight (smallBits M Y ω) * f ω)
  simpa only [smallTrace_unchanged v q hqY] using h

theorem word_small_event_probability (v : ι → ℕ) (q : ι → PrimeUpTo M)
    (hq : ∀ a, valueSystem M v (Pi.single (q a) 1) = Pi.single a 1)
    (hqY : ∀ a, Y < (q a).val.val) (word : ι → F₂)
    (A : ({p : PrimeUpTo M // p.val.val ≤ Y} → F₂) → Prop) :
    average (fun ω ↦ if A (smallBits M Y ω) ∧ valueSystem M v ω = word then (1 : ℝ) else 0) =
      average (fun ω ↦ if A (smallBits M Y ω) then (1 : ℝ) else 0) *
        (Fintype.card (ι → F₂) : ℝ)⁻¹ := by
  have h := weighted_conditional_identity v q hq hqY word
    (fun s ↦ if A s then 1 else 0) (fun _ ↦ 1)
  simp only [mul_one] at h
  have he : (fun ω : SampleSpace M ↦ if valueSystem M v ω = word then
      (if A (smallBits M Y ω) then (1 : ℝ) else 0) else 0) =
      (fun ω ↦ if A (smallBits M Y ω) ∧ valueSystem M v ω = word then 1 else 0) := by
    funext ω
    split_ifs <;> simp_all
  rw [he] at h
  have hc : (Fintype.card (ι → F₂) : ℝ)⁻¹ ≠ 0 :=
    inv_ne_zero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  exact ((eq_div_iff hc).mp h).symm

theorem hard_conditional_expectation (v : ι → ℕ) (q : ι → PrimeUpTo M)
    (hq : ∀ a, valueSystem M v (Pi.single (q a) 1) = Pi.single a 1)
    (hqY : ∀ a, Y < (q a).val.val) (word : ι → F₂)
    (A : ({p : PrimeUpTo M // p.val.val ≤ Y} → F₂) → Prop)
    (hA : 0 < average (fun ω ↦ if A (smallBits M Y ω) then (1 : ℝ) else 0))
    (f : SampleSpace M → ℝ) :
    (0 < average (fun ω ↦
      if A (smallBits M Y ω) ∧ valueSystem M v ω = word then (1 : ℝ) else 0)) ∧
    average (fun ω ↦ if A (smallBits M Y ω) then f (forceWord v q word ω) else 0) /
      average (fun ω ↦ if A (smallBits M Y ω) then (1 : ℝ) else 0) =
    average (fun ω ↦ if A (smallBits M Y ω) ∧ valueSystem M v ω = word then f ω else 0) /
      average (fun ω ↦
        if A (smallBits M Y ω) ∧ valueSystem M v ω = word then (1 : ℝ) else 0) := by
  refine ⟨?_, ?_⟩
  · rw [word_small_event_probability v q hq hqY word A]
    exact mul_pos hA (inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos))
  · have h := weighted_conditional_identity v q hq hqY word
      (fun s ↦ if A s then 1 else 0) f
    simp only [ite_mul, one_mul, zero_mul] at h
    have he : (fun ω : SampleSpace M ↦ if valueSystem M v ω = word then
        (if A (smallBits M Y ω) then f ω else 0) else 0) =
        (fun ω ↦ if A (smallBits M Y ω) ∧ valueSystem M v ω = word then f ω else 0) := by
      funext ω
      split_ifs <;> simp_all
    rw [he] at h
    rw [h, word_small_event_probability v q hq hqY word A, div_div, mul_comm]

theorem actual_window_hard_conditional {j B : ℕ} (hj : 0 < j) (hM : j + B ≤ M + 1)
    (hY : 1 ≤ Y) (hBY : B ≤ Y)
    (hgood : ∀ a : Fin B, Y < OddPrimePivot.largestOddPrime (j + a.val))
    (word : Fin B → F₂) (A : ({p : PrimeUpTo M // p.val.val ≤ Y} → F₂) → Prop)
    (hA : 0 < average (fun ω ↦ if A (smallBits M Y ω) then (1 : ℝ) else 0))
    (f : SampleSpace M → ℝ) :
    let q := cylinderPivot hj hM (fun a ↦ hY.trans_lt (hgood a))
    (0 < average (fun ω ↦ if A (smallBits M Y ω) ∧
      valueSystem M (fun a : Fin B ↦ j + a.val) ω = word then (1 : ℝ) else 0)) ∧
    average (fun ω ↦ if A (smallBits M Y ω) then
      f (forceWord (fun a : Fin B ↦ j + a.val) q word ω) else 0) /
      average (fun ω ↦ if A (smallBits M Y ω) then (1 : ℝ) else 0) =
    average (fun ω ↦ if A (smallBits M Y ω) ∧
      valueSystem M (fun a : Fin B ↦ j + a.val) ω = word then f ω else 0) /
      average (fun ω ↦ if A (smallBits M Y ω) ∧
        valueSystem M (fun a : Fin B ↦ j + a.val) ω = word then (1 : ℝ) else 0) := by
  dsimp only
  apply hard_conditional_expectation _ _ _ _ word A hA f
  · exact cylinderPivot_basis hj hM _ (fun a ↦ hBY.trans (hgood a).le)
  · exact hgood

end PaperP1.PrivateHardConditionalForcing
