/-
Adapted from Vulkin-prog/paper-c-lean, PaperCPrel8/SignedPalmForcing.lean,
commit b9fa9ba490f201b408a302a86f1594ee620b228b, Apache-2.0,
Git blob f1e184dbb39609461fadb40d1d25d501c6d5da53.
Changes: P1's actual finite weights, exact mark model and small-prime trace.
The main conditional-law theorem also proves positivity of the marked event.
-/
module

public import PaperP1.Model.PrivateHardConditionalForcing
public import PaperP1.Model.SignedExactWords

/-! # The specified signed private-pivot Palm forcing of companion T19.16

The left boundary `j` corresponds to run start `j+1`. Only its actual
`L+e+2` values are prescribed. The larger retained support is used solely
to certify pivot hypotheses and does not add forced equations.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SignedPrivatePalmForcing

open PaperP1.Arithmetic PaperP1.Model PaperP1.PrivateValueSystem
  PaperP1.PrivatePivotGeometry PaperP1.PrivatePrimeForcing PaperP1.UniformFubini
  PaperP1.SmallPrimeConditioning PaperP1.PrivateHardConditionalForcing
  PaperP1.SignedExactWords PaperP1.OddPrimePivot

local instance signedPrivatePalmForcingDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

theorem actual_support_of_maximal {j L E e Y : ℕ} (he : e ≤ E)
    (hgood : ∀ i : Fin (L + E + 2), Y < largestOddPrime (j + i.val)) :
    ∀ i : Fin (L + e + 2), Y < largestOddPrime (j + i.val) := by
  intro i
  exact hgood ⟨i.val, by have := i.isLt; omega⟩

theorem signedForcing_hits {M j L e : ℕ} (hL : 1 ≤ L)
    (q : Fin (L + e + 2) → PrimeUpTo M)
    (hq : ∀ a, valueSystem M (fun i : Fin (L + e + 2) ↦ j + i.val)
      (Pi.single (q a) 1) = Pi.single a 1) (s : F₂) (ω : SampleSpace M) :
    SignedExactMark (valueBit (forceWord (fun i : Fin (L + e + 2) ↦ j + i.val)
      q (signedExactWord L e s) ω)) (j + 1) L e s :=
  (finite_signedWord_iff hL s _).mp (forceWord_hits _ q hq _ ω)

theorem actual_signed_small_probability {M Y j L e : ℕ}
    (hj : 0 < j) (hL : 1 ≤ L) (hM : j + (L + e + 2) ≤ M + 1)
    (hY : 1 ≤ Y) (hBY : L + e + 2 ≤ Y)
    (hgood : ∀ a : Fin (L + e + 2), Y < largestOddPrime (j + a.val))
    (s : F₂) (A : ({p : PrimeUpTo M // p.val.val ≤ Y} → F₂) → Prop) :
    average (fun ω ↦ if A (smallBits M Y ω) ∧
      SignedExactMark (valueBit ω) (j + 1) L e s then (1 : ℝ) else 0) =
    average (fun ω ↦ if A (smallBits M Y ω) then (1 : ℝ) else 0) * signedMarkRate L e := by
  let q := cylinderPivot hj hM (fun a ↦ hY.trans_lt (hgood a))
  have hq := cylinderPivot_basis hj hM (fun a ↦ hY.trans_lt (hgood a))
    (fun a ↦ hBY.trans (hgood a).le)
  have h := word_small_event_probability (fun a : Fin (L + e + 2) ↦ j + a.val)
    q hq hgood (signedExactWord L e s) A
  simpa only [finite_signedWord_iff hL, Fintype.card_fun, Fintype.card_fin, ZMod.card,
    Nat.cast_pow, Nat.cast_ofNat, signedMarkRate] using h

theorem actual_signed_probability {M Y j L e : ℕ}
    (hj : 0 < j) (hL : 1 ≤ L) (hM : j + (L + e + 2) ≤ M + 1)
    (hY : 1 ≤ Y) (hBY : L + e + 2 ≤ Y)
    (hgood : ∀ a : Fin (L + e + 2), Y < largestOddPrime (j + a.val)) (s : F₂) :
    average (fun ω : SampleSpace M ↦
      if SignedExactMark (valueBit ω) (j + 1) L e s then (1 : ℝ) else 0) =
      signedMarkRate L e := by
  simpa only [true_and, ite_true, constant, one_mul] using
    actual_signed_small_probability hj hL hM hY hBY hgood s (fun _ ↦ True)

theorem actual_signed_hard_conditional {M Y j L e : ℕ}
    (hj : 0 < j) (hL : 1 ≤ L) (hM : j + (L + e + 2) ≤ M + 1)
    (hY : 1 ≤ Y) (hBY : L + e + 2 ≤ Y)
    (hgood : ∀ a : Fin (L + e + 2), Y < largestOddPrime (j + a.val))
    (s : F₂) (A : ({p : PrimeUpTo M // p.val.val ≤ Y} → F₂) → Prop)
    (hA : 0 < average (fun ω ↦ if A (smallBits M Y ω) then (1 : ℝ) else 0))
    (f : SampleSpace M → ℝ) :
    let q := cylinderPivot hj hM (fun a ↦ hY.trans_lt (hgood a))
    (0 < average (fun ω ↦ if A (smallBits M Y ω) ∧
      SignedExactMark (valueBit ω) (j + 1) L e s then (1 : ℝ) else 0)) ∧
    average (fun ω ↦ if A (smallBits M Y ω) then
      f (forceWord (fun a : Fin (L + e + 2) ↦ j + a.val) q (signedExactWord L e s) ω) else 0) /
      average (fun ω ↦ if A (smallBits M Y ω) then (1 : ℝ) else 0) =
    average (fun ω ↦ if A (smallBits M Y ω) ∧
      SignedExactMark (valueBit ω) (j + 1) L e s then f ω else 0) /
      average (fun ω ↦ if A (smallBits M Y ω) ∧
        SignedExactMark (valueBit ω) (j + 1) L e s then (1 : ℝ) else 0) := by
  have h := actual_window_hard_conditional hj hM hY hBY hgood (signedExactWord L e s) A hA f
  simpa only [finite_signedWord_iff hL] using h

end PaperP1.SignedPrivatePalmForcing
