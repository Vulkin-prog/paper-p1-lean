module

public import PaperP1.Model.PrivatePrimeForcing

/-! # Absolute words up to a global sign with an arbitrary preserved anchor

The relative rows are encoded by the actual products `v_i*v_anchor`.
Multiplicativity identifies them with differences of the original raw bits.
No randomness or nonzero parity vector is required at the anchor itself.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AnchoredPrivateValues

open PaperP1.Arithmetic PaperP1.Model PaperP1.PrivateValueSystem
  PaperP1.PrivatePrimeForcing

variable {ι : Type*} [DecidableEq ι]

abbrev Free (anchor : ι) := {i : ι // i ≠ anchor}

def relativeValues (v : ι → ℕ) (anchor : ι) : Free anchor → ℕ :=
  fun i ↦ v i.val * v anchor

def relativeWord (b : ι → F₂) (anchor : ι) : Free anchor → F₂ :=
  fun i ↦ b i.val - b anchor

theorem add_eq_sub (a b : F₂) : a + b = a - b := by
  revert a b
  decide

omit [DecidableEq ι] in
theorem relative_value {M : ℕ} (v : ι → ℕ) (anchor : ι)
    (hpos : ∀ i, 0 < v i) (ω : SampleSpace M) (i : Free anchor) :
    valueSystem M (relativeValues v anchor) ω i =
      valueBit ω (v i.val) - valueBit ω (v anchor) := by
  rw [valueSystem_apply, relativeValues, valueBit_mul ω (Nat.ne_of_gt (hpos i.val))
    (Nat.ne_of_gt (hpos anchor)), add_eq_sub]

theorem relative_eq_iff {M : ℕ} (v : ι → ℕ) (anchor : ι) (hpos : ∀ i, 0 < v i)
    (b : ι → F₂) (ω : SampleSpace M) :
    valueSystem M (relativeValues v anchor) ω = relativeWord b anchor ↔
      ∃ s : F₂, valueSystem M v ω = fun i ↦ b i + s := by
  constructor
  · intro h
    refine ⟨valueBit ω (v anchor) - b anchor, ?_⟩
    funext i
    rw [valueSystem_apply]
    by_cases hi : i = anchor
    · subst i
      abel
    · have hh := congrFun h ⟨i, hi⟩
      rw [relative_value v anchor hpos] at hh
      change valueBit ω (v i) - valueBit ω (v anchor) = b i - b anchor at hh
      calc
        _ = (valueBit ω (v i) - valueBit ω (v anchor)) + valueBit ω (v anchor) :=
          (sub_add_cancel _ _).symm
        _ = _ := by rw [hh]; abel
  · rintro ⟨s, h⟩
    funext i
    rw [relative_value v anchor hpos]
    have hi := congrFun h i.val
    have ha := congrFun h anchor
    simp only [valueSystem_apply] at hi ha
    change valueBit ω (v i.val) - valueBit ω (v anchor) = b i.val - b anchor
    rw [hi, ha]
    abel

theorem relative_prime_basis {M : ℕ} (v : ι → ℕ) (anchor : ι)
    (hpos : ∀ i, 0 < v i) (q : Free anchor → PrimeUpTo M)
    (hdiag : ∀ i, parityVec (v i.val) (q i).val.val = 1)
    (hoff : ∀ i, ∀ k, k ≠ i.val → parityVec (v k) (q i).val.val = 0)
    (i : Free anchor) :
    valueSystem M (relativeValues v anchor) (Pi.single (q i) 1) = Pi.single i 1 := by
  apply valueSystem_prime_basis
  · rw [relativeValues, parityVec_mul (Nat.ne_of_gt (hpos i.val))
      (Nat.ne_of_gt (hpos anchor)), Finsupp.add_apply, hdiag,
      hoff i anchor i.property.symm, add_zero]
  · intro k hki
    have hval : k.val ≠ i.val := fun h ↦ hki (Subtype.ext h)
    rw [relativeValues, parityVec_mul (Nat.ne_of_gt (hpos k.val))
      (Nat.ne_of_gt (hpos anchor)), Finsupp.add_apply, hoff i k.val hval,
      hoff i anchor i.property.symm, add_zero]

end PaperP1.AnchoredPrivateValues
