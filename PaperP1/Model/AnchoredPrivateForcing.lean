module

public import PaperP1.Model.AnchoredPrivateValues
public import PaperP1.Model.PrivateHardConditionalForcing

/-! # Complete conditional forcing up to sign while preserving a chosen anchor

Only the nonanchor private primes are changed. The anchor's raw value may
be deterministic or defective. Full-observable laws follow from the actual
relative-value system; no fairness of the anchor value is assumed.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AnchoredPrivateForcing

open PaperP1.Arithmetic PaperP1.Model PaperP1.PrivateValueSystem
  PaperP1.PrivatePrimeForcing PaperP1.AnchoredPrivateValues PaperP1.UniformFubini
  PaperP1.PrivateHardConditionalForcing PaperP1.SmallPrimeConditioning

local instance anchoredPrivateForcingDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

variable {M : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

def force (v : ι → ℕ) (anchor : ι) (q : Free anchor → PrimeUpTo M)
    (b : ι → F₂) (ω : SampleSpace M) : SampleSpace M :=
  forceWord (relativeValues v anchor) q (relativeWord b anchor) ω

theorem free_card (anchor : ι) : Fintype.card (Free anchor) = Fintype.card ι - 1 := by
  classical
  simp [Free, Fintype.card_subtype_compl]

theorem force_hits (v : ι → ℕ) (anchor : ι) (hpos : ∀ i, 0 < v i)
    (q : Free anchor → PrimeUpTo M)
    (hq : ∀ i, valueSystem M (relativeValues v anchor) (Pi.single (q i) 1) = Pi.single i 1)
    (b : ι → F₂) (ω : SampleSpace M) :
    ∃ s : F₂, valueSystem M v (force v anchor q b ω) = fun i ↦ b i + s :=
  (relative_eq_iff v anchor hpos b _).mp
    (forceWord_hits (relativeValues v anchor) q hq (relativeWord b anchor) ω)

theorem force_fixes (v : ι → ℕ) (anchor : ι) (hpos : ∀ i, 0 < v i)
    (q : Free anchor → PrimeUpTo M) (b : ι → F₂) (ω : SampleSpace M)
    (h : ∃ s : F₂, valueSystem M v ω = fun i ↦ b i + s) :
    force v anchor q b ω = ω :=
  forceWord_fixes _ _ _ _ ((relative_eq_iff v anchor hpos b ω).mpr h)

theorem force_idempotent (v : ι → ℕ) (anchor : ι) (hpos : ∀ i, 0 < v i)
    (q : Free anchor → PrimeUpTo M)
    (hq : ∀ i, valueSystem M (relativeValues v anchor) (Pi.single (q i) 1) = Pi.single i 1)
    (b : ι → F₂) (ω : SampleSpace M) :
    force v anchor q b (force v anchor q b ω) = force v anchor q b ω :=
  force_fixes v anchor hpos q b _ (force_hits v anchor hpos q hq b ω)

theorem preserves_anchor (v : ι → ℕ) (anchor : ι) (q : Free anchor → PrimeUpTo M)
    (hn : ∀ i, ¬(q i).val.val ∣ v anchor) (b : ι → F₂) (ω : SampleSpace M) :
    valueBit (force v anchor q b ω) (v anchor) = valueBit ω (v anchor) :=
  forceWord_preserves_value _ _ _ _ _ hn

theorem preserves_nonpivot (v : ι → ℕ) (anchor : ι) (q : Free anchor → PrimeUpTo M)
    (b : ι → F₂) (ω : SampleSpace M) (p : PrimeUpTo M) (hp : ∀ i, p ≠ q i) :
    force v anchor q b ω p = ω p := forceWord_preserves_nonpivot _ _ _ _ _ hp

theorem source_orientation (v : ι → ℕ) (anchor : ι) (hpos : ∀ i, 0 < v i)
    (q : Free anchor → PrimeUpTo M)
    (hq : ∀ i, valueSystem M (relativeValues v anchor) (Pi.single (q i) 1) = Pi.single i 1)
    (hn : ∀ i, ¬(q i).val.val ∣ v anchor) (b : ι → F₂) (ω : SampleSpace M) :
    valueSystem M v (force v anchor q b ω) =
      fun i ↦ b i + (valueBit ω (v anchor) - b anchor) := by
  obtain ⟨s, hs⟩ := force_hits v anchor hpos q hq b ω
  have ha := congrFun hs anchor
  simp only [valueSystem_apply, preserves_anchor v anchor q hn] at ha
  have he : s = valueBit ω (v anchor) - b anchor := by
    calc
      _ = (b anchor + s) - b anchor := by abel
      _ = _ := by rw [← ha]
  simpa only [he] using hs

theorem uniform_conditional (v : ι → ℕ) (anchor : ι) (hpos : ∀ i, 0 < v i)
    (q : Free anchor → PrimeUpTo M)
    (hq : ∀ i, valueSystem M (relativeValues v anchor) (Pi.single (q i) 1) = Pi.single i 1)
    (b : ι → F₂) (f : SampleSpace M → ℝ) :
    average (fun ω ↦ f (force v anchor q b ω)) =
      average (fun ω ↦ if ∃ s : F₂, valueSystem M v ω = (fun i ↦ b i + s) then f ω else 0) /
        (2 ^ (Fintype.card ι - 1) : ℝ)⁻¹ := by
  have h := uniform_conditional_expectation (relativeValues v anchor) q hq (relativeWord b anchor) f
  simpa only [force, relative_eq_iff v anchor hpos, Fintype.card_fun, free_card,
    ZMod.card, Nat.cast_pow, Nat.cast_ofNat] using h

theorem event_probability (v : ι → ℕ) (anchor : ι) (hpos : ∀ i, 0 < v i)
    (q : Free anchor → PrimeUpTo M)
    (hq : ∀ i, valueSystem M (relativeValues v anchor) (Pi.single (q i) 1) = Pi.single i 1)
    (b : ι → F₂) :
    average (fun ω : SampleSpace M ↦
      if ∃ s : F₂, valueSystem M v ω = (fun i ↦ b i + s) then (1 : ℝ) else 0) =
      (2 ^ (Fintype.card ι - 1) : ℝ)⁻¹ := by
  have h := uniform_conditional v anchor hpos q hq b (fun _ ↦ 1)
  rw [constant] at h
  have hc : (2 ^ (Fintype.card ι - 1) : ℝ)⁻¹ ≠ 0 := by positivity
  simpa only [one_mul] using ((eq_div_iff hc).mp h).symm

theorem small_weighted_conditional {Y : ℕ} (v : ι → ℕ) (anchor : ι) (hpos : ∀ i, 0 < v i)
    (q : Free anchor → PrimeUpTo M)
    (hq : ∀ i, valueSystem M (relativeValues v anchor) (Pi.single (q i) 1) = Pi.single i 1)
    (hY : ∀ i, Y < (q i).val.val) (b : ι → F₂)
    (weight : ({p : PrimeUpTo M // p.val.val ≤ Y} → F₂) → ℝ) (f : SampleSpace M → ℝ) :
    average (fun ω ↦ weight (smallBits M Y ω) * f (force v anchor q b ω)) =
      average (fun ω ↦ if ∃ s : F₂, valueSystem M v ω = (fun i ↦ b i + s) then
        weight (smallBits M Y ω) * f ω else 0) / (2 ^ (Fintype.card ι - 1) : ℝ)⁻¹ := by
  have h := weighted_conditional_identity (relativeValues v anchor) q hq hY
    (relativeWord b anchor) weight f
  simpa only [force, relative_eq_iff v anchor hpos, Fintype.card_fun, free_card,
    ZMod.card, Nat.cast_pow, Nat.cast_ofNat] using h

end PaperP1.AnchoredPrivateForcing
