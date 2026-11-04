module

public import PaperP1.Model.AnchoredWindowForcing
public import PaperP1.Model.SignedExactWords

/-! # The two literal unsigned forcings of companion T19.17

The start word has length `L+1`; exact excess zero has length `L+2`.
Every admissible arithmetic anchor yields the complete conditional sample
law with the respective exact rate `p` or `p/2`, even at a defective anchor.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UnsignedAnchoredRunForcing

open PaperP1.Arithmetic PaperP1.Model PaperP1.PrivateValueSystem PaperP1.UniformFubini
  PaperP1.SignedExactWords PaperP1.AnchoredWindowForcing

local instance unsignedAnchoredRunForcingDecidable (P : Prop) : Decidable P :=
  Classical.propDecidable P

def startWord (L : ℕ) (s : F₂) : Fin (L + 1) → F₂ :=
  fun i ↦ if i.val = 0 then 1 + s else s

theorem startWord_shift (L : ℕ) (s : F₂) :
    (fun i ↦ startWord L 0 i + s) = startWord L s := by
  funext i
  unfold startWord
  split_ifs <;> simp

theorem exactWord_shift (L : ℕ) (s : F₂) :
    (fun i ↦ signedExactWord L 0 0 i + s) = signedExactWord L 0 s := by
  funext i
  unfold signedExactWord
  split_ifs <;> simp

theorem startWord_iff {g : ℕ → F₂} {j L : ℕ} (hL : 1 ≤ L) (s : F₂) :
    (∀ i : Fin (L + 1), g (j + i.val) = startWord L s i) ↔
      StartEvent g (j + 1) L ∧ g (j + 1) = s := by
  constructor
  · intro hw
    have hz := hw ⟨0, by omega⟩
    have ho := hw ⟨1, by omega⟩
    have hs : g (j + 1) = s := by simpa [startWord] using ho
    have hz' : g j = 1 + s := by simpa [startWord] using hz
    refine ⟨⟨?_, ?_⟩, hs⟩
    · simpa only [Nat.add_sub_cancel, hs] using
        (eq_one_add_iff_add_eq_one _ _).mp hz'
    · intro k hk
      have hm := hw ⟨k + 1, by omega⟩
      simpa [startWord, Nat.add_assoc, Nat.add_comm k 1, hs] using hm
  · rintro ⟨⟨hleft, hmid⟩, hs⟩ i
    by_cases hi : i.val = 0
    · have hb : g j = 1 + s := by
        apply (eq_one_add_iff_add_eq_one _ _).mpr
        simpa only [Nat.add_sub_cancel, hs] using hleft
      simpa [startWord, hi] using hb
    · have hm := hmid (i.val - 1) (by have := i.isLt; omega)
      have hv : j + 1 + (i.val - 1) = j + i.val := by omega
      simpa only [hv, hs, startWord, hi, ite_false] using hm

theorem unsigned_start_word_iff {g : ℕ → F₂} {j L : ℕ} (hL : 1 ≤ L) :
    (∃ s : F₂, ∀ i : Fin (L + 1), g (j + i.val) = startWord L 0 i + s) ↔
      StartEvent g (j + 1) L := by
  have hw (s : F₂) : (∀ i : Fin (L + 1), g (j + i.val) = startWord L 0 i + s) ↔
      StartEvent g (j + 1) L ∧ g (j + 1) = s := by
    have he := congrFun (startWord_shift L s)
    simp_rw [he]
    exact startWord_iff hL s
  simp only [hw]
  constructor
  · rintro ⟨_, h, _⟩
    exact h
  · intro h
    exact ⟨g (j + 1), h, rfl⟩

theorem unsigned_exact_word_iff {g : ℕ → F₂} {j L : ℕ} (hL : 1 ≤ L) :
    (∃ s : F₂, ∀ i : Fin (L + 2), g (j + i.val) = signedExactWord L 0 0 i + s) ↔
      ∃ s : F₂, SignedExactMark g (j + 1) L 0 s := by
  apply exists_congr
  intro s
  have he := congrFun (exactWord_shift L s)
  simp_rw [he]
  exact signedWord_iff (g := g) (j := j) (e := 0) hL s

theorem finite_start_word_iff {M j L : ℕ} (hL : 1 ≤ L) (ω : SampleSpace M) :
    (∃ s : F₂, valueSystem M (fun i : Fin (L + 1) ↦ j + i.val) ω =
      (fun i ↦ startWord L 0 i + s)) ↔ StartEvent (valueBit ω) (j + 1) L := by
  simp only [valueSystem_eq_iff]
  exact unsigned_start_word_iff hL

theorem finite_exact_word_iff {M j L : ℕ} (hL : 1 ≤ L) (ω : SampleSpace M) :
    (∃ s : F₂, valueSystem M (fun i : Fin (L + 2) ↦ j + i.val) ω =
      (fun i ↦ signedExactWord L 0 0 i + s)) ↔
        ∃ s : F₂, SignedExactMark (valueBit ω) (j + 1) L 0 s := by
  simp only [valueSystem_eq_iff]
  exact unsigned_exact_word_iff hL

theorem start_forcing_hits {M j L Y : ℕ} {anchor : Fin (L + 1)}
    (D : Data M j (L + 1) Y anchor) (hL : 1 ≤ L) (ω : SampleSpace M) :
    StartEvent (valueBit (force D (startWord L 0) ω)) (j + 1) L :=
  (finite_start_word_iff hL _).mp (hits D (startWord L 0) ω)

theorem exact_forcing_hits {M j L Y : ℕ} {anchor : Fin (L + 2)}
    (D : Data M j (L + 2) Y anchor) (hL : 1 ≤ L) (ω : SampleSpace M) :
    ∃ s : F₂, SignedExactMark (valueBit (force D (signedExactWord L 0 0) ω)) (j + 1) L 0 s :=
  (finite_exact_word_iff hL _).mp (hits D (signedExactWord L 0 0) ω)

theorem start_probability {M j L Y : ℕ} {anchor : Fin (L + 1)}
    (D : Data M j (L + 1) Y anchor) (hL : 1 ≤ L) :
    average (fun ω : SampleSpace M ↦ if StartEvent (valueBit ω) (j + 1) L then (1 : ℝ) else 0) =
      (2 ^ L : ℝ)⁻¹ := by
  simpa only [finite_start_word_iff hL, Nat.add_sub_cancel] using
    AnchoredWindowForcing.event_probability D (startWord L 0)

theorem exact_probability {M j L Y : ℕ} {anchor : Fin (L + 2)}
    (D : Data M j (L + 2) Y anchor) (hL : 1 ≤ L) :
    average (fun ω : SampleSpace M ↦
      if ∃ s : F₂, SignedExactMark (valueBit ω) (j + 1) L 0 s then (1 : ℝ) else 0) =
      (2 ^ (L + 1) : ℝ)⁻¹ := by
  simpa only [finite_exact_word_iff hL, show L + 2 - 1 = L + 1 by omega] using
    AnchoredWindowForcing.event_probability D (signedExactWord L 0 0)

theorem start_full_conditional {M j L Y : ℕ} {anchor : Fin (L + 1)}
    (D : Data M j (L + 1) Y anchor) (hL : 1 ≤ L) (f : SampleSpace M → ℝ) :
    average (fun ω ↦ f (force D (startWord L 0) ω)) =
      average (fun ω ↦ if StartEvent (valueBit ω) (j + 1) L then f ω else 0) / (2 ^ L : ℝ)⁻¹ := by
  simpa only [finite_start_word_iff hL, Nat.add_sub_cancel] using
    full_conditional D (startWord L 0) f

theorem exact_full_conditional {M j L Y : ℕ} {anchor : Fin (L + 2)}
    (D : Data M j (L + 2) Y anchor) (hL : 1 ≤ L) (f : SampleSpace M → ℝ) :
    average (fun ω ↦ f (force D (signedExactWord L 0 0) ω)) =
      average (fun ω ↦ if ∃ s : F₂, SignedExactMark (valueBit ω) (j + 1) L 0 s then f ω else 0) /
        (2 ^ (L + 1) : ℝ)⁻¹ := by
  simpa only [finite_exact_word_iff hL, show L + 2 - 1 = L + 1 by omega] using
    full_conditional D (signedExactWord L 0 0) f

end PaperP1.UnsignedAnchoredRunForcing
