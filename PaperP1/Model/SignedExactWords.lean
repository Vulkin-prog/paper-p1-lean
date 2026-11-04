/-
The signed word is adapted from Vulkin-prog/paper-c-lean,
PaperCV282/SignedExactMarks.lean, commit b9fa9ba490f201b408a302a86f1594ee620b228b,
Apache-2.0, Git blob 2a69b7db8be6a305da586d7948fac7785588e6b3.
P1's exact mark is defined here through its existing StartEvent, an exact
right boundary and the source sign. No old marked-process model is imported.
-/
module

public import PaperP1.Model.PrivateValueSystem
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity

/-! # Exact signed run words, both boundaries and geometric type masses -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SignedExactWords

open PaperP1.Arithmetic PaperP1.Model PaperP1.PrivateValueSystem Finset

theorem eq_one_add_iff_add_eq_one (a b : F₂) : a = 1 + b ↔ a + b = 1 := by
  revert a b
  decide

def signedExactWord (L e : ℕ) (s : F₂) : Fin (L + e + 2) → F₂ :=
  fun i ↦ if i.val = 0 ∨ i.val + 1 = L + e + 2 then 1 + s else s

theorem phase_one_add (s : F₂) : phase (1 + s) = -phase s := by
  revert s
  decide

theorem phase_signedExactWord (L e : ℕ) (s : F₂) (i : Fin (L + e + 2)) :
    phase (signedExactWord L e s i) =
      if i.val = 0 ∨ i.val + 1 = L + e + 2 then -phase s else phase s := by
  unfold signedExactWord
  split_ifs <;> simp only [phase_one_add]

/-- A run of exactly `L+e` values, its two changes, and its actual sign. -/
def SignedExactMark (g : ℕ → F₂) (x L e : ℕ) (s : F₂) : Prop :=
  StartEvent g x (L + e) ∧ g (x + (L + e)) + g x = 1 ∧ g x = s

theorem signedWord_iff {g : ℕ → F₂} {j L e : ℕ} (hL : 1 ≤ L) (s : F₂) :
    (∀ i : Fin (L + e + 2), g (j + i.val) = signedExactWord L e s i) ↔
      SignedExactMark g (j + 1) L e s := by
  constructor
  · intro hw
    have hz := hw ⟨0, by omega⟩
    have ho := hw ⟨1, by omega⟩
    have hl := hw ⟨L + e + 1, by omega⟩
    have hs : g (j + 1) = s := by
      change g (j + 1) = (if (1 : ℕ) = 0 ∨ 1 + 1 = L + e + 2 then 1 + s else s) at ho
      rw [ite_eq_right (by omega)] at ho
      exact ho
    have hz' : g j = 1 + s := by simpa [signedExactWord] using hz
    have hl' : g (j + 1 + (L + e)) = 1 + s := by
      simpa [signedExactWord, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hl
    refine ⟨⟨?_, ?_⟩, ?_, hs⟩
    · simpa only [Nat.add_sub_cancel, hs] using
        (eq_one_add_iff_add_eq_one _ _).mp hz'
    · intro k hk
      have hm := hw ⟨k + 1, by omega⟩
      change g (j + (k + 1)) =
        (if k + 1 = 0 ∨ k + 1 + 1 = L + e + 2 then 1 + s else s) at hm
      rw [ite_eq_right (by omega)] at hm
      simpa only [Nat.add_assoc, Nat.add_comm k 1, hs] using hm
    · rw [hs]
      exact (eq_one_add_iff_add_eq_one _ _).mp hl'
  · rintro ⟨⟨hleft, hmid⟩, hright, hs⟩ i
    by_cases hi : i.val = 0
    · have hb : g j = 1 + s := by
        apply (eq_one_add_iff_add_eq_one _ _).mpr
        simpa only [Nat.add_sub_cancel, hs] using hleft
      simpa [signedExactWord, hi] using hb
    · by_cases hlast : i.val + 1 = L + e + 2
      · have hb : g (j + 1 + (L + e)) = 1 + s := by
          apply (eq_one_add_iff_add_eq_one _ _).mpr
          simpa only [hs] using hright
        have hv : j + i.val = j + 1 + (L + e) := by omega
        simpa [signedExactWord, hlast, hv] using hb
      · have hm := hmid (i.val - 1) (by have := i.isLt; omega)
        have hv : j + 1 + (i.val - 1) = j + i.val := by omega
        simpa only [hv, hs, signedExactWord, hi, hlast, false_or, ite_false] using hm

theorem finite_signedWord_iff {M j L e : ℕ} (hL : 1 ≤ L) (s : F₂)
    (ω : SampleSpace M) :
    valueSystem M (fun i : Fin (L + e + 2) ↦ j + i.val) ω = signedExactWord L e s ↔
      SignedExactMark (valueBit ω) (j + 1) L e s := by
  rw [valueSystem_eq_iff]
  exact signedWord_iff hL s

/-- The bit encoding is the literal word `(-σ, σ, ..., σ, -σ)`. -/
theorem signed_phase_word_iff {M j L e : ℕ} (hL : 1 ≤ L) (s : F₂) (ω : SampleSpace M) :
    (∀ i : Fin (L + e + 2), randomMultiplicativeValue ω (j + i.val) =
      if i.val = 0 ∨ i.val + 1 = L + e + 2 then -phase s else phase s) ↔
      SignedExactMark (valueBit ω) (j + 1) L e s := by
  rw [← finite_signedWord_iff hL, valueSystem_eq_iff]
  apply forall_congr'
  intro i
  rw [← phase_signedExactWord]
  exact phase_eq_iff _ _

def signedMarkRate (L e : ℕ) : ℝ := (2 ^ (L + e + 2) : ℝ)⁻¹

theorem signedMarkRate_pos (L e : ℕ) : 0 < signedMarkRate L e := by
  unfold signedMarkRate
  positivity

theorem signedMarkRate_factor (L e : ℕ) :
    signedMarkRate L e = (2 ^ L : ℝ)⁻¹ * (2 ^ (e + 2) : ℝ)⁻¹ := by
  simp [signedMarkRate, show L + e + 2 = L + (e + 2) by omega, pow_add,
    mul_comm]

theorem signedMarkRate_zero (L : ℕ) : signedMarkRate L 0 = (2 ^ L : ℝ)⁻¹ / 4 := by
  rw [signedMarkRate_factor]
  norm_num [div_eq_mul_inv]

/-- The sum includes both signs. There is no factor growing with the cutoff. -/
theorem sum_signedMarkRate (L E : ℕ) :
    (∑ e ∈ range (E + 1), ∑ _s : F₂, signedMarkRate L e) =
      (2 ^ L : ℝ)⁻¹ * (1 - (2 ^ (E + 1) : ℝ)⁻¹) := by
  simp only [sum_const, card_univ, ZMod.card, Nat.cast_ofNat, nsmul_eq_mul]
  induction E with
  | zero =>
      simp [signedMarkRate_zero]
      ring
  | succ E ih =>
      rw [sum_range_succ, ih, signedMarkRate_factor]
      have hpow : (2 ^ (E + 1 + 1) : ℝ) = 2 ^ (E + 1) * 2 := pow_succ _ _
      have hpow' : (2 ^ (E + 1 + 2) : ℝ) = 2 ^ (E + 1) * 4 := by
        rw [pow_add]
        norm_num
      rw [hpow, hpow']
      field_simp
      ring

theorem sum_signedMarkRate_le (L E : ℕ) :
    (∑ e ∈ range (E + 1), ∑ _s : F₂, signedMarkRate L e) ≤ (2 ^ L : ℝ)⁻¹ := by
  rw [sum_signedMarkRate]
  exact mul_le_of_le_one_right (by positivity) (sub_le_self _ (by positivity))

end PaperP1.SignedExactWords
