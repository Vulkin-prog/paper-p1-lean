module

public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Ring.Commute
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-! # An elementary nonvanishing criterion for the biquadratic norm -/

set_option autoImplicit false

@[expose] public section

namespace PaperP1.BiquadraticNorm

def upper {R : Type*} [CommRing R] (f g a b c d : R) : R :=
  a ^ 2 + f * b ^ 2 - g * c ^ 2 - f * g * d ^ 2

def mixed {R : Type*} [CommRing R] (g a b c d : R) : R := a * b - g * c * d

def norm {R : Type*} [CommRing R] (f g a b c d : R) : R :=
  upper f g a b c d ^ 2 - 4 * f * mixed g a b c d ^ 2

theorem nonsquare_ne_zero {F : Type*} [Field F] (f : F) (hf : ¬ IsSquare f) : f ≠ 0 := by
  intro h
  apply hf
  exact ⟨0, by rw [h, mul_zero]⟩

theorem anisotropic {F : Type*} [Field F] (f a b : F) (hf : ¬ IsSquare f)
    (h : a ^ 2 = f * b ^ 2) : a = 0 ∧ b = 0 := by
  by_cases hb : b = 0
  · refine ⟨?_, hb⟩
    simpa only [hb, zero_pow (by decide : 2 ≠ 0), mul_zero, sq_eq_zero_iff] using h
  · exfalso
    apply hf
    rw [isSquare_iff_exists_sq]
    refine ⟨a / b, ?_⟩
    rw [div_pow]
    apply (eq_div_iff (pow_ne_zero 2 hb)).mpr
    simpa only [mul_comm] using h.symm

theorem square_difference_identity {R : Type*} [CommRing R] (f g a b c d : R) :
    (a ^ 2 - f * b ^ 2) ^ 2 - (g * (c ^ 2 - f * d ^ 2)) ^ 2 =
      upper f g a b c d * (a ^ 2 + f * b ^ 2 + g * c ^ 2 + f * g * d ^ 2) -
        4 * f * mixed g a b c d * (a * b + g * c * d) := by
  unfold upper mixed
  ring

theorem norm_eq_zero_iff {F : Type*} [Field F] [CharZero F] (f g a b c d : F)
    (hf : ¬ IsSquare f) (hg : ¬ IsSquare g) (hfg : ¬ IsSquare (f * g)) :
    norm f g a b c d = 0 ↔ a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  constructor
  · intro hn
    have htwo : (2 : F) ≠ 0 := by norm_num
    have heq : upper f g a b c d ^ 2 = f * (2 * mixed g a b c d) ^ 2 := by
      unfold norm at hn
      linear_combination hn
    obtain ⟨hu, hv⟩ := anisotropic f _ _ hf heq
    have hv' : mixed g a b c d = 0 := (mul_eq_zero.mp hv).resolve_left htwo
    have hsq : (a ^ 2 - f * b ^ 2) ^ 2 = (g * (c ^ 2 - f * d ^ 2)) ^ 2 := by
      apply sub_eq_zero.mp
      rw [square_difference_identity, hu, hv']
      ring
    change a ^ 2 + f * b ^ 2 - g * c ^ 2 - f * g * d ^ 2 = 0 at hu
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with hp | hm
    · have hac : a ^ 2 = g * c ^ 2 := by
        apply (mul_left_cancel₀ htwo)
        linear_combination hu + hp
      obtain ⟨ha, hc⟩ := anisotropic g a c hg hac
      have hbd : b ^ 2 = g * d ^ 2 := by
        apply (mul_left_cancel₀ (nonsquare_ne_zero f hf))
        linear_combination hu - hac
      obtain ⟨hb, hd⟩ := anisotropic g b d hg hbd
      exact ⟨ha, hb, hc, hd⟩
    · have had : a ^ 2 = (f * g) * d ^ 2 := by
        apply (mul_left_cancel₀ htwo)
        linear_combination hu + hm
      obtain ⟨ha, hd⟩ := anisotropic (f * g) a d hfg had
      have hbc : (f * b) ^ 2 = (f * g) * c ^ 2 := by
        linear_combination f * hu - f * had
      obtain ⟨hfb, hc⟩ := anisotropic (f * g) (f * b) c hfg hbc
      have hb : b = 0 := (mul_eq_zero.mp hfb).resolve_left (nonsquare_ne_zero f hf)
      exact ⟨ha, hb, hc, hd⟩
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    simp [norm, upper, mixed]

theorem norm_ne_zero {F : Type*} [Field F] [CharZero F] (f g a b c d : F)
    (hf : ¬ IsSquare f) (hg : ¬ IsSquare g) (hfg : ¬ IsSquare (f * g))
    (hne : a ≠ 0 ∨ b ≠ 0 ∨ c ≠ 0 ∨ d ≠ 0) : norm f g a b c d ≠ 0 := by
  intro h
  obtain ⟨ha, hb, hc, hd⟩ := (norm_eq_zero_iff f g a b c d hf hg hfg).mp h
  rcases hne with h | h | h | h
  · exact h ha
  · exact h hb
  · exact h hc
  · exact h hd

end PaperP1.BiquadraticNorm
