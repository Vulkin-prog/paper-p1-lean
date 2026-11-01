module

public import PaperP1.Arithmetic.SignedChannelLeadingBounds
public import PaperP1.Arithmetic.ActualSourceTranslations
public import PaperP1.Asymptotics.CriticalChannelPowers
public import PaperP1.Asymptotics.ChannelMainTermAlgebra

/-! # Explicit positive constants for the actual fixed-channel leading term -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ChannelMainTermBounds

open PaperP1.ChannelSumIdentity PaperP1.SignedChannelLeadingBounds PaperP1.CriticalChannelPowers

def mainTerm (N L a b : ℕ) : ℝ :=
  ((2 ^ L : ℝ)⁻¹) ^ 2 * ((N : ℝ) * (ActualSourceTranslations.coefficient a b : ℝ) * (signed L a b : ℤ))

def lowerConstant (C : ℝ) (a b : ℕ) : ℝ :=
  (((2 : ℝ) ^ C)⁻¹) ^ 2 * (ActualSourceTranslations.coefficient a b : ℝ) *
    (1 / (8 * (b : ℝ))) * (2 : ℝ) ^ (-C / b - 1)

def upperConstant (C : ℝ) (a b : ℕ) : ℝ :=
  ((2 : ℝ) ^ C) ^ 2 * (ActualSourceTranslations.coefficient a b : ℝ) *
    (4 * (b : ℝ)) * (2 : ℝ) ^ ((C + 1) / b)

theorem coefficient_pos {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hinterior : b < 2 * a) :
    (0 : ℝ) < (ActualSourceTranslations.coefficient a b : ℝ) := by
  have haQ : (0 : ℚ) < a := by exact_mod_cast ha
  have hbQ : (0 : ℚ) < b := by exact_mod_cast hb
  have hiQ : (b : ℚ) < 2 * a := by exact_mod_cast hinterior
  have hw : (0 : ℚ) < ActualSourceTranslations.coefficient a b := by
    unfold ActualSourceTranslations.coefficient
    apply div_pos
    · linarith
    · exact mul_pos haQ hbQ
  exact_mod_cast hw

theorem constants_pos (C : ℝ) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hinterior : b < 2 * a) :
    0 < lowerConstant C a b ∧ 0 < upperConstant C a b := by
  have hw := coefficient_pos ha hb hinterior
  unfold lowerConstant upperConstant
  constructor <;> positivity

theorem main_term_bounds {N L a b : ℕ} {C : ℝ} (hN : 2 ≤ N) (ha : 0 < a) (hab : a < b)
    (hinterior : b < 2 * a) (hL : 10 * b ^ 3 ≤ L)
    (hband : |(L : ℝ) - Real.log N / Real.log 2| ≤ C) :
    lowerConstant C a b * L * (N : ℝ) ^ (-1 + 1 / (b : ℝ)) ≤ mainTerm N L a b ∧
      mainTerm N L a b ≤ upperConstant C a b * L * (N : ℝ) ^ (-1 + 1 / (b : ℝ)) := by
  have hb : 0 < b := ha.trans hab
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hn : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hw := coefficient_pos ha hb hinterior
  have hs := length_bounds ha hab hL
  have hsLo : (L : ℝ) * (2 : ℝ) ^ (L / b) ≤ 8 * (b : ℝ) * (signed L a b : ℤ) := by exact_mod_cast hs.1
  have hsHi : ((signed L a b : ℤ) : ℝ) ≤ 4 * (b : ℝ) * L * (2 : ℝ) ^ (L / b) := by exact_mod_cast hs.2
  have hSlow : (1 / (8 * (b : ℝ))) * L * (2 : ℝ) ^ (L / b) ≤ (signed L a b : ℤ) := by
    have hd : (L : ℝ) * (2 : ℝ) ^ (L / b) / (8 * (b : ℝ)) ≤ (signed L a b : ℤ) := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 8 * b)).mpr
      nlinarith only [hsLo]
    convert hd using 1; ring
  have hmain := ChannelMainTermAlgebra.main_term_scale
    (N := (N : ℝ)) (L := (L : ℝ)) (P := ((2 ^ L : ℝ)⁻¹) ^ 2)
    (W := (2 : ℝ) ^ (L / b)) (S := ((signed L a b : ℤ) : ℝ))
    (w := (ActualSourceTranslations.coefficient a b : ℝ))
    (cs := 1 / (8 * (b : ℝ))) (Cs := 4 * (b : ℝ))
    (PL := (((2 : ℝ) ^ C)⁻¹) ^ 2) (PU := ((2 : ℝ) ^ C) ^ 2)
    (QL := (2 : ℝ) ^ (-C / b - 1)) (QU := (2 : ℝ) ^ ((C + 1) / b)) (β := 1 / (b : ℝ))
    hn (Nat.cast_nonneg L) (sq_nonneg _) hw.le (by positivity) (by positivity) (by positivity) (sq_nonneg _)
    (nominal_square_lower hN hband) (nominal_square_upper hN hband)
    (quotient_word_lower hN hb hband) (quotient_word_upper hN hb hband) hSlow hsHi
  simpa only [mainTerm, lowerConstant, upperConstant, mul_assoc] using hmain

end PaperP1.ChannelMainTermBounds
