module

public import PaperP1.Arithmetic.ChannelSumIdentity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-! # Positive leading coefficients and explicit eventual finite bounds for the signed channel sum -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SignedChannelLeadingBounds

open PaperP1.ChannelSumIdentity

def linearCoefficient (a b r : ℕ) : ℤ := ((b : ℤ) - a) * ((b : ℤ) + r - 1)

def constantCoefficient (a b r : ℕ) : ℤ :=
  ((r : ℤ) - 1) ^ 2 + ((a : ℤ) + b) * ((r : ℤ) - 1) + 3 * a * b

def polynomialLoss (L a b : ℕ) : ℤ := ((a : ℤ) + b) * ((L : ℤ) - 1) + a * b

theorem coefficient_bounds {a b r : ℕ} (ha : 0 < a) (hab : a < b) (hr : r < b) :
    1 ≤ linearCoefficient a b r ∧ linearCoefficient a b r ≤ 2 * (b : ℤ) ^ 2 ∧
      0 ≤ constantCoefficient a b r ∧ constantCoefficient a b r ≤ 6 * (b : ℤ) ^ 2 := by
  have haZ : (1 : ℤ) ≤ a := by exact_mod_cast (by omega : 1 ≤ a)
  have hbZ : (2 : ℤ) ≤ b := by exact_mod_cast (by omega : 2 ≤ b)
  have habZ : (a : ℤ) < b := by exact_mod_cast hab
  have hrZ : (r : ℤ) < b := by exact_mod_cast hr
  have hr0 : (0 : ℤ) ≤ r := Int.natCast_nonneg r
  have ha0 : (0 : ℤ) ≤ a := by omega
  have hb0 : (0 : ℤ) ≤ b := by omega
  have hAB0 : (0 : ℤ) ≤ (a : ℤ) + b := by omega
  have hAB : (a : ℤ) + b ≤ 2 * b := by omega
  have habProd : (a : ℤ) * b ≤ (b : ℤ) ^ 2 := by
    have h := mul_le_mul_of_nonneg_right habZ.le hb0
    nlinarith only [h]
  have haProd : (a : ℤ) ≤ (a : ℤ) * b := by
    have h := mul_le_mul_of_nonneg_left (by omega : (1 : ℤ) ≤ b) ha0
    simpa only [mul_one] using h
  have hbProd : (b : ℤ) ≤ (a : ℤ) * b := by
    have h := mul_le_mul_of_nonneg_right haZ hb0
    simpa only [one_mul] using h
  have hzLower : (-1 : ℤ) ≤ (r : ℤ) - 1 := by omega
  have hzUpper : (r : ℤ) - 1 ≤ b := by omega
  have hcrossLower := mul_le_mul_of_nonneg_left hzLower hAB0
  have hcrossUpper₁ := mul_le_mul_of_nonneg_left hzUpper hAB0
  have hcrossUpper₂ := mul_le_mul_of_nonneg_right hAB hb0
  have hsquare : ((r : ℤ) - 1) ^ 2 ≤ (b : ℤ) ^ 2 := by
    have h := mul_nonneg (by omega : (0 : ℤ) ≤ (b : ℤ) - ((r : ℤ) - 1))
      (by omega : (0 : ℤ) ≤ (b : ℤ) + ((r : ℤ) - 1))
    nlinarith only [h]
  dsimp only [linearCoefficient, constantCoefficient]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := mul_le_mul (by omega : (1 : ℤ) ≤ (b : ℤ) - a)
      (by omega : (1 : ℤ) ≤ (b : ℤ) + r - 1) zero_le_one (by omega : (0 : ℤ) ≤ (b : ℤ) - a)
    simpa only [mul_one] using h
  · have h := mul_le_mul (by omega : (b : ℤ) - a ≤ b)
      (by omega : (b : ℤ) + r - 1 ≤ 2 * b) (by omega : (0 : ℤ) ≤ (b : ℤ) + r - 1) hb0
    nlinarith only [h]
  · nlinarith only [sq_nonneg ((r : ℤ) - 1), hcrossLower, haProd, hbProd]
  · nlinarith only [hsquare, hcrossUpper₁, hcrossUpper₂, habProd]

theorem loss_bounds {L a b m r : ℕ} (ha : 0 < a) (hab : a < b) (hm : 1 ≤ m) (hr : r < b)
    (hL : L = b * m + r) : 0 ≤ polynomialLoss L a b ∧ polynomialLoss L a b ≤ 5 * (b : ℤ) ^ 2 * m := by
  have haZ : (1 : ℤ) ≤ a := by exact_mod_cast (by omega : 1 ≤ a)
  have hbZ : (2 : ℤ) ≤ b := by exact_mod_cast (by omega : 2 ≤ b)
  have hmZ : (1 : ℤ) ≤ m := by exact_mod_cast hm
  have habZ : (a : ℤ) < b := by exact_mod_cast hab
  have hrZ : (r : ℤ) < b := by exact_mod_cast hr
  have hr0 : (0 : ℤ) ≤ r := Int.natCast_nonneg r
  have hm0 : (0 : ℤ) ≤ m := by omega
  have hb0 : (0 : ℤ) ≤ b := by omega
  have hLZ : (L : ℤ) = (b : ℤ) * m + r := by exact_mod_cast hL
  have hbm : (b : ℤ) ≤ (b : ℤ) * m := by
    have h := mul_le_mul_of_nonneg_left hmZ hb0
    simpa only [mul_one] using h
  have hLpos : (1 : ℤ) ≤ L := by nlinarith only [hLZ, hbm, hr0, hbZ]
  have hLup : (L : ℤ) ≤ 2 * (b : ℤ) * m := by nlinarith only [hLZ, hbm, hrZ]
  have hAB : (a : ℤ) + b ≤ 2 * b := by omega
  have hprod := mul_le_mul hAB hLup (Int.natCast_nonneg L) (by omega : (0 : ℤ) ≤ 2 * b)
  have habProd := mul_le_mul_of_nonneg_right habZ.le hb0
  have hbmSq := mul_le_mul_of_nonneg_left hmZ (sq_nonneg (b : ℤ))
  have hloss := mul_le_mul_of_nonneg_left (by omega : (L : ℤ) - 1 ≤ L) (by omega : (0 : ℤ) ≤ (a : ℤ) + b)
  dsimp only [polynomialLoss]
  constructor
  · exact add_nonneg (mul_nonneg (by omega) (by omega)) (by positivity)
  · nlinarith only [hprod, habProd, hbmSq, hloss]

theorem signed_formula {L a b : ℕ} (hm : 1 ≤ L / b) :
    signed L a b = (2 : ℤ) ^ (L / b - 1) *
      (linearCoefficient a b (L % b) * (L / b : ℕ) + constantCoefficient a b (L % b)) - polynomialLoss L a b := by
  unfold signed
  rw [euclidean_identity hm (-1)]
  dsimp only [linearCoefficient, constantCoefficient, polynomialLoss]
  ring

theorem quotient_bounds {L a b : ℕ} (ha : 0 < a) (hab : a < b) (hm : 1 ≤ L / b)
    (hpower : 10 * (b : ℤ) ^ 2 ≤ (2 : ℤ) ^ (L / b - 1)) :
    ((L / b : ℕ) : ℤ) * (2 : ℤ) ^ (L / b) ≤ 4 * signed L a b ∧
      signed L a b ≤ 4 * (b : ℤ) ^ 2 * (L / b : ℕ) * (2 : ℤ) ^ (L / b) := by
  have hb : 0 < b := ha.trans hab
  have hr := Nat.mod_lt L hb
  obtain ⟨hAlo, hAhi, hClo, hChi⟩ := coefficient_bounds ha hab hr
  obtain ⟨hLoss0, hLoss⟩ := loss_bounds ha hab hm hr (Nat.div_add_mod L b).symm
  let q : ℤ := (2 : ℤ) ^ (L / b - 1)
  let A : ℤ := linearCoefficient a b (L % b)
  let T : ℤ := constantCoefficient a b (L % b)
  have hq : 0 ≤ q := by positivity
  have hm0 : (0 : ℤ) ≤ (L / b : ℕ) := Int.natCast_nonneg _
  have hm1 : (1 : ℤ) ≤ (L / b : ℕ) := by exact_mod_cast hm
  have hF : signed L a b = q * (A * (L / b : ℕ) + T) - polynomialLoss L a b := signed_formula hm
  have hqPow : (2 : ℤ) ^ (L / b) = 2 * q := by
    calc
      _ = (2 : ℤ) ^ ((L / b - 1) + 1) := congrArg (fun n : ℕ ↦ (2 : ℤ) ^ n) (by omega)
      _ = _ := by rw [pow_succ]; ring
  have hAMlo : ((L / b : ℕ) : ℤ) ≤ A * (L / b : ℕ) := by
    have h := mul_le_mul_of_nonneg_right hAlo hm0
    simpa only [one_mul] using h
  have hinnerLo : ((L / b : ℕ) : ℤ) ≤ A * (L / b : ℕ) + T := by linarith only [hAMlo, hClo]
  have hlo := mul_le_mul_of_nonneg_left hinnerLo hq
  have hslow : q * (L / b : ℕ) - 5 * (b : ℤ) ^ 2 * (L / b : ℕ) ≤ signed L a b := by
    linarith only [hlo, hLoss, hF]
  have hpowerM := mul_le_mul_of_nonneg_right hpower hm0
  have hAMhi := mul_le_mul_of_nonneg_right hAhi hm0
  have hCM : 6 * (b : ℤ) ^ 2 ≤ 6 * (b : ℤ) ^ 2 * (L / b : ℕ) := by
    have h := mul_le_mul_of_nonneg_left hm1 (by positivity : (0 : ℤ) ≤ 6 * (b : ℤ) ^ 2)
    simpa only [mul_one] using h
  have hinnerHi : A * (L / b : ℕ) + T ≤ 8 * (b : ℤ) ^ 2 * (L / b : ℕ) := by
    nlinarith only [hAMhi, hChi, hCM]
  have hhi := mul_le_mul_of_nonneg_left hinnerHi hq
  rw [hqPow]
  constructor
  · nlinarith only [hslow, hpowerM]
  · nlinarith only [hhi, hF, hLoss0]

theorem length_bounds {L a b : ℕ} (ha : 0 < a) (hab : a < b) (hL : 10 * b ^ 3 ≤ L) :
    (L : ℤ) * (2 : ℤ) ^ (L / b) ≤ 8 * (b : ℤ) * signed L a b ∧
      signed L a b ≤ 4 * (b : ℤ) * L * (2 : ℤ) ^ (L / b) := by
  have hb : 0 < b := ha.trans hab
  have hmLarge : 10 * b ^ 2 ≤ L / b := by
    apply (Nat.le_div_iff_mul_le hb).mpr
    nlinarith only [hL]
  have hm : 1 ≤ L / b := by have hs := pow_pos hb 2; nlinarith only [hmLarge, hs]
  have hpNat : 10 * b ^ 2 ≤ 2 ^ (L / b - 1) := by
    have hp := Nat.lt_two_pow_self (n := L / b - 1)
    omega
  have hp : 10 * (b : ℤ) ^ 2 ≤ (2 : ℤ) ^ (L / b - 1) := by exact_mod_cast hpNat
  have hquot := quotient_bounds ha hab hm hp
  have hbm : b * (L / b) ≤ L := by have h := Nat.div_mul_le_self L b; nlinarith only [h]
  have hbmLarge : b ≤ b * (L / b) := by
    have h := Nat.mul_le_mul_left b hm
    simpa only [mul_one] using h
  have hr := Nat.mod_lt L hb
  have hident := Nat.div_add_mod L b
  have hLup : L ≤ 2 * b * (L / b) := by nlinarith only [hbmLarge, hr, hident]
  have hLupZ : (L : ℤ) ≤ 2 * (b : ℤ) * (L / b : ℕ) := by exact_mod_cast hLup
  have hbmZ : (b : ℤ) * (L / b : ℕ) ≤ L := by exact_mod_cast hbm
  have hprodLo := mul_le_mul_of_nonneg_right hLupZ (by positivity : (0 : ℤ) ≤ (2 : ℤ) ^ (L / b))
  have hquotLo := mul_le_mul_of_nonneg_left hquot.1 (by positivity : (0 : ℤ) ≤ 2 * (b : ℤ))
  have hprodHi := mul_le_mul_of_nonneg_right hbmZ
    (by positivity : (0 : ℤ) ≤ 4 * (b : ℤ) * (2 : ℤ) ^ (L / b))
  constructor
  · nlinarith only [hprodLo, hquotLo]
  · nlinarith only [hquot.2, hprodHi]

theorem signed_positive {L a b : ℕ} (ha : 0 < a) (hab : a < b) (hL : 10 * b ^ 3 ≤ L) :
    0 < signed L a b := by
  have hb : 0 < b := ha.trans hab
  have hlength : 0 < L := by have hs := pow_pos hb 3; nlinarith only [hL, hs]
  have hbound := (length_bounds ha hab hL).1
  have hpos : (0 : ℤ) < (L : ℤ) * (2 : ℤ) ^ (L / b) := mul_pos (by exact_mod_cast hlength) (by positivity)
  by_contra hnot
  have hs : signed L a b ≤ 0 := by omega
  have hn := mul_nonpos_of_nonneg_of_nonpos (by positivity : (0 : ℤ) ≤ 8 * (b : ℤ)) hs
  linarith only [hbound, hpos, hn]

end PaperP1.SignedChannelLeadingBounds
