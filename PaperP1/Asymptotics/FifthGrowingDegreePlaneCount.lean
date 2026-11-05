module

public import PaperP1.Arithmetic.FifthDegreeUniformFieldCount
public import PaperP1.Analysis.BinaryLogarithmicBudget
public import PaperP1.Asymptotics.HalfCountSchedule

/-! # An unconditional quantitative growing-degree range below the fifth power barrier

This does not supply the full source range a<1/2 or the nonaligned rank theorem.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FifthGrowingDegreePlaneCount

open Polynomial Finset DegreeUniformAffineParameters FifthDegreeUniformFieldCount

theorem power_cap (a : ℝ) (ha₁ : a < 1 / 5) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ D : ℕ, 2 ≤ D → (D : ℝ) ≤ (N : ℝ) ^ a →
      ∀ (F : Type*) [Field F] [CharZero F], ∀ P : F[X][X],
      PlaneCurvePointCount.degree P = D → Irreducible P →
      ((PlaneCurvePointCount.grid P N).card : ℝ) ≤ ε * N := by
  let g := 1 - 5 * a
  have hg : 0 < g := by dsimp [g]; linarith only [ha₁]
  obtain ⟨M, hM⟩ := exists_nat_gt (max 2 (4 / g))
  have hM2 : (2 : ℝ) < M := (le_max_left _ _).trans_lt hM
  have hMp : (0 : ℝ) < M := by linarith only [hM2]
  have hprod : (4 : ℝ) < (M : ℝ) * g :=
    (div_lt_iff₀ hg).mp ((le_max_right _ _).trans_lt hM)
  have hfrac : 1 / (M : ℝ) ≤ g / 4 := (div_le_iff₀ hMp).mpr (by nlinarith only [hprod])
  obtain ⟨C, hC, hcount⟩ := global_field_count
  obtain ⟨NS, _hNS, hs⟩ := BinaryLogarithmicBudget.polynomial_absorption
    (C * (M : ℝ) ^ 5) 2 (1 / 4) (by norm_num)
  obtain ⟨NT, _hNT, ht⟩ := BinaryLogarithmicBudget.polynomial_absorption C 2 (g / 4) (by positivity)
  let b := max (3 / 4 : ℝ) (5 * a + g / 2)
  have hb : b < 1 := max_lt (by norm_num) (by dsimp [g]; linarith only [ha₁])
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption (1 / ε) b (1 - b) (by linarith only [hb])
  refine ⟨3 + NS + NT + NF, by omega, ?_⟩
  intro N hN D hD hcap F _hF _hchar P hdegree hP
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hD2 : (2 : ℝ) ≤ D := by exact_mod_cast hD
  have hbase := hcount D N hD (by omega) F P hdegree hP
  let L := logarithmicBudget N
  have hbound : ((PlaneCurvePointCount.grid P N).card : ℝ) ≤ (N : ℝ) ^ b := by
    by_cases hDM : D ≤ M
    · have hcoef : C * (D : ℝ) ^ 5 * (L : ℝ) ^ 2 ≤ (N : ℝ) ^ (1 / 4 : ℝ) := by
        have hh := (le_abs_self (C * (M : ℝ) ^ 5 * (L : ℝ) ^ 2)).trans (hs N (by omega))
        have hd : (D : ℝ) ^ 5 ≤ (M : ℝ) ^ 5 :=
          pow_le_pow_left₀ (Nat.cast_nonneg _) (by exact_mod_cast hDM) 5
        exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd hC.le) (by positivity)).trans hh
      have hroot : (N : ℝ) ^ (1 / (D : ℝ)) ≤ (N : ℝ) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hn1 (one_div_le_one_div_of_le (by norm_num) hD2)
      calc
        _ ≤ (C * (D : ℝ) ^ 5 * (L : ℝ) ^ 2) * (N : ℝ) ^ (1 / (D : ℝ)) := by
          simpa only [profile, mul_assoc] using hbase
        _ ≤ (N : ℝ) ^ (1 / 4 : ℝ) * (N : ℝ) ^ (1 / 2 : ℝ) :=
          mul_le_mul hcoef hroot (by positivity) (by positivity)
        _ = (N : ℝ) ^ (3 / 4 : ℝ) := by rw [← Real.rpow_add hn]; norm_num
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 (le_max_left _ _)
    · have hMD : (M : ℝ) ≤ D := by exact_mod_cast (show M ≤ D by omega)
      have hroot : (N : ℝ) ^ (1 / (D : ℝ)) ≤ (N : ℝ) ^ (g / 4) :=
        Real.rpow_le_rpow_of_exponent_le hn1
          ((one_div_le_one_div_of_le hMp hMD).trans hfrac)
      have hdeg : (D : ℝ) ^ 5 ≤ (N : ℝ) ^ (5 * a) := by
        apply (pow_le_pow_left₀ (Nat.cast_nonneg _) hcap 5).trans_eq
        rw [← Real.rpow_mul_natCast hn.le]
        congr 1
        ring
      have hcoef : C * (L : ℝ) ^ 2 ≤ (N : ℝ) ^ (g / 4) :=
        (le_abs_self _).trans (ht N (by omega))
      calc
        _ ≤ (C * (L : ℝ) ^ 2) * (D : ℝ) ^ 5 * (N : ℝ) ^ (1 / (D : ℝ)) := by
          convert hbase using 1
          dsimp only [profile, L]
          ring
        _ ≤ (N : ℝ) ^ (g / 4) * (N : ℝ) ^ (5 * a) * (N : ℝ) ^ (g / 4) := by gcongr
        _ = (N : ℝ) ^ (5 * a + g / 2) := by rw [← Real.rpow_add hn, ← Real.rpow_add hn]; congr 1; ring
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 (le_max_right _ _)
  have hfinal := hf N (by omega)
  rw [show b + (1 - b) = 1 by ring, Real.rpow_one] at hfinal
  have hquot : (N : ℝ) ^ b / ε ≤ N := by simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul, mul_one] using hfinal
  have hh := (div_le_iff₀ hε).mp hquot
  exact hbound.trans (by simpa only [mul_comm] using hh)


theorem scaled_power_cap (c₀ a : ℝ) (hc₀ : 0 < c₀) (ha : 0 ≤ a)
    (ha₁ : a < 1 / 5) (ε : ℝ) (hε : 0 < ε) :
    ∃ B₀ : ℕ, 3 ≤ B₀ ∧ ∀ B ≥ B₀, ∀ D : ℕ, 2 ≤ D → (D : ℝ) ≤ (B : ℝ) ^ a →
      ∀ (F : Type*) [Field F] [CharZero F], ∀ P : F[X][X],
      PlaneCurvePointCount.degree P = D → Irreducible P →
      ((PlaneCurvePointCount.grid P ⌊c₀ * B⌋₊).card : ℝ) ≤ ε * B := by
  let b := (a + 1 / 5) / 2
  let c := c₀ / 2
  have hb : 0 < b := by dsimp [b]; linarith only [ha]
  have hb₁ : b < 1 / 5 := by dsimp [b]; linarith only [ha₁]
  have hab : a < b := by dsimp [b]; linarith only [ha₁]
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨N₀, hN₀, hcount⟩ := power_cap b hb₁ (ε / c₀) (by positivity)
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption (1 / (c ^ b)) a (b - a) (by linarith only [hab])
  let B₀ := ⌈((2 * (N₀ + 2) : ℕ) : ℝ) / c₀⌉₊ + NF + 3
  refine ⟨B₀, by dsimp [B₀]; omega, ?_⟩
  intro B hB D hD hcap F _hF _hchar P hdegree hP
  have hceil : (((2 * (N₀ + 2) : ℕ) : ℝ) / c₀) ≤ (B : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast (show ⌈((2 * (N₀ + 2) : ℕ) : ℝ) / c₀⌉₊ ≤ B by dsimp [B₀] at hB; omega))
  have hscale : ((2 * (N₀ + 2) : ℕ) : ℝ) ≤ c₀ * B := by
    have hh := (div_le_iff₀ hc₀).mp hceil
    nlinarith only [hh]
  push_cast at hscale
  let N := ⌊c₀ * B⌋₊
  have hfloor : c₀ * B < (N : ℝ) + 1 := Nat.lt_floor_add_one _
  have hNat : N₀ ≤ N := by
    have hh : (N₀ : ℝ) ≤ N := by nlinarith only [hscale, hfloor, Nat.cast_nonneg (α := ℝ) N₀]
    exact_mod_cast hh
  have hN : 1 ≤ N := by omega
  have hhalf : c * B ≤ (N : ℝ) := by
    dsimp only [c]
    nlinarith only [hscale, hfloor, Nat.cast_nonneg (α := ℝ) N₀]
  have hpower : (B : ℝ) ^ a / (c ^ b) ≤ (B : ℝ) ^ b := by
    have hh := hf B (by dsimp [B₀] at hB; omega)
    rw [show a + (b - a) = b by ring] at hh
    simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul, mul_one] using hh
  have hpow : (B : ℝ) ^ a ≤ (c * B) ^ b := by
    calc
      _ ≤ (B : ℝ) ^ b * c ^ b := (div_le_iff₀ (Real.rpow_pos_of_pos hc b)).mp hpower
      _ = _ := by rw [Real.mul_rpow hc.le (Nat.cast_nonneg B)]; ring
  have hnewcap : (D : ℝ) ≤ (N : ℝ) ^ b := hcap.trans
    (hpow.trans (Real.rpow_le_rpow (by positivity) hhalf hb.le))
  have hresult := hcount N hNat D hD hnewcap F P hdegree hP
  have hupper : (N : ℝ) ≤ c₀ * B := Nat.floor_le (by positivity)
  calc
    _ ≤ (ε / c₀) * N := hresult
    _ ≤ (ε / c₀) * (c₀ * B) := mul_le_mul_of_nonneg_left hupper (by positivity)
    _ = (ε / c₀ * c₀) * B := by ring
    _ = ε * B := by rw [div_mul_cancel₀ ε hc₀.ne']

theorem growing_cap (c₀ a : ℝ) (hc₀ : 0 < c₀) (ha : 0 ≤ a) (ha₁ : a < 1 / 5)
    (cap : ℕ → ℝ) (hcap : PlaneCurvePointCount.UpperPowerCap a cap) (ε : ℝ) (hε : 0 < ε) :
    ∃ B₀ : ℕ, 3 ≤ B₀ ∧ ∀ B ≥ B₀, ∀ D : ℕ, 2 ≤ D → (D : ℝ) ≤ cap B →
      ∀ (F : Type*) [Field F] [CharZero F], ∀ P : F[X][X],
      PlaneCurvePointCount.degree P = D → Irreducible P →
      ((PlaneCurvePointCount.grid P ⌊c₀ * B⌋₊).card : ℝ) ≤ ε * B := by
  let b := (a + 1 / 5) / 2
  have hb : 0 ≤ b := by dsimp [b]; linarith only [ha]
  have hb₁ : b < 1 / 5 := by dsimp [b]; linarith only [ha₁]
  have hab : 0 < b - a := by dsimp [b]; linarith only [ha₁]
  obtain ⟨NC, hc⟩ := hcap (b - a) hab
  obtain ⟨NS, hNS, hs⟩ := scaled_power_cap c₀ b hc₀ hb hb₁ ε hε
  refine ⟨max NC NS, by omega, ?_⟩
  intro B hB D hD hDcap F _hF _hchar P hdegree hP
  have hbound := hc B (by omega)
  rw [show a + (b - a) = b by ring] at hbound
  exact hs B (by omega) D hD (hDcap.trans hbound) F P hdegree hP

end PaperP1.FifthGrowingDegreePlaneCount
