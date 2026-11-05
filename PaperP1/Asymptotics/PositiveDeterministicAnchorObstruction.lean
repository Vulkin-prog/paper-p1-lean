module

public import PaperP1.Asymptotics.PositiveAnchorCostScale
public import PaperP1.Asymptotics.AnchoredSmallPivotCostLower
public import PaperP1.Asymptotics.PrintedAnchorObstructionParameters
public import PaperP1.Asymptotics.CriticalChannelPowers

/-! # An internal positive-constant cost obstruction for every arithmetic anchor

The actual clean source population supplies a positive fixed constant, without
an ordinary short-interval input. The full printed1-o(1) coefficient remains open.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PositiveDeterministicAnchorObstruction

open Arithmetic Model AnchoredPrivateField PrintedAnchorObstructionParameters LogFifthPivotCutoff
  AnchoredCostErrorScale

theorem uniform_lower (C D a : ℝ) (hD : 0 ≤ D) (ha : 0 < a) (ha1 : a < 1 / 10) :
    ∃ r : ℝ, 0 < r ∧ ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L : ℕ, ∀ i : Fin 2, ∀ B Y M : ℕ,
      1 ≤ L → L + i.val + 1 ≤ B → B ≤ Y → Y ≤ cutoff N →
      (B : ℝ) ≤ D * Real.log N → 2 * N + B ≤ M →
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ anchor : AnchoredDyadicField.retainedBoundaries N B Y → Fin (L + i.val + 1),
      ∀ A : Data M Y (L + i.val) (AnchoredDyadicField.retainedBoundaries N B Y) anchor,
      ∀ b : Fin (L + i.val + 1) → F₂,
        r * (rate (L + i.val)) ^ 2 * (N : ℝ) ^ (2 - a) ≤ offsite A b := by
  obtain ⟨r, hr, NR, hR⟩ := PositiveAnchorCostScale.uniform_bracket_lower C D a hD ha ha1
  obtain ⟨NC, hc⟩ := AnchoredSmallPivotCostLower.uniform_ordinary_candidates_lower
    D hD (errorExponent a) (errorExponent_pos ha1)
  obtain ⟨NZ, hz⟩ := uniform_data D (1 / 4) (by norm_num) (by norm_num)
  refine ⟨r, hr, max NR (max NC NZ), ?_⟩
  intro N hN L i B Y M hL hKB hBY hYZ hwidth hM hcrit anchor A b
  obtain ⟨_hbig, _hz, _hratio, hcollision, hupper⟩ := hz N (by omega) B (L + i.val) hwidth hKB
  have hfinite := hc N (by omega) B Y (cutoff N) (L + i.val) M ((N : ℝ) ^ a)
    (by omega) hKB hBY hwidth hYZ hupper hM hcollision anchor A b
  have hbracket := hR N (by omega) L i B hL hKB hwidth hcrit
  have hh := (mul_le_mul_of_nonneg_left hbracket (sq_nonneg (rate (L + i.val)))).trans hfinite
  convert hh using 1
  ring

theorem printed_lower (C D a : ℝ) (hD : 0 ≤ D) (ha : 0 < a) (ha1 : a < 1 / 10) :
    ∃ r : ℝ, 0 < r ∧ ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L E M : ℕ, ∀ i : Fin 2,
      ((L + E + 2 : ℕ) : ℝ) ≤ D * Real.log N → 2 * N + (L + E + 2) ≤ M →
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ anchor : AnchoredDyadicField.retainedBoundaries N (L + E + 2) (2 * (L + E + 2)) →
        Fin (L + i.val + 1),
      ∀ A : Data M (2 * (L + E + 2)) (L + i.val)
        (AnchoredDyadicField.retainedBoundaries N (L + E + 2) (2 * (L + E + 2))) anchor,
      ∀ b : Fin (L + i.val + 1) → F₂,
        r * nominal N L i.val a ≤ offsite A b := by
  obtain ⟨r, hr, NC, hc⟩ := uniform_lower C D a hD ha ha1
  obtain ⟨NP, hp⟩ := uniform_parameters C D
  refine ⟨r, hr, max NC NP, ?_⟩
  intro N hN L E M i hwidth hM hcrit anchor A b
  obtain ⟨hL, hcut⟩ := hp N (by omega) L E hcrit hwidth
  have hoff := hc N (by omega) L i (L + E + 2) (2 * (L + E + 2)) M hL
    (by have := i.isLt; omega) (by omega) hcut hwidth hM hcrit anchor A b
  rw [nominal_eq (by omega : 0 < N)]
  simpa only [mul_assoc] using hoff

theorem uniform_power_obstruction (C D α K : ℝ) (hD : 0 ≤ D) (hα : 0 < α) :
    ∃ N₀ : ℕ, ∀ N ≥ max N₀ 2, ∀ L E M : ℕ, ∀ i : Fin 2,
      ((L + E + 2 : ℕ) : ℝ) ≤ D * Real.log N → 2 * N + (L + E + 2) ≤ M →
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ anchor : AnchoredDyadicField.retainedBoundaries N (L + E + 2) (2 * (L + E + 2)) →
        Fin (L + i.val + 1),
      ∀ A : Data M (2 * (L + E + 2)) (L + i.val)
        (AnchoredDyadicField.retainedBoundaries N (L + E + 2) (2 * (L + E + 2))) anchor,
      ∀ b : Fin (L + i.val + 1) → F₂,
        K * (N : ℝ) ^ (-α) ≤ offsite A b := by
  let a := min (α / 2) (1 / 20)
  have ha : 0 < a := lt_min (by positivity) (by norm_num)
  have ha1 : a < 1 / 10 := (min_le_right _ _).trans_lt (by norm_num)
  have haα : a < α := (min_le_left _ _).trans_lt (by linarith only [hα])
  obtain ⟨r, hr, NC, hc⟩ := printed_lower C D a hD ha ha1
  let c := r * (((2 : ℝ) ^ C)⁻¹) ^ 2 / 4
  have hcpos : 0 < c := by dsimp only [c]; positivity
  obtain ⟨NP, hp⟩ := HalfCountSchedule.factor_absorption (K / c) (-α) (α - a)
    (by linarith only [haα])
  refine ⟨max NC NP, ?_⟩
  intro N hN L E M i hwidth hM hcrit anchor A b
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlower := hc N (by omega) L E M i hwidth hM hcrit anchor A b
  have hnom := (div_le_iff₀ hn).mp (CriticalChannelPowers.nominal_lower (by omega : 2 ≤ N) hcrit)
  have hNomSquare : (((2 : ℝ) ^ C)⁻¹) ^ 2 ≤ ((N : ℝ) * (2 ^ L : ℝ)⁻¹) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity)
    nlinarith only [hnom]
  have hfac : (1 / 4 : ℝ) ≤ (2 ^ (2 * i.val) : ℝ)⁻¹ := by fin_cases i <;> norm_num
  have hm := mul_le_mul hfac hNomSquare (by positivity : (0 : ℝ) ≤ (((2 : ℝ) ^ C)⁻¹) ^ 2)
    (by positivity : (0 : ℝ) ≤ (2 ^ (2 * i.val) : ℝ)⁻¹)
  have hminor : c * (N : ℝ) ^ (-a) ≤ r * nominal N L i.val a := by
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm hr.le)
      (Real.rpow_nonneg hn.le (-a))
    simpa only [c, nominal, mul_assoc, mul_left_comm, div_eq_mul_inv, one_mul] using hh
  have hpower := hp N (by omega)
  rw [show -α + (α - a) = -a by ring] at hpower
  have hmul := mul_le_mul_of_nonneg_left hpower hcpos.le
  have hid : c * (K / c * (N : ℝ) ^ (-α)) = K * (N : ℝ) ^ (-α) := by field_simp
  rw [hid] at hmul
  exact hmul.trans (hminor.trans hlower)

end PaperP1.PositiveDeterministicAnchorObstruction
