module

public import PaperP1.Arithmetic.SmoothLowerBarrierBase
public import PaperP1.Arithmetic.SmoothQuotientGeometry
public import PaperP1.Arithmetic.SmoothLowerPrimeMargin

/-! # An actual smooth-count lower barrier by integer induction

Every quotient is an actual natural quotient. The final uniform theorem
supplies its base range and prime margin internally.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SmoothLowerBarrierInduction

open Finset OrdinarySmoothCensus DefectCounting SmoothPrimeIncidence
  SmoothLowerBarrierProfile SmoothQuotientGeometry

theorem finite_lower (ε T a : ℝ) (M Y : ℕ) (hε : 0 ≤ ε) (hT : Real.exp 1 + 1 ≤ T)
    (ha : 0 ≤ a) (hM : 1 ≤ M) (hY : 2 ≤ Y)
    (hbase : ∀ X : ℕ, 1 ≤ X → Real.log X / Real.log Y ≤ T + 1 →
      a * X * density ε T (Real.log X / Real.log Y) ≤ (smoothUpTo X Y).card)
    (hprime : ∀ t ≥ T, tilt ε (t - 1) ≤ Real.log Y →
      t * Real.log Y ≤ (1 - 1 / (Y : ℝ)) *
        WeightedPrimeSum.logPrimeSum Y (1 - tilt ε (t - 1) / Real.log Y))
    (hcap : tilt ε (max T (Real.log M / Real.log Y)) ≤ Real.log Y) :
    a * M * density ε T (Real.log M / Real.log Y) ≤ (smoothUpTo M Y).card := by
  have hTe : Real.exp 1 ≤ T := by linarith only [hT]
  have hT1 : 1 ≤ T := by have hh := Real.exp_pos 1; linarith only [hT, hh]
  have hy : (1 : ℝ) < Y := by exact_mod_cast (show 1 < Y by omega)
  have hy0 : (0 : ℝ) < Y := by linarith only [hy]
  have hlogY : 0 < Real.log Y := Real.log_pos hy
  have hfloor : 0 ≤ 1 - 1 / (Y : ℝ) := by
    have hh : 1 / (Y : ℝ) ≤ 1 := (div_le_iff₀ hy0).mpr (by simpa only [one_mul] using hy.le)
    linarith only [hh]
  have hAll : ∀ X : ℕ, X ≤ M → 1 ≤ X →
      a * X * density ε T (Real.log X / Real.log Y) ≤ (smoothUpTo X Y).card := by
    intro X
    induction X using Nat.strong_induction_on with
    | h X ih =>
      intro hXM hX
      let t := Real.log X / Real.log Y
      by_cases hsmall : t ≤ T + 1
      · exact hbase X hX hsmall
      · have ht : T + 1 < t := lt_of_not_ge hsmall
        have ht2 : 2 < t := by linarith only [ht, hT1]
        have hx : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
        have hsquare : Y ^ 2 ≤ X := square_le_of_ratio hX hY ht2.le
        have hYX : Y ≤ X := by nlinarith only [hsquare, hY]
        have hlogX : 0 < Real.log X := Real.log_pos (by exact_mod_cast (show 1 < X by omega))
        let ξ := tilt ε (t - 1)
        let δ := ξ / Real.log Y
        have hξcap : ξ ≤ Real.log Y := by
          have htM : t ≤ Real.log M / Real.log Y :=
            div_le_div_of_nonneg_right (Real.log_le_log hx (by exact_mod_cast hXM)) hlogY.le
          have hmax : 1 < max T (Real.log M / Real.log Y) := by
            have hh := le_max_left T (Real.log M / Real.log Y)
            linarith only [hT1, hh, ht2, htM, le_max_right T (Real.log M / Real.log Y)]
          exact (tilt_monotone ε (by change 1 < t - 1; linarith only [ht2]) hmax
            (by linarith only [htM, le_max_right T (Real.log M / Real.log Y)] : t - 1 ≤ max T (Real.log M / Real.log Y))).trans hcap
        have hcounts (p : ℕ) (hp : p ∈ smallPrimesUpTo Y) :
            a * X * density ε T t * (1 - 1 / (Y : ℝ)) * (p : ℝ) ^ (-(1 - δ)) ≤
              (smoothUpTo (X / p) Y).card := by
          obtain ⟨hpp, hpy⟩ := mem_smallPrimesUpTo.mp hp
          have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
          have hpx : p ≤ X := hpy.trans hYX
          have hq : 1 ≤ X / p := Nat.div_pos hpx hpp.pos
          have hqX : X / p < X := Nat.div_lt_self (by omega : 0 < X) hpp.one_lt
          have hqM : X / p ≤ M := (Nat.div_le_self X p).trans hXM
          have hi := ih (X / p) hqX hqM hq
          let s := Real.log p / Real.log Y
          have hs : 0 ≤ s := div_nonneg (Real.log_natCast_nonneg p) hlogY.le
          have hs1 : s ≤ 1 := (div_le_iff₀ hlogY).mpr
            (by simpa only [one_mul] using Real.log_le_log hp0 (by exact_mod_cast hpy))
          have hexp : Real.exp (s * ξ) = (p : ℝ) ^ δ := by
            rw [Real.rpow_def_of_pos hp0]
            congr 1
            dsimp only [s, δ]
            ring
          have hshift := density_shift ε T t s hTe ht.le hs hs1
          rw [hexp] at hshift
          have hquot := log_quotient_upper hY hpp.pos hpx
          have hDensity : density ε T t * (p : ℝ) ^ δ ≤ density ε T (Real.log ((X / p : ℕ) : ℝ) / Real.log Y) :=
            hshift.trans (density_antitone ε T hε hTe hquot)
          have hrelative := quotient_relative_lower hY hpp.pos hpy hsquare
          have hprod := mul_le_mul hrelative hDensity
            (mul_nonneg (density_pos ε T t).le (Real.rpow_nonneg hp0.le δ))
            (Nat.cast_nonneg (α := ℝ) (X / p))
          have hprodA := mul_le_mul_of_nonneg_left hprod ha
          have hid : a * ((1 - 1 / (Y : ℝ)) * (X : ℝ) / p * (density ε T t * (p : ℝ) ^ δ)) =
              a * X * density ε T t * (1 - 1 / (Y : ℝ)) * (p : ℝ) ^ (-(1 - δ)) := by
            rw [show -(1 - δ) = δ - 1 by ring, Real.rpow_sub hp0, Real.rpow_one]
            ring
          rw [hid] at hprodA
          exact hprodA.trans (by simpa only [mul_assoc] using hi)
        have hweighted : (a * X * density ε T t) * (1 - 1 / (Y : ℝ)) * WeightedPrimeSum.logPrimeSum Y (1 - δ) ≤
            Real.log X * (smoothUpTo X Y).card := by
          calc
            _ = ∑ p ∈ smallPrimesUpTo Y, Real.log p *
                (a * X * density ε T t * (1 - 1 / (Y : ℝ)) * (p : ℝ) ^ (-(1 - δ))) := by
              rw [WeightedPrimeSum.logPrimeSum, mul_sum]
              apply sum_congr rfl
              intro p _
              ring
            _ ≤ ∑ p ∈ smallPrimesUpTo Y, Real.log p * ((smoothUpTo (X / p) Y).card : ℝ) := by
              apply sum_le_sum
              intro p hp
              exact mul_le_mul_of_nonneg_left (hcounts p hp) (Real.log_natCast_nonneg p)
            _ ≤ _ := weighted_recursion X Y
        have hmargin := hprime t (by linarith only [ht] : T ≤ t) hξcap
        have hid : t * Real.log Y = Real.log X := by dsimp only [t]; field_simp
        rw [hid] at hmargin
        have hscaled := mul_le_mul_of_nonneg_left hmargin
          (mul_nonneg (mul_nonneg ha (Nat.cast_nonneg X)) (density_pos ε T t).le)
        have hb : (a * X * density ε T t) * Real.log X ≤ Real.log X * (smoothUpTo X Y).card :=
          hscaled.trans (by simpa only [mul_assoc] using hweighted)
        apply (mul_le_mul_iff_left₀ hlogX).mp
        nlinarith only [hb]
  exact hAll M le_rfl hM

theorem uniform_lower (ε : ℝ) (hε : 0 < ε) :
    ∃ a T : ℝ, 0 < a ∧ Real.exp 1 + 1 ≤ T ∧ ∃ Y₀ : ℕ, 2 ≤ Y₀ ∧
      ∀ Y ≥ Y₀, ∀ M : ℕ, 1 ≤ M →
        tilt ε (max T (Real.log M / Real.log Y)) ≤ Real.log Y →
        a * M * density ε T (Real.log M / Real.log Y) ≤ (smoothUpTo M Y).card := by
  obtain ⟨T, hT, YP, hYP, hp⟩ := SmoothLowerPrimeMargin.uniform_weighted_margin ε hε
  obtain ⟨a, ha, _ha1, YB, hYB, hb⟩ := SmoothLowerBarrierBase.uniform_base ε T hε.le (by linarith only [hT])
  refine ⟨a, T, ha, hT, max YP YB, by omega, ?_⟩
  intro Y hY M hM hcap
  exact finite_lower ε T a M Y hε.le hT ha.le hM (by omega)
    (hb Y (by omega)) (hp Y (by omega)) hcap

end PaperP1.SmoothLowerBarrierInduction
