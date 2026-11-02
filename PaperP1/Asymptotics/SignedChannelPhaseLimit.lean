module

public import PaperP1.Arithmetic.ChannelPhaseConstants
public import Mathlib.Analysis.SpecificLimits.Basic

/-! # Exact normalized channel identities and limits along a fixed residue

The original integer signed sum is normalized explicitly. Its lower-degree
terms tend to zero by the reciprocal-natural and geometric limits.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SignedChannelPhaseLimit

open Finset Filter PaperP1.ChannelSumIdentity PaperP1.FiniteChannelHierarchy
  PaperP1.ChannelPhaseConstants

def linearTerm (a b r : ℕ) : ℝ := ((b : ℝ) - a) * ((b : ℝ) + r - 1)

def constantTerm (a b r : ℕ) : ℝ :=
  ((r : ℝ) - 1) ^ 2 + ((a : ℝ) + b) * ((r : ℝ) - 1) + 3 * (a : ℝ) * b

def lossSlope (a b : ℕ) : ℝ := ((a : ℝ) + b) * b

def lossConstant (a b r : ℕ) : ℝ := ((a : ℝ) + b) * ((r : ℝ) - 1) + (a : ℝ) * b

theorem signed_euclidean {a b q r : ℕ} (hq : 1 ≤ q) (hr : r < b) :
    (signed (b * q + r) a b : ℝ) =
      (2 : ℝ) ^ (q - 1) * (linearTerm a b r * q + constantTerm a b r) -
        lossSlope a b * q - lossConstant a b r := by
  have hb : 0 < b := by omega
  have hdiv : (b * q + r) / b = q := by
    rw [Nat.mul_add_div hb, Nat.div_eq_of_lt hr, add_zero]
  unfold signed
  rw [hdiv, channel_identity hq _ _ _ (r : ℤ) _ (by push_cast; ring)]
  push_cast
  unfold linearTerm constantTerm lossSlope lossConstant
  ring

theorem normalized_identity {a b q r : ℕ} (hq : 1 ≤ q) (hr : r < b) :
    (signed (b * q + r) a b : ℝ) / ((q : ℝ) * (2 : ℝ) ^ q) =
      linearTerm a b r / 2 + (constantTerm a b r / 2) * (q : ℝ)⁻¹ -
        lossSlope a b * (1 / 2 : ℝ) ^ q -
          lossConstant a b r * ((q : ℝ)⁻¹ * (1 / 2 : ℝ) ^ q) := by
  rw [signed_euclidean hq hr]
  have hqn : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
  have hp : (2 : ℝ) ^ (q - 1) = (2 : ℝ) ^ q / 2 := by
    have heq : (2 : ℝ) ^ q = (2 : ℝ) ^ (q - 1) * 2 := by
      rw [← pow_succ, Nat.sub_add_cancel hq]
    rw [heq]
    ring
  have hg : (1 / 2 : ℝ) ^ q = 1 / (2 : ℝ) ^ q := by rw [div_pow, one_pow]
  rw [hp, hg]
  field_simp

theorem tendsto_normalized (a b r : ℕ) (hr : r < b) :
    Tendsto (fun q : ℕ ↦ (signed (b * q + r) a b : ℝ) / ((q : ℝ) * (2 : ℝ) ^ q))
      atTop (nhds (linearTerm a b r / 2)) := by
  have hi : Tendsto (fun q : ℕ ↦ (q : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hg : Tendsto (fun q : ℕ ↦ (1 / 2 : ℝ) ^ q) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have ht := (((tendsto_const_nhds (x := linearTerm a b r / 2)).add
    (hi.const_mul (constantTerm a b r / 2))).sub (hg.const_mul (lossSlope a b))).sub
      ((hi.mul hg).const_mul (lossConstant a b r))
  have ht' : Tendsto (fun q : ℕ ↦ linearTerm a b r / 2 +
      (constantTerm a b r / 2) * (q : ℝ)⁻¹ - lossSlope a b * (1 / 2 : ℝ) ^ q -
        lossConstant a b r * ((q : ℝ)⁻¹ * (1 / 2 : ℝ) ^ q)) atTop
      (nhds (linearTerm a b r / 2)) := by
    simpa only [mul_zero, add_zero, sub_zero] using ht
  apply ht'.congr'
  filter_upwards [eventually_ge_atTop 1] with q hq
  exact (normalized_identity hq hr).symm

theorem weighted_linear_identity (b r : ℕ) (hb : 3 ≤ b) :
    (∑ a ∈ numerators b, FiniteChannelHierarchy.weight a b * (linearTerm a b r / 2)) =
      (((b : ℝ) + r - 1) / b) * phaseSum b := by
  rw [phaseSum, mul_sum]
  apply sum_congr rfl
  intro a ha
  have ha1 := (mem_Icc.mp (mem_filter.mp ha).1).1
  have haR : (a : ℝ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
  have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast (show b ≠ 0 by omega)
  rw [FiniteChannelHierarchy.weight_formula, linearTerm]
  field_simp

theorem tendsto_height_normalized (b r : ℕ) (hb : 3 ≤ b) (hr : r < b) :
    Tendsto (fun q : ℕ ↦ heightSum b (b * q + r) / ((q : ℝ) * (2 : ℝ) ^ q))
      atTop (nhds ((((b : ℝ) + r - 1) / b) * phaseSum b)) := by
  have ht := tendsto_finsetSum (numerators b) (fun a _ ↦
    (tendsto_normalized a b r hr).const_mul (FiniteChannelHierarchy.weight a b))
  rw [weighted_linear_identity b r hb] at ht
  convert ht using 1
  funext q
  rw [heightSum, sum_div]
  apply sum_congr rfl
  intro a _
  ring

end PaperP1.SignedChannelPhaseLimit
