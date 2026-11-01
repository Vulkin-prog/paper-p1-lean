module

public import PaperP1.Asymptotics.LatePrimeRankDensity
public import Mathlib.Data.Nat.Log

/-! # The actual logarithmic peeling order and its positive-mass error -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LatePeelingOrder

open Finset Filter PaperP1.Model PaperP1.PrimeCylinderScale
  PaperP1.LatePrimePopulation PaperP1.LatePrimeStarts

def order (q : ℕ) : ℕ := Nat.log 2 (q - 1) / 2

def loss (q : ℕ) : ℝ := ((population q).card : ℝ) * (2 ^ (q - 1) : ℝ)⁻¹ * 2 ^ order q

theorem order_le_length (q : ℕ) : order q ≤ q - 1 :=
  (Nat.div_le_self _ _).trans (Nat.log_le_self 2 (q - 1))

theorem order_tendsto : Tendsto order atTop atTop := by
  refine tendsto_atTop.mpr fun k ↦ ?_
  refine eventually_atTop.mpr ⟨2 ^ (2 * k) + 1, ?_⟩
  intro q hq
  have hpow : 2 ^ (2 * k) ≤ q - 1 := by omega
  have hlog := Nat.le_log_of_pow_le (by norm_num : 1 < 2) hpow
  change k ≤ Nat.log 2 (q - 1) / 2
  omega

theorem order_positive_eventually : ∀ᶠ q : ℕ in atTop, 1 ≤ order q :=
  order_tendsto.eventually (eventually_ge_atTop 1)

theorem pow_order_le_sqrt {q : ℕ} (hq : 2 ≤ q) :
    (2 ^ order q : ℝ) ≤ Real.sqrt (q - 1 : ℕ) := by
  have hindex : 2 * order q ≤ Nat.log 2 (q - 1) := by
    have h := Nat.div_mul_le_self (Nat.log 2 (q - 1)) 2
    unfold order
    omega
  have hnat : 2 ^ (2 * order q) ≤ q - 1 :=
    (Nat.pow_le_pow_right (by norm_num : 0 < 2) hindex).trans
      (Nat.pow_log_le_self 2 (by omega : q - 1 ≠ 0))
  apply Real.le_sqrt_of_sq_le
  rw [← pow_mul, Nat.mul_comm (order q) 2]
  exact_mod_cast hnat

theorem loss_nonneg (q : ℕ) : 0 ≤ loss q := by unfold loss; positivity

/-- The error coefficient uses the actual population and the actual integer order. -/
theorem loss_bound {q : ℕ} (hq : 2 ≤ q) : loss q ≤ 2 / Real.sqrt (q - 1 : ℕ) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hn : (0 : ℝ) < size q := by exact_mod_cast size_pos q
  have hL : (0 : ℝ) < (q - 1 : ℕ) := by exact_mod_cast (show 0 < q - 1 by omega)
  have hroot := Real.sqrt_pos.mpr hL
  have hcard : ((population q).card : ℝ) ≤ (size q : ℝ) / (2 * q) + 1 := by
    have hsub : ((population q).card : ℝ) ≤ (starts (size q) q).card := by
      exact_mod_cast card_le_card (population_subset q)
    exact hsub.trans (card_bounds (N := size q) (by omega : 0 < q)).2
  have hLq : ((q - 1 : ℕ) : ℝ) ≤ q := by exact_mod_cast Nat.sub_le q 1
  have hLN : ((q - 1 : ℕ) : ℝ) ≤ size q := by
    exact_mod_cast (Nat.sub_le q 1).trans (index_le_size (by omega : 1 ≤ q))
  have hfirst : ((q - 1 : ℕ) : ℝ) / (2 * q) ≤ 1 / 2 :=
    (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * q)).mpr (by linarith)
  have hsecond : ((q - 1 : ℕ) : ℝ) / size q ≤ 1 :=
    (div_le_iff₀ hn).mpr (by simpa only [one_mul] using hLN)
  calc
    loss q = (((population q).card : ℝ) / size q) * 2 ^ order q := by
      unfold loss
      rw [size_cast]
      ring
    _ ≤ (((size q : ℝ) / (2 * q) + 1) / size q) * Real.sqrt (q - 1 : ℕ) :=
      mul_le_mul (div_le_div_of_nonneg_right hcard hn.le) (pow_order_le_sqrt hq)
        (by positivity) (by positivity)
    _ ≤ 2 / Real.sqrt (q - 1 : ℕ) := by
      apply (le_div_iff₀ hroot).mpr
      have hid : ((((size q : ℝ) / (2 * q) + 1) / size q) * Real.sqrt (q - 1 : ℕ)) *
          Real.sqrt (q - 1 : ℕ) = ((q - 1 : ℕ) : ℝ) / (2 * q) + ((q - 1 : ℕ) : ℝ) / size q := by
        rw [mul_assoc, Real.mul_self_sqrt hL.le]
        field_simp
      rw [hid]
      linarith

theorem loss_tendsto_zero : Tendsto loss atTop (nhds 0) := by
  have hlength : Tendsto (fun q : ℕ ↦ q - 1) atTop atTop := by
    refine tendsto_atTop.mpr fun k ↦ eventually_atTop.mpr ⟨k + 1, ?_⟩
    intro q hq
    omega
  have hreal := (tendsto_natCast_atTop_atTop (R := ℝ)).comp hlength
  have hsqrt := Real.tendsto_sqrt_atTop.comp hreal
  have hupper : Tendsto (fun q : ℕ ↦ 2 / Real.sqrt (q - 1 : ℕ)) atTop (nhds (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop hsqrt
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    (Eventually.of_forall loss_nonneg) (by filter_upwards [eventually_ge_atTop 2] with q hq; exact loss_bound hq)

end PaperP1.LatePeelingOrder
