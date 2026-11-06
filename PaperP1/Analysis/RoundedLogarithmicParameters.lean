module

public import PaperP1.Analysis.SparseGramEnvelope
public import PaperP1.Analysis.FixedOrderLogarithmicScale

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.RoundedLogarithmicParameters
open Filter PaperP1 FixedOrderLogarithmicScale

def step (n X : ℕ) (t : ℝ) : ℕ := ⌊scale n (X : ℝ) |t|⌋₊

def count (n X : ℕ) : ℕ := ⌊(X : ℝ)^(exponent n)⌋₊

theorem count_tendsto (n : ℕ) (hn : 0 < n) : Tendsto (count n) atTop atTop := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have he : 0 < exponent n := by unfold exponent; positivity
  have hPow := (tendsto_rpow_atTop he).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  apply tendsto_atTop.2
  intro b
  filter_upwards [hPow.eventually (eventually_ge_atTop (b : ℝ))] with X hX
  exact Nat.le_floor hX

theorem product_bound (n X : ℕ) (hn : 0 < n) (hX : 1 ≤ X) (t : ℝ)
    (hLower : (X : ℝ)^(3/4 : ℝ) ≤ |t|) (hUpper : |t| ≤ (X : ℝ)^((n : ℝ)+1/4)) :
    ((step n X t*count n X : ℕ) : ℝ) ≤ (X : ℝ)^(1-3/(16*(n : ℝ))) := by
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hXp : (0 : ℝ) < X := by linarith only [hXR]
  have ht : 0 < |t| := (Real.rpow_pos_of_pos hXp (3/4 : ℝ)).trans_le hLower
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hScale := scale_bounds n hn X |t| hXR ht hLower hUpper
  have hA : (step n X t : ℝ) ≤ scale n X |t| := Nat.floor_le (scale_pos n X |t| hXp ht).le
  have hK : (count n X : ℝ) ≤ (X : ℝ)^(exponent n) := Nat.floor_le (Real.rpow_nonneg hXp.le _)
  have hProd := mul_le_mul hA hK (Nat.cast_nonneg (count n X)) (scale_pos n X |t| hXp ht).le
  calc
    _ = (step n X t : ℝ)*(count n X : ℝ) := by rw [Nat.cast_mul]
    _ ≤ scale n X |t| *(X : ℝ)^(exponent n) := hProd
    _ ≤ (X : ℝ)^(1-1/(4*(n : ℝ)))*(X : ℝ)^(exponent n) :=
      mul_le_mul_of_nonneg_right hScale.2 (Real.rpow_nonneg hXp.le _)
    _ = _ := by
      rw [← Real.rpow_add hXp]
      congr 1
      unfold exponent
      field_simp
      ring


theorem geometry_eventually (n : ℕ) (hn : 0 < n) : ∀ᶠ X : ℕ in atTop,
    1 ≤ X ∧ 1 ≤ count n X ∧
    (X : ℝ)^(exponent n)/2 ≤ (count n X : ℝ) ∧ (count n X : ℝ) ≤ (X : ℝ)^(exponent n) ∧
    ∀ t : ℝ, (X : ℝ)^(3/4 : ℝ) ≤ |t| → |t| ≤ (X : ℝ)^((n : ℝ)+1/4) →
      0 < |t| ∧ 1 ≤ step n X t ∧
      scale n X |t|/2 ≤ (step n X t : ℝ) ∧ (step n X t : ℝ) ≤ scale n X |t| ∧
      step n X t*count n X ≤ X ∧ n*(step n X t*count n X) ≤ X := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hNat := tendsto_natCast_atTop_atTop (R := ℝ)
  have hBeta := (tendsto_rpow_atTop (show 0 < exponent n by unfold exponent; positivity)).comp hNat
  have hQuarter := (tendsto_rpow_atTop (show (0 : ℝ) < 1/(4*(n : ℝ)) by positivity)).comp hNat
  have hAlpha := (tendsto_rpow_atTop (show (0 : ℝ) < 3/(16*(n : ℝ)) by positivity)).comp hNat
  filter_upwards [eventually_ge_atTop 1,hBeta.eventually (eventually_ge_atTop 2),
    hQuarter.eventually (eventually_ge_atTop 2),hAlpha.eventually (eventually_ge_atTop (n : ℝ))] with X hX hB hQ hC
  change 2 ≤ (X : ℝ)^(exponent n) at hB
  change 2 ≤ (X : ℝ)^(1/(4*(n : ℝ))) at hQ
  change (n : ℝ) ≤ (X : ℝ)^(3/(16*(n : ℝ))) at hC
  have hCount := floor_half_bounds ((X : ℝ)^(exponent n)) hB
  refine ⟨hX,hCount.2.2,hCount.1,hCount.2.1,?_⟩
  intro t hLower hUpper
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hXp : (0 : ℝ) < X := by linarith only [hXR]
  have ht : 0 < |t| := (Real.rpow_pos_of_pos hXp (3/4 : ℝ)).trans_le hLower
  have hScale := scale_bounds n hn X |t| hXR ht hLower hUpper
  have hStep := floor_half_bounds (scale n X |t|) (hQ.trans hScale.1)
  have hProd := product_bound n X hn hX t hLower hUpper
  have hExponent : (1 : ℝ)-3/(16*(n : ℝ)) ≤ 1 := by
    have hh : (0 : ℝ) ≤ 3/(16*(n : ℝ)) := by positivity
    linarith only [hh]
  have hPower := Real.rpow_le_rpow_of_exponent_le hXR hExponent
  rw [Real.rpow_one] at hPower
  have hAKR := hProd.trans hPower
  have hAK : step n X t*count n X ≤ X := by exact_mod_cast hAKR
  have hMul := mul_le_mul_of_nonneg_right hC (Real.rpow_nonneg hXp.le (1-3/(16*(n : ℝ))))
  rw [← Real.rpow_add hXp] at hMul
  have he : 3/(16*(n : ℝ))+(1-3/(16*(n : ℝ)))=1 := by ring
  rw [he,Real.rpow_one] at hMul
  have hTotalR := (mul_le_mul_of_nonneg_left hProd (Nat.cast_nonneg n : (0 : ℝ) ≤ n)).trans hMul
  have hTotal : n*(step n X t*count n X) ≤ X := by exact_mod_cast hTotalR
  exact ⟨ht,hStep.2.2,hStep.1,hStep.2.1,hAK,hTotal⟩
end PaperP1.RoundedLogarithmicParameters
