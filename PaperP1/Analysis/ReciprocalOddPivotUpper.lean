module

public import PaperP1.Analysis.OrdinaryReciprocalPrimeInput
public import PaperP1.Arithmetic.ReciprocalPivotSquareTail
public import PaperP1.Analysis.ReciprocalSquareTail

/-! # Actual reciprocal odd-pivot upper bound from the ordinary prime input

The finite square-part weights have bounded sum. Their number is not
charged as a prefactor. The large square-part tail is estimated internally.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ReciprocalOddPivotUpper

open Finset Filter PaperP1.ReciprocalOddPivots PaperP1.ReciprocalPivotSquareTail
  PaperP1.OrdinaryReciprocalPrimeInput PaperP1.SaddleParameters PaperP1.SaddleScales
  PaperP1.HardSaddleExplicitScale PaperP1.HardSaddleGrowth

theorem finite_small_part_bound (X A : ℕ) (F : ℝ) (hF : 0 ≤ F)
    (hterms : ∀ a ∈ (Icc 1 (Nat.sqrt X)).filter (· ≤ A),
      primeSum (X / a ^ 2) ≤ (X : ℝ) / (a : ℝ) ^ 2 * F) :
    (∑ a ∈ (Icc 1 (Nat.sqrt X)).filter (· ≤ A), primeSum (X / a ^ 2)) ≤ 2 * X * F := by
  let S := (Icc 1 (Nat.sqrt X)).filter (· ≤ A)
  have hsq := PaperP1.ReciprocalSquareTail.finite_bound 1 (by norm_num) S
    (fun a ha ↦ by exact_mod_cast (mem_Icc.mp (mem_filter.mp ha).1).1)
  calc
    _ ≤ ∑ a ∈ S, (X : ℝ) / (a : ℝ) ^ 2 * F := sum_le_sum hterms
    _ = ((X : ℝ) * F) * ∑ a ∈ S, 1 / (a : ℝ) ^ 2 := by
      rw [mul_sum]
      apply sum_congr rfl
      intro a _
      ring
    _ ≤ ((X : ℝ) * F) * 2 := mul_le_mul_of_nonneg_left (by simpa only [div_one] using hsq) (by positivity)
    _ = _ := by ring

theorem uniform_finite_upper (hinput : EIPInput) (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, ∀ X ≥ max X₀ 2,
      pivotSum X ≤ 6 * X * Real.exp (-explicitScale (Real.log X) + ε * saddleNu 1 (Real.log X)) := by
  obtain ⟨XP, hP⟩ := uniform_square_part_upper hinput ε hε
  obtain ⟨HG, hG⟩ := scale_upper_eventually
  have hnatlog : Tendsto (fun X : ℕ ↦ Real.log X) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨XG, hXG⟩ := eventually_atTop.mp
    (hnatlog.eventually (eventually_ge_atTop (max HG (max (saddleThreshold 1) 1))))
  refine ⟨max XP XG, ?_⟩
  intro X hX
  have hlog := hXG X (by omega)
  have hH : 0 < Real.log X := by have := (le_max_right _ _).trans ((le_max_right _ _).trans hlog); linarith
  have hV : 0 < saddleCutoff 1 (Real.log X) := saddleCutoff_pos (by norm_num) (by order)
  have hnu : 0 ≤ saddleNu 1 (Real.log X) := (div_pos hH hV).le
  let V := saddleCutoff 1 (Real.log X)
  let A := ⌊Real.exp (4 * V)⌋₊
  let F := Real.exp (-explicitScale (Real.log X) + ε * saddleNu 1 (Real.log X))
  have hA : 1 ≤ A := by
    apply (Nat.le_floor_iff (Real.exp_nonneg _)).mpr
    simp only [Nat.cast_one]
    exact Real.one_le_exp (by dsimp [V]; positivity)
  have hAfloor : (A : ℝ) ≤ Real.exp (4 * V) := Nat.floor_le (Real.exp_nonneg _)
  have hAhalf : Real.exp (4 * V) ≤ 2 * (A : ℝ) := by
    have hh := Nat.lt_floor_add_one (Real.exp (4 * V))
    have ha : (1 : ℝ) ≤ A := by exact_mod_cast hA
    change Real.exp (4 * V) < (A : ℝ) + 1 at hh
    linarith only [hh, ha]
  have hsmall : (∑ a ∈ (Icc 1 (Nat.sqrt X)).filter (· ≤ A), primeSum (X / a ^ 2)) ≤ 2 * X * F := by
    apply finite_small_part_bound X A F (Real.exp_pos _).le
    intro a ha
    obtain ⟨hI, haA⟩ := mem_filter.mp ha
    obtain ⟨ha1, hasqrt⟩ := mem_Icc.mp hI
    exact hP X (by omega) a (by omega) (Nat.le_sqrt'.mp hasqrt)
      ((by exact_mod_cast haA : (a : ℝ) ≤ A).trans hAfloor)
  have htail : 2 * (X : ℝ) / A ≤ 4 * X * F := by
    have hApos : (0 : ℝ) < A := by exact_mod_cast (show 0 < A by omega)
    have hinv : 1 / (A : ℝ) ≤ 2 * Real.exp (-4 * V) := by
      rw [show (-4 : ℝ) * V = -(4 * V) by ring, Real.exp_neg]
      change 1 / (A : ℝ) ≤ 2 / Real.exp (4 * V)
      exact (div_le_div_iff₀ hApos (Real.exp_pos (4 * V))).mpr (by simpa only [one_mul] using hAhalf)
    have hGbound := hG (Real.log X) (by order)
    have hexp : Real.exp (-4 * V) ≤ F := Real.exp_le_exp.mpr (by
      dsimp [V] at *
      nlinarith only [hGbound, hV, mul_nonneg hε.le hnu])
    calc
      _ = (2 * X) * (1 / (A : ℝ)) := by ring
      _ ≤ (2 * X) * (2 * Real.exp (-4 * V)) := mul_le_mul_of_nonneg_left hinv (by positivity)
      _ ≤ (2 * X) * (2 * F) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hexp (by norm_num)) (by positivity)
      _ = _ := by ring
  have hh := full_square_part_bound X A hA
  dsimp [F] at hsmall htail
  linarith only [hh, hsmall, htail]

end PaperP1.ReciprocalOddPivotUpper
