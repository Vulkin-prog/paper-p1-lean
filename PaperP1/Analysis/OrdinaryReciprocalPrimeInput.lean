module

public import PaperP1.Analysis.UniformSaddleVariation
public import PaperP1.Analysis.SaddleMonotonicity
public import PaperP1.Arithmetic.SquarePartLogGeometry

/-! # Explicit ordinary reciprocal-prime input and its uniform square-part transport

The only literature input here concerns the actual largest prime factor
P+(n), rather than the odd-valuation pivot. It is the logarithmic
precision of Erdos--Ivic--Pomerance (1986), Theorem 1 and equation (1.3).
It remains a theorem argument, not an axiom or an internally proved input.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OrdinaryReciprocalPrimeInput

open Filter PaperP1.SaddleParameters PaperP1.SaddleScales PaperP1.HardSaddleExplicitScale
  PaperP1.HardSaddleGrowth PaperP1.ReciprocalOddPivots

def EIPInput : Prop := ∀ ε : ℝ, 0 < ε → ∃ X₀ : ℕ, ∀ X ≥ max X₀ 2,
  (X : ℝ) * Real.exp (-explicitScale (Real.log X) - ε * saddleNu 1 (Real.log X)) ≤ primeSum X ∧
  primeSum X ≤ (X : ℝ) * Real.exp (-explicitScale (Real.log X) + ε * saddleNu 1 (Real.log X))

theorem tendsto_left_endpoint (A : ℝ) :
    Tendsto (fun H : ℝ ↦ H - A * saddleCutoff 1 H) atTop atTop := by
  have hs : Tendsto (fun H : ℝ ↦ A * saddleCutoff 1 H / H) atTop (nhds 0) := by
    simpa only [mul_div_assoc, mul_zero] using tendsto_cutoff_div_height.const_mul A
  apply tendsto_atTop.mpr
  intro T
  filter_upwards [eventually_ge_atTop (max 1 (2 * T)),
    hs.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with H hH hh
  have hpos : 0 < H := by have := (le_max_left _ _).trans hH; linarith
  have hm := (div_le_iff₀ hpos).mp hh.le
  have hT := (le_max_right _ _).trans hH
  linarith only [hm, hT]

theorem uniform_square_part_upper (hinput : EIPInput) (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, ∀ X ≥ max X₀ 2, ∀ a : ℕ,
      0 < a → a ^ 2 ≤ X → (a : ℝ) ≤ Real.exp (4 * saddleCutoff 1 (Real.log X)) →
      primeSum (X / a ^ 2) ≤ (X : ℝ) / (a : ℝ) ^ 2 *
        Real.exp (-explicitScale (Real.log X) + ε * saddleNu 1 (Real.log X)) := by
  obtain ⟨XP, hP⟩ := hinput (ε / 2) (by positivity)
  obtain ⟨HG, hG⟩ := PaperP1.UniformSaddleVariation.uniform_left_variation 9 (ε / 2) (by norm_num) (by positivity)
  let T : ℝ := max (saddleThreshold 1) (Real.log ((max XP 2 : ℕ) : ℝ))
  have hnatlog : Tendsto (fun X : ℕ ↦ Real.log X) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hleft := (tendsto_left_endpoint 9).comp hnatlog
  have hv := tendsto_cutoff_atTop.comp hnatlog
  obtain ⟨X₀, h⟩ := eventually_atTop.mp
    ((hnatlog.eventually (eventually_ge_atTop HG)).and
      ((hleft.eventually (eventually_ge_atTop T)).and
        (hv.eventually (eventually_ge_atTop (Real.log 2)))))
  refine ⟨X₀, ?_⟩
  intro X hX a ha hsquare haexp
  obtain ⟨hgeom, hdomain, hV⟩ := h X (by omega)
  obtain ⟨hqlo, hqhi⟩ := PaperP1.SquarePartLogGeometry.log_quotient_range ha hsquare haexp hV
  have hqpos := (PaperP1.SquarePartLogGeometry.quotient_bounds ha hsquare).1
  have hqreal : (0 : ℝ) < ((X / a ^ 2 : ℕ) : ℝ) := by exact_mod_cast hqpos
  have hfloor : max XP 2 ≤ X / a ^ 2 := by
    have hbound : Real.log ((max XP 2 : ℕ) : ℝ) ≤ Real.log ((X / a ^ 2 : ℕ) : ℝ) :=
      ((le_max_right _ _).trans hdomain).trans hqlo
    have hmpos : (0 : ℝ) < ((max XP 2 : ℕ) : ℝ) := by exact_mod_cast (show 0 < max XP 2 by omega)
    exact_mod_cast (Real.log_le_log_iff hmpos hqreal).mp hbound
  have hroot : saddleThreshold 1 ≤ Real.log ((X / a ^ 2 : ℕ) : ℝ) :=
    ((le_max_left _ _).trans hdomain).trans hqlo
  have hnu := PaperP1.SaddleMonotonicity.nu_monotone (by norm_num : (0 : ℝ) < 1) hroot hqhi
  have hvariation := hG (Real.log X) hgeom (Real.log ((X / a ^ 2 : ℕ) : ℝ)) hqlo hqhi
  have hvariation' := (le_abs_self (explicitScale (Real.log X) - explicitScale (Real.log ((X / a ^ 2 : ℕ) : ℝ)))).trans hvariation
  have hnu' := mul_le_mul_of_nonneg_left hnu (by positivity : 0 ≤ ε / 2)
  have hexp : -explicitScale (Real.log ((X / a ^ 2 : ℕ) : ℝ)) +
      (ε / 2) * saddleNu 1 (Real.log ((X / a ^ 2 : ℕ) : ℝ)) ≤
      -explicitScale (Real.log X) + ε * saddleNu 1 (Real.log X) := by
    linarith only [hvariation', hnu']
  calc
    _ ≤ ((X / a ^ 2 : ℕ) : ℝ) * Real.exp (-explicitScale (Real.log ((X / a ^ 2 : ℕ) : ℝ)) +
        (ε / 2) * saddleNu 1 (Real.log ((X / a ^ 2 : ℕ) : ℝ))) := (hP _ hfloor).2
    _ ≤ ((X / a ^ 2 : ℕ) : ℝ) * Real.exp (-explicitScale (Real.log X) + ε * saddleNu 1 (Real.log X)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) hqreal.le
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (PaperP1.SquarePartLogGeometry.quotient_bounds ha hsquare).2.2 (Real.exp_pos _).le

end PaperP1.OrdinaryReciprocalPrimeInput
