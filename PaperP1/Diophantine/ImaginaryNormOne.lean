module

public import PaperP1.Diophantine.ImaginaryQuadraticOrder
public import Mathlib.Data.Int.Interval

/-! # A uniform bound for integral elements of imaginary norm one

The integer trace lies in [-2,2]. Together with the sign of the imaginary
coordinate it determines the element, giving a deliberately loose bound 10.
The coefficient D is arbitrary and positive; no unit classification is used.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ImaginaryNormOne

open ImaginaryQuadraticOrder

variable (D : ℕ) [Fact (0 < D)]

theorem trace_square_le_four (z : OK D)
    (hz : Algebra.norm ℚ (z : QD D) = 1) : traceInteger D z ^ 2 ≤ 4 := by
  rw [norm_eq D] at hz
  have hD : (0 : ℚ) < D := by exact_mod_cast (Fact.out : 0 < D)
  have hnonneg : 0 ≤ (D : ℚ) * (z : QD D).im ^ 2 :=
    mul_nonneg hD.le (sq_nonneg _)
  have htrace : (traceInteger D z : ℚ) ^ 2 ≤ 4 := by
    rw [traceInteger_cast]
    nlinarith
  exact_mod_cast htrace

theorem trace_mem_Icc (z : OK D)
    (hz : Algebra.norm ℚ (z : QD D) = 1) :
    traceInteger D z ∈ Finset.Icc (-2 : ℤ) 2 := by
  have h := trace_square_le_four D z hz
  rw [Finset.mem_Icc]
  constructor <;> nlinarith

def code (z : OK D) : ℤ × Bool :=
  (traceInteger D z, decide (0 ≤ (z : QD D).im))

theorem code_injective_on_norm_one {z w : OK D}
    (hz : Algebra.norm ℚ (z : QD D) = 1)
    (hw : Algebra.norm ℚ (w : QD D) = 1)
    (he : code D z = code D w) : z = w := by
  have ht : traceInteger D z = traceInteger D w := congrArg Prod.fst he
  have hre : (z : QD D).re = (w : QD D).re := by
    have ht' : (traceInteger D z : ℚ) = (traceInteger D w : ℚ) := by rw [ht]
    rw [traceInteger_cast, traceInteger_cast] at ht'
    linarith
  rw [norm_eq D] at hz hw
  have hD : (0 : ℚ) < D := by exact_mod_cast (Fact.out : 0 < D)
  have hsq : (z : QD D).im ^ 2 = (w : QD D).im ^ 2 := by
    apply mul_left_cancel₀ (ne_of_gt hD)
    rw [hre] at hz
    linarith
  have him : (z : QD D).im = (w : QD D).im := by
    by_cases hz0 : 0 ≤ (z : QD D).im
    · by_cases hw0 : 0 ≤ (w : QD D).im
      · exact (sq_eq_sq₀ hz0 hw0).mp hsq
      · simp [code, hz0, hw0] at he
    · by_cases hw0 : 0 ≤ (w : QD D).im
      · simp [code, hz0, hw0] at he
      · have hneg : -(z : QD D).im = -(w : QD D).im :=
          (sq_eq_sq₀ (by linarith : 0 ≤ -(z : QD D).im)
            (by linarith : 0 ≤ -(w : QD D).im)).mp (by simpa using hsq)
        exact neg_injective hneg
  apply NumberField.RingOfIntegers.ext
  exact QuadraticAlgebra.ext hre him

theorem norm_one_card (T : Finset (OK D))
    (hT : ∀ z ∈ T, Algebra.norm ℚ (z : QD D) = 1) : T.card ≤ 10 := by
  classical
  have hcard : T.card ≤
      ((Finset.Icc (-2 : ℤ) 2).product (Finset.univ : Finset Bool)).card := by
    apply Finset.card_le_card_of_injOn (code D)
    · intro z hz
      exact Finset.mem_product.mpr ⟨trace_mem_Icc D z (hT z hz), Finset.mem_univ _⟩
    · intro z hz w hw he
      exact code_injective_on_norm_one D (hT z hz) (hT w hw) he
  norm_num at hcard
  exact hcard

end PaperP1.ImaginaryNormOne
