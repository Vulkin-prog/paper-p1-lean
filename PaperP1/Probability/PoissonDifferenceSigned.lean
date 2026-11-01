module

public import PaperP1.Probability.CharlierDifferenceNorm
public import PaperP1.Probability.QuadraticPoisson

/-! # All Poisson differences as actual signed measures -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PoissonDifferenceSigned

open MeasureTheory PaperP1.PoissonSequence PaperP1.FiniteShiftAction PaperP1.IteratedPoissonDifferences
  PaperP1.QuadraticPoisson PaperP1.AtomicSignedLaw

def signedDifference (μ : ℝ) : ℕ → SignedMeasure ℕ
  | 0 => poissonSigned μ
  | r + 1 => differenceMap (signedDifference μ r)

def signedL1 (ν : SignedMeasure ℕ) : ℝ := ∑' k : ℕ, |ν {k}|

def norm (μ : ℝ) (r : ℕ) : ℝ := signedL1 (signedDifference μ r)

def correctionCoefficient (μ : ℝ) : ℝ := norm μ 2 / 4

theorem signedDifference_eq_sequence (μ : ℝ) (hμ : 0 ≤ μ) (r : ℕ) :
    signedDifference μ r = ofSequence (difference r (mass μ)) := by
  induction r with
  | zero => rw [difference_zero]; rfl
  | succ r ih =>
    have hs := summable_difference r (mass μ) (hasSum_mass μ hμ).summable
    rw [signedDifference, ih, difference_succ,
      ofSequence_sub (hasSum_shift hs.hasSum).summable hs, ofSequence_shift hs]
    rfl

theorem signedDifference_singleton (μ : ℝ) (hμ : 0 ≤ μ) (r k : ℕ) :
    signedDifference μ r {k} = difference r (mass μ) k := by
  rw [signedDifference_eq_sequence μ hμ r]
  exact ofSequence_singleton (summable_difference r (mass μ) (hasSum_mass μ hμ).summable) k

theorem norm_eq_l1 (μ : ℝ) (hμ : 0 ≤ μ) (r : ℕ) : norm μ r = l1 (difference r (mass μ)) := by
  unfold norm signedL1 l1
  apply tsum_congr
  intro k
  rw [signedDifference_singleton μ hμ r k]

theorem norm_all_orders (μ : ℝ) (hμ : 0 < μ) (r : ℕ) :
    norm μ r ≤ min ((2 : ℝ) ^ r) (Real.sqrt (r.factorial : ℝ) / μ ^ ((r : ℝ) / 2)) := by
  rw [norm_eq_l1 μ hμ.le r]
  exact PaperP1.CharlierDifferenceNorm.all_order_norm_bound μ hμ r

end PaperP1.PoissonDifferenceSigned
