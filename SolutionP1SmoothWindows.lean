module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Data.Finset.Interval
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import PaperP1.Analysis.SmoothLogarithmicWindowDensity
public import PaperP1.Analysis.ScaledRealOffCentralEnergy
public import PaperP1.Analysis.ActualGaussianMeanComparison

/-! # Ordinary smooth integers in logarithmic intervals

This candidate states a sufficient two-smooth-integer census and the actual
off-central and Gaussian mean-square estimates used in its proof. It is a
selected analytic family from P1, not the entire 167-result formalization and
not the full private-forcing obstruction of companion T19.17. The Challenge
uses only Mathlib; the Solution imports the substantive proofs. Deliberate
statement holes occur only in the Challenge and are not proof evidence.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace PaperP1Registry.SmoothWindows
open Finset MeasureTheory
open scoped Classical

/-- The largest ordinary prime factor, with value one at one (and at zero).
This is ordinary smoothness, rather than a condition on odd valuations. -/
def largestPrimeFactor (n : ℕ) : ℕ := max 1 (n.primeFactors.sup id)

/-- The literal logarithmic interval length used by the sufficient census. -/
def windowLength (N : ℕ) : ℕ := ⌊Real.log (N : ℝ)/(4*Real.log 2)⌋₊

/-- Starts in the dyadic block whose literal integer interval contains at most
one ordinary smooth integer. The interval includes its left endpoint. -/
def exceptional (N Y : ℕ) : Finset ℕ := (Ico N (2*N)).filter fun j ↦
  ((Ico j (j+windowLength N)).filter fun n ↦ largestPrimeFactor n ≤ Y).card ≤ 1

/-- For every fixed positive smoothness exponent, almost every logarithmic
interval contains two ordinary smooth integers. A single cutoff precedes all
dyadic scales; no relative-density asymptotic is asserted. This is the sufficient
census used in P1 companion T19.17, not the full obstruction proposition. -/
theorem almost_all_two_smooth (a : ℝ) (ha : 0 < a) (τ : ℝ) (hτ : 0 < τ) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀,
      ((exceptional N ⌊(N : ℝ)^a⌋₊).card : ℝ) ≤ τ*(N : ℝ) :=
by
  have hBad (N Y : ℕ) : exceptional N Y = PaperP1.SmoothLogarithmicWindowDensity.badWindows N Y := by
    ext j
    simp [exceptional, largestPrimeFactor, windowLength,
      PaperP1.SmoothLogarithmicWindowDensity.badWindows,
      PaperP1.OddPrimePivot.largestPrimeFactor,
      PaperP1.LogarithmicOrdinaryCensusBridge.windowLength]
  simpa only [hBad] using PaperP1.SmoothLogarithmicWindowDensity.uniform_bound a ha τ hτ

/-- The finite dyadic Dirichlet polynomial, with its actual logarithmic phase. -/
def dirichlet (N : ℕ) (f : ℕ → ℝ) (t : ℝ) : ℂ :=
  ∑ n ∈ Ico N (2*N), (f n : ℂ)/(n : ℂ)*
    Complex.exp (Complex.I*((-Real.log (n : ℝ) : ℝ) : ℂ)*(t : ℂ))

/-- The part of the symmetric frequency interval outside a fixed central band. -/
def offCentral (T T₀ : ℝ) : Set ℝ := Set.Ioc (-T) T ∩ {t : ℝ | T₀ ≤ |t|}

/-- Uniform off-central energy for real completely multiplicative functions
bounded by one at every prime. The central cutoff is chosen before every fixed
height multiplier, and the scale cutoff precedes the function and frequency.
No smallness on the central frequency band is claimed. -/
theorem uniform_off_central (ε : ℝ) (hε : 0 < ε) :
    ∃ T₀ : ℝ, 8 ≤ T₀ ∧ ∀ D : ℝ, 0 ≤ D → ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀,
      ∀ f : ℕ →* ℝ, (∀ p : ℕ, p.Prime → |f p| ≤ 1) → ∀ T : ℝ, 1 ≤ T →
      T ≤ D*(N : ℝ)/Real.log (N : ℝ) →
      (∫ t in offCentral T T₀, ‖dirichlet N f t‖^2) ≤ ε :=
by
  simpa only [offCentral, dirichlet, PaperP1.UniformRealOffCentralEnergy.region,
    PaperP1.DirichletPolynomialMeanValue.value,
    PaperP1.GaussianExponentialSums.polynomial, PaperP1.LogarithmicPhase.phase] using
    PaperP1.ScaledRealOffCentralEnergy.common_central_bound ε hε

/-- The normalized heat kernel at every positive width. The totalized value
at nonpositive widths is unused in the comparison theorem. -/
def heat (b v : ℝ) : ℝ := Real.sqrt (Real.pi/b)/(2*Real.pi)*Real.exp (-v^2/(4*b))

/-- The short Gaussian width; D is fixed before the scale is chosen. -/
def shortWidth (D : ℝ) (N : ℕ) : ℝ := (Real.log (N : ℝ)/(D*(N : ℝ)))^2

/-- The actual rounded long comparison interval, of length N/sqrt(log N). -/
def longLength (N : ℕ) : ℕ := ⌈(N : ℝ)/Real.sqrt (Real.log (N : ℝ))⌉₊

/-- The squared relative long interval length. -/
def longWidth (N : ℕ) : ℝ := ((longLength N : ℝ)/(N : ℝ))^2

/-- The literal finite logarithmic Gaussian average, on the two dyadic blocks.
The negative logarithmic centres account for the sign of the Fourier phase. -/
def smoothed (N : ℕ) (f : ℕ → ℝ) (b u : ℝ) : ℝ :=
  ∑ n ∈ Ico N (4*N), f n/(n : ℝ)*heat b (u+Real.log (n : ℝ))

/-- Uniform whole-line mean-square comparison between the short and long
Gaussian averages. This theorem is about Gaussian averages. It does not assert
the stronger general sharp short-interval mean-square theorem. -/
theorem gaussian_mean_comparison (D : ℝ) (hD : 0 < D) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ f : ℕ →* ℝ,
      (∀ p : ℕ, p.Prime → |f p| ≤ 1) →
      (∫ u : ℝ, (smoothed N f (shortWidth D N) u-smoothed N f (longWidth N) u)^2) ≤ ε :=
by
  simpa only [smoothed, heat, shortWidth, longWidth, longLength,
    PaperP1.ActualGaussianMeanComparison.smoothed,
    PaperP1.GaussianSmoothedEnergy.smoothed, PaperP1.GaussianOverlap.heat,
    PaperP1.GaussianLaplaceKernel.prefactor, PaperP1.GaussianLaplaceKernel.gaussian,
    PaperP1.GaussianLogarithmicScales.shortWidth,
    PaperP1.GaussianLogarithmicScales.longWidth, PaperP1.SmoothLongMeanStability.length,
    sub_zero, sub_neg_eq_add] using
    PaperP1.ActualGaussianMeanComparison.uniform_bound D hD ε hε

end PaperP1Registry.SmoothWindows
