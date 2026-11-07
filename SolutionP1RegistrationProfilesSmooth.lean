module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Order.Floor.Semiring
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Finset.Interval
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import PaperP1.Analysis.ActualGaussianMeanComparison
public import PaperP1.Analysis.RevisedCompanionStatements
public import PaperP1.Analysis.ScaledRealOffCentralEnergy
public import PaperP1.Analysis.SmoothLogarithmicWindowDensity
public import PaperP1.Asymptotics.AsymmetricAlignmentScopeObstruction

/-! # Arithmetic profiles and smooth logarithmic windows

Consolidated components retain their literal models, complete hypotheses and
original proof bodies, relocated into distinct model namespaces. The declaration
map records every original statement and source hash. No mathematical change.
-/

set_option autoImplicit false
@[expose] public noncomputable section

section ComponentAsymmetricProfiles

/-! # Asymmetric parity-space profiles with their necessary alignment radius

All parity vectors, old value spaces, even selections and loss weights below
are stated directly using Mathlib. The matched Solution supplies the actual
corrected 31/24 profile and the checked radius-one obstruction. The Challenge
has only the three selected statement holes; these are not proof evidence.
-/

namespace PaperP1Registry.RegistrationModels.ProfilesSmooth.AsymmetricProfiles
open Finset
open scoped Classical
local instance primeTwo : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

/-- The field of parity coordinates. -/
abbrev F₂ := ZMod 2

/-- Prime-factorization exponents modulo two, indexed by all natural numbers. -/
def parity (n : ℕ) : ℕ →₀ F₂ :=
  n.factorization.mapRange (fun e : ℕ ↦ (e : F₂)) (by simp)

/-- Forget every prime coordinate at most the cutoff H. -/
def largeParity (H n : ℕ) : ℕ →₀ F₂ := (parity n).filter (fun p ↦ H < p)

/-- Raw old value information; no parity restriction is imposed on old selections. -/
def oldSpace (H : ℕ) (U : Finset ℕ) : Submodule F₂ (ℕ →₀ F₂) :=
  Submodule.span F₂ ((fun n ↦ largeParity H n) '' (U : Set ℕ))

/-- The full start window has boundary vertex z-1 and vertices z,...,z+L-1. -/
def vertexLabel (z L : ℕ) (u : Fin (L+1)) : ℕ :=
  if u.val=0 then z-1 else z+(u.val-1)

/-- Large-prime parity columns of the actual new complete window. -/
def newData (H z L : ℕ) (u : Fin (L+1)) : ℕ →₀ F₂ :=
  largeParity H (vertexLabel z L u)

/-- Sum of a finite coefficient selection. Its kernel is the even-selection space. -/
def sumMap (L : ℕ) : (Fin (L+1) → F₂) →ₗ[F₂] F₂ :=
  Fintype.linearCombination F₂ (fun _ ↦ 1)

/-- The map taking an even selection to its large-prime parity vector. -/
def evenMap (H z L : ℕ) : LinearMap.ker (sumMap L) →ₗ[F₂] (ℕ →₀ F₂) :=
  (Fintype.linearCombination F₂ (newData H z L)).comp (LinearMap.ker (sumMap L)).subtype

/-- The dimension of even new selections whose parity belongs to the old value space. -/
def loss (H : ℕ) (U : Finset ℕ) (z L : ℕ) : ℕ :=
  Module.finrank F₂ (Submodule.comap (evenMap H z L) (oldSpace H U))

/-- Alignment radius D follows the radius D(L+1) of the old enclosing interval. -/
def Aligned (D X z L : ℕ) : Prop :=
  ∃ r s : ℕ, 0 < r ∧ 0 < s ∧ r.Coprime s ∧ r ≤ (L+1)^3 ∧ s ≤ (L+1)^3 ∧
    |(r : ℤ)*z-(s : ℤ)*X| ≤ ((r+s : ℕ) : ℤ)*((D*(L+1) : ℕ) : ℤ)

/-- The fixed expanded domain for old centres. Q=1 is the original dyadic block. -/
def oldBlock (N Q : ℕ) : Finset ℕ := Ico N (N+Q*N)

/-- All nonaligned old/new centre pairs, with new centre in [N,2N). -/
def nonalignedPairs (N Q L D : ℕ) : Finset (ℕ × ℕ) :=
  (oldBlock N Q ×ˢ Ico N (2*N)).filter fun p ↦ ¬Aligned D p.1 p.2 L

/-- The full exponential loss weight, rather than an indicator of positive loss. -/
def weight (H L : ℕ) (old : ℕ → Finset ℕ) (p : ℕ × ℕ) : ℝ :=
  (2 : ℝ)^loss H (old p.1) p.2 L-1

/-- Weighted asymmetric profile for arbitrary old sets in their enclosing intervals. -/
def profile (N Q L H D : ℕ) (old : ℕ → Finset ℕ) : ℝ :=
  ∑ p ∈ nonalignedPairs N Q L D, weight H L old p

/-- Corrected companion T1.10 with expanded old-centre domain, matching
alignment radius, explicit cutoff interval and the full weight 2^loss-1.
One scale threshold precedes all lengths, cutoffs and choices of old sets. -/
theorem _root_.PaperP1Registry.Registration.ProfilesSmooth.asymmetric_profiles_expanded_profile (Q : ℕ) (hQ : 1 ≤ Q) (C ε : ℝ) (D Dcut : ℕ)
    (hD : 1 ≤ D) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 4 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L H : ℕ,
      |(L : ℝ)-Real.log (N : ℝ)/Real.log 2| ≤ C →
      (2*D+1)*(L+1) ≤ H → H ≤ Dcut*(L+1) →
      ∀ old : ℕ → Finset ℕ,
      (∀ x ∈ oldBlock N Q, ∀ n ∈ old x,
        |(n : ℤ)-x| ≤ ((D*(L+1) : ℕ) : ℤ)) →
      profile N Q L H D old ≤ (N : ℝ)^(31/24+ε) :=
by
  have hLoss (H : ℕ) (U : Finset ℕ) (z L : ℕ) :
      loss H U z L = PaperP1.AsymmetricEvenLoss.loss H U z L := by rfl
  have hPairs (N Q L D : ℕ) : nonalignedPairs N Q L D =
      PaperP1.ExpandedAsymmetricCoarseProfile.nonalignedPairs N Q L D := by
    ext p
    simp [nonalignedPairs,oldBlock,Aligned,
      PaperP1.ExpandedAsymmetricCoarseProfile.nonalignedPairs,
      PaperP1.ExpandedAsymmetricSupportEnvelope.block,
      PaperP1.Model.dyadicBlock,PaperP1.CompressedTargetAlignment.Aligned]
  simpa only [profile,weight,hPairs,hLoss,
    PaperP1.ExpandedAsymmetricCoarseProfile.profile,
    PaperP1.AsymmetricCoarseProfile.weight,oldBlock,
    PaperP1.ExpandedAsymmetricSupportEnvelope.block] using
    PaperP1.RevisedCompanionStatements.companion_T1_10 Q hQ C ε D Dcut hD hε

/-- Adjoining prime coordinates at most H to the old data does not change loss. -/
theorem _root_.PaperP1Registry.Registration.ProfilesSmooth.asymmetric_profiles_small_prime_invariance (H z L : ℕ) (U P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime ∧ p ≤ H) :
    loss H (U ∪ P) z L = loss H U z L :=
by
  have hLoss (H : ℕ) (U : Finset ℕ) (z L : ℕ) :
      loss H U z L = PaperP1.AsymmetricEvenLoss.loss H U z L := by rfl
  simpa only [hLoss] using
    PaperP1.RevisedCompanionStatements.small_prime_bits_unchanged H z L U P hP

/-- The original radius-one profile with the admissible old radius 3(L+1). -/
def radiusOneProfile (N L H : ℕ) : ℝ :=
  profile N 1 L H 1 (fun X ↦ Icc X (X+3*(L+1)))

/-- Radius one cannot give the printed exponent for arbitrary old radius.
The old sets here have radius 3(L+1), while the exclusion radius is one.
This does not contradict the matching-radius theorem above. -/
theorem _root_.PaperP1Registry.Registration.ProfilesSmooth.asymmetric_profiles_radius_one_obstruction (D : ℕ) (hD : 1 ≤ D) :
    ¬∃ A : ℝ, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ)-Real.log (N : ℝ)/Real.log 2| ≤ 3 →
      radiusOneProfile N L (D*(L+1)) ≤ A*(N : ℝ)^((31/24 : ℝ)+1/48) :=
by
  have hLoss (H : ℕ) (U : Finset ℕ) (z L : ℕ) :
      loss H U z L = PaperP1.AsymmetricEvenLoss.loss H U z L := by rfl
  have hBad (N L H : ℕ) : radiusOneProfile N L H =
      PaperP1.AsymmetricAlignmentScopeObstruction.profile N L H := by
    simp [radiusOneProfile,profile,weight,nonalignedPairs,oldBlock,Aligned,hLoss,
      PaperP1.AsymmetricAlignmentScopeObstruction.profile,
      PaperP1.Model.dyadicBlock,PaperP1.CompressedTargetAlignment.Aligned,Nat.two_mul]
  simpa only [hBad] using
    PaperP1.AsymmetricAlignmentScopeObstruction.no_uniform_radius_one_bound D hD

end PaperP1Registry.RegistrationModels.ProfilesSmooth.AsymmetricProfiles

end ComponentAsymmetricProfiles

section ComponentSmoothWindows

/-! # Ordinary smooth integers in logarithmic intervals

This candidate states a sufficient two-smooth-integer census and the actual
off-central and Gaussian mean-square estimates used in its proof. It is a
selected analytic family from P1, not the entire 167-result formalization and
not the full private-forcing obstruction of companion T19.17. The Challenge
uses only Mathlib; the Solution imports the substantive proofs. Deliberate
statement holes occur only in the Challenge and are not proof evidence.
-/

namespace PaperP1Registry.RegistrationModels.ProfilesSmooth.SmoothWindows
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
theorem _root_.PaperP1Registry.Registration.ProfilesSmooth.smooth_windows_almost_all_two_smooth (a : ℝ) (ha : 0 < a) (τ : ℝ) (hτ : 0 < τ) :
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
theorem _root_.PaperP1Registry.Registration.ProfilesSmooth.smooth_windows_uniform_off_central (ε : ℝ) (hε : 0 < ε) :
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
theorem _root_.PaperP1Registry.Registration.ProfilesSmooth.smooth_windows_gaussian_mean_comparison (D : ℝ) (hD : 0 < D) (ε : ℝ) (hε : 0 < ε) :
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

end PaperP1Registry.RegistrationModels.ProfilesSmooth.SmoothWindows

end ComponentSmoothWindows
