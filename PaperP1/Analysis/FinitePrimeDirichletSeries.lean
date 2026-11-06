module

public import PaperP1.Analysis.RealEulerSquareMean
public import PaperP1.Analysis.DirichletRamareApproximation
public import Mathlib.NumberTheory.EulerProduct.Basic

/-! # Actual absolutely convergent finite-prime integer Dirichlet series and uniform mean square -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FinitePrimeDirichletSeries
open Finset PaperP1 LogarithmicPhase RealPrimeEulerBound
open scoped Classical

def twistHom (f : ℕ →* ℝ) (t : ℝ) : ℕ →* ℂ where
  toFun n := DirichletRamareApproximation.twist (fun n ↦ (f n : ℂ)) n t
  map_one' := by simp [DirichletRamareApproximation.twist,phase]
  map_mul' m n := DirichletRamareApproximation.twist_mul (fun n ↦ (f n : ℂ))
    (fun a b ↦ by rw [f.map_mul,Complex.ofReal_mul]) t m n

def value (P : Finset ℕ) (f : ℕ →* ℝ) (t : ℝ) : ℂ :=
  ∑' n : Nat.factoredNumbers P, DirichletRamareApproximation.twist (fun n ↦ (f n : ℂ)) n t

theorem summable_and_hasSum (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (f : ℕ →* ℝ) (hf : ∀ p : ℕ, p.Prime → |f p| ≤ 1) (t : ℝ) :
    Summable (fun n : Nat.factoredNumbers P ↦ ‖DirichletRamareApproximation.twist (fun n ↦ (f n : ℂ)) n t‖) ∧
      HasSum (fun n : Nat.factoredNumbers P ↦ DirichletRamareApproximation.twist (fun n ↦ (f n : ℂ)) n t)
        (RealPrimeEulerBound.product P f t) := by
  have hprime : ∀ {p : ℕ}, p.Prime → ‖twistHom f t p‖ < 1 := by
    intro p hp
    have hh := primeTerm_half f p t hp (hf p hp)
    change ‖twistHom f t p‖ ≤ 1/2 at hh
    linarith
  have hh := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric hprime P
  have he : P.filter Nat.Prime=P := filter_eq_self.mpr hP
  rw [he] at hh
  exact hh

theorem value_eq_product (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (f : ℕ →* ℝ) (hf : ∀ p : ℕ, p.Prime → |f p| ≤ 1) (t : ℝ) :
    value P f t=RealPrimeEulerBound.product P f t := (summable_and_hasSum P hP f hf t).2.tsum_eq

theorem normalized_series_bound (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (f : ℕ →* ℝ) (hf : ∀ p : ℕ, p.Prime → |f p| ≤ 1) (t : ℝ) :
    Real.exp (-PrimeAvoidanceSieve.reciprocalMass P)*‖value P f t‖ ≤
      Real.exp ((∑ p ∈ P, 1/(p : ℝ)^2)-RealPretentiousDistance.distance P f t) := by
  rw [value_eq_product P hP f hf t]
  exact normalized_bound P hP f (fun p hp ↦ hf p (hP p hp)) t

theorem normalized_series_square_mean_small (η : ℝ) (hη : 0 < η) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∀ T : ℝ, SlowPrimeBandSieve.upper N ≤ T → ∀ f : ℕ →* ℝ,
        (∀ p : ℕ, p.Prime → |f p| ≤ 1) →
        (∫ t in -T..T, (Real.exp (-PrimeAvoidanceSieve.reciprocalMass (SlowPrimeBandSieve.primes N))*
          ‖value (SlowPrimeBandSieve.primes N) f t‖)^2) ≤ η*T := by
  obtain ⟨N₀,hN₀,hmean⟩ := RealEulerSquareMean.normalized_square_mean_small η hη
  refine ⟨N₀,hN₀,?_⟩
  intro N hN T hT f hf
  have he (t : ℝ) := value_eq_product (SlowPrimeBandSieve.primes N)
    (fun p hp ↦ (mem_filter.mp hp).2) f hf t
  simp_rw [he]
  exact hmean N hN T hT f (fun p hp ↦ hf p (mem_filter.mp hp).2)
end FinitePrimeDirichletSeries
