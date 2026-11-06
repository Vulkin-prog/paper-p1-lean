module

public import PaperP1.Analysis.FiniteEulerLogBound
public import PaperP1.Analysis.CommonPrimeFrequencyException

/-! # Real prime Euler products suppressed by the actual finite pretentious distance -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RealPrimeEulerBound
open Finset PaperP1 LogarithmicPhase PrimeAvoidanceSieve RealPretentiousDistance
open scoped Classical

def primeTerm (f : ℕ → ℝ) (p : ℕ) (t : ℝ) : ℂ := (f p : ℂ)/(p : ℂ)*phase (-Real.log p) t

def product (P : Finset ℕ) (f : ℕ → ℝ) (t : ℝ) : ℂ :=
  FiniteEulerLogBound.product P (fun p ↦ primeTerm f p t)

def normalized (P : Finset ℕ) (f : ℕ → ℝ) (t : ℝ) : ℝ :=
  Real.exp (-reciprocalMass P)*‖product P f t‖

theorem primeTerm_continuous (f : ℕ → ℝ) (p : ℕ) : Continuous (primeTerm f p) := by
  exact continuous_const.mul (phase_continuous (-Real.log p))

theorem primeTerm_norm (f : ℕ → ℝ) (p : ℕ) (t : ℝ) : ‖primeTerm f p t‖=|f p|/(p : ℝ) := by
  rw [primeTerm,norm_mul,phase_norm,mul_one,norm_div,Complex.norm_real,Real.norm_eq_abs,Complex.norm_natCast]

theorem primeTerm_half (f : ℕ → ℝ) (p : ℕ) (t : ℝ) (hp : p.Prime) (hf : |f p| ≤ 1) :
    ‖primeTerm f p t‖ ≤ 1/2 := by
  rw [primeTerm_norm]
  exact (div_le_div_of_nonneg_right hf (Nat.cast_nonneg p : (0 : ℝ) ≤ p)).trans
    (div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by exact_mod_cast hp.two_le))

theorem product_continuous (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (f : ℕ → ℝ)
    (hf : ∀ p ∈ P, |f p| ≤ 1) : Continuous (product P f) := by
  unfold product FiniteEulerLogBound.product
  apply continuous_finsetProd
  intro p hp
  exact (continuous_const.sub (primeTerm_continuous f p)).inv₀
    (fun t ↦ FiniteEulerLogBound.factor_ne (primeTerm f p t) (primeTerm_half f p t (hP p hp) (hf p hp)))

theorem normalized_continuous (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (f : ℕ → ℝ)
    (hf : ∀ p ∈ P, |f p| ≤ 1) : Continuous (normalized P f) := by
  exact continuous_const.mul (product_continuous P hP f hf).norm

theorem primeTerm_square (f : ℕ → ℝ) (p : ℕ) (t : ℝ) (hf : |f p| ≤ 1) :
    ‖primeTerm f p t‖^2 ≤ 1/(p : ℝ)^2 := by
  rw [primeTerm_norm,div_pow]
  have hh : |f p|^2 ≤ 1 := by simpa only [one_pow] using pow_le_pow_left₀ (abs_nonneg _) hf 2
  exact div_le_div_of_nonneg_right hh (sq_nonneg _)

theorem primeTerm_real_sum (P : Finset ℕ) (f : ℕ → ℝ) (t : ℝ) :
    (∑ p ∈ P, (primeTerm f p t).re)=reciprocalMass P-distance P f t := by
  have hd := distance_eq_real_dirichlet P f t
  have he : (∑ p ∈ P, (primeTerm f p t).re)=
      (DirichletPolynomialMeanValue.value P (fun p ↦ (f p : ℂ)) t).re := by
    rw [DirichletPolynomialMeanValue.value,GaussianExponentialSums.polynomial,Complex.re_sum]
    rfl
  rw [he]
  linarith

theorem log_product_error (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (f : ℕ → ℝ)
    (hf : ∀ p ∈ P, |f p| ≤ 1) (t : ℝ) :
    |Real.log ‖product P f t‖-(reciprocalMass P-distance P f t)| ≤ ∑ p ∈ P, 1/(p : ℝ)^2 := by
  have hh := FiniteEulerLogBound.log_product_error P (fun p ↦ primeTerm f p t)
    (fun p hp ↦ primeTerm_half f p t (hP p hp) (hf p hp))
  rw [primeTerm_real_sum] at hh
  exact hh.trans (sum_le_sum (fun p hp ↦ primeTerm_square f p t (hf p hp)))

theorem norm_product_bound (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (f : ℕ → ℝ)
    (hf : ∀ p ∈ P, |f p| ≤ 1) (t : ℝ) :
    ‖product P f t‖ ≤ Real.exp (reciprocalMass P-distance P f t+(∑ p ∈ P, 1/(p : ℝ)^2)) := by
  have he := FiniteEulerLogBound.norm_product_bound P (fun p ↦ primeTerm f p t)
    (fun p hp ↦ primeTerm_half f p t (hP p hp) (hf p hp))
  rw [primeTerm_real_sum] at he
  exact he.trans (Real.exp_le_exp.mpr (add_le_add le_rfl (sum_le_sum (fun p hp ↦ primeTerm_square f p t (hf p hp)))))

theorem normalized_bound (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (f : ℕ → ℝ)
    (hf : ∀ p ∈ P, |f p| ≤ 1) (t : ℝ) :
    normalized P f t ≤ Real.exp ((∑ p ∈ P, 1/(p : ℝ)^2)-distance P f t) := by
  have hh := mul_le_mul_of_nonneg_left (norm_product_bound P hP f hf t) (Real.exp_pos (-reciprocalMass P)).le
  unfold normalized
  calc
    _ ≤ Real.exp (-reciprocalMass P)*Real.exp (reciprocalMass P-distance P f t+(∑ p ∈ P, 1/(p : ℝ)^2)) := hh
    _ = _ := by rw [← Real.exp_add]; congr 1; ring
theorem normalized_nonneg (P : Finset ℕ) (f : ℕ → ℝ) (t : ℝ) : 0 ≤ normalized P f t := by
  unfold normalized
  positivity

theorem normalized_global_bound (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (f : ℕ → ℝ)
    (hf : ∀ p ∈ P, |f p| ≤ 1) (t : ℝ) :
    normalized P f t ≤ Real.exp (∑ p ∈ P, 1/(p : ℝ)^2) := by
  exact (normalized_bound P hP f hf t).trans (Real.exp_le_exp.mpr
    (sub_le_self _ (distance_nonneg P f t hf)))

theorem slow_band_uniform_off_exception (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∀ T : ℝ, SlowPrimeBandSieve.upper N ≤ T →
      ∃ E : Set ℝ, MeasurableSet E ∧ E ⊆ Set.Ioc (-T) T ∧ MeasureTheory.volume.real E ≤ ε*T ∧
        ∀ t ∈ Set.Ioc (-T) T, t ∉ E → ∀ f : ℕ → ℝ,
          (∀ p ∈ SlowPrimeBandSieve.primes N, |f p| ≤ 1) →
            normalized (SlowPrimeBandSieve.primes N) f t ≤ δ := by
  obtain ⟨N₁,hN₁,hexc⟩ := CommonPrimeFrequencyException.common_repulsion_uniform (1-Real.log δ) ε hε
  obtain ⟨N₂,hN₂⟩ := Filter.eventually_atTop.mp SlowPrimeBandSieve.geometry_eventually
  refine ⟨max N₁ N₂,hN₁.trans (le_max_left _ _),?_⟩
  intro N hN T hT
  obtain ⟨E,hE,hsub,hmeas,hrep⟩ := hexc N (by omega) T hT
  refine ⟨E,hE,hsub,hmeas,?_⟩
  intro t ht hnot f hf
  have hD := hrep t ht hnot f hf
  have hgeom := hN₂ N (by omega)
  have hsum : (∑ p ∈ SlowPrimeBandSieve.primes N, 1/(p : ℝ)^2) ≤ 1 :=
    (SlowPrimeBandSieve.square_tail_bound N hgeom.1).trans
      ((div_le_one (by linarith : 0 < SlowPrimeBandSieve.lower N)).mpr hgeom.1)
  have hn := normalized_bound (SlowPrimeBandSieve.primes N) (fun p hp ↦ (mem_filter.mp hp).2) f hf t
  have hb : (∑ p ∈ SlowPrimeBandSieve.primes N, 1/(p : ℝ)^2)-distance (SlowPrimeBandSieve.primes N) f t ≤ Real.log δ := by
    linarith
  exact hn.trans ((Real.exp_le_exp.mpr hb).trans_eq (Real.exp_log hδ))
end RealPrimeEulerBound
