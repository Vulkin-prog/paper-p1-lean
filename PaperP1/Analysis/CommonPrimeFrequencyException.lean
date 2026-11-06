module

public import PaperP1.Analysis.RealPretentiousDistance
public import PaperP1.Analysis.PrimePolynomialMoments

/-! # Actual common frequency exceptions for all bounded real prime coefficients -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CommonPrimeFrequencyException
open Finset MeasureTheory PaperP1 GaussianExponentialSums DirichletPolynomialMeanValue
  PrimeAvoidanceSieve RealPretentiousDistance
open scoped Classical

def exceptional (P : Finset ℕ) (T : ℝ) : Set ℝ :=
  {t | t ∈ Set.Ioc (-T) T ∧ reciprocalMass P/2 ≤ ‖value P (fun _ ↦ 1) (2*t)‖}

theorem doubled_value_continuous (P : Finset ℕ) : Continuous (fun t : ℝ ↦ value P (fun _ ↦ 1) (2*t)) := by
  exact (polynomial_continuous P (fun p ↦ 1/(p : ℂ)) (fun p ↦ -Real.log p)).comp (continuous_const.mul continuous_id)

theorem exceptional_measurable (P : Finset ℕ) (T : ℝ) : MeasurableSet (exceptional P T) := by
  exact measurableSet_Ioc.inter (measurableSet_le measurable_const (doubled_value_continuous P).norm.measurable)

theorem repulsion_off_exception (P : Finset ℕ) (T t : ℝ) (ht : t ∈ Set.Ioc (-T) T)
    (hnot : t ∉ exceptional P T) (f : ℕ → ℝ) (hf : ∀ p ∈ P, |f p| ≤ 1) :
    reciprocalMass P/8 < distance P f t := by
  by_contra h
  exact hnot ⟨ht,real_close_implies_prime_large P f t hf (not_lt.mp h)⟩

theorem doubled_high_moment (k Q : ℕ) (hQ0 : 0 < Q) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ p ∈ P, p ≤ Q) (T : ℝ) (hT : 0 < T) :
    (∫ t in -T..T, ‖value P (fun _ ↦ 1) (2*t)‖^(2*k)) ≤
      Real.exp 1*(Real.sqrt Real.pi*T+Real.pi*((Q^k : ℕ) : ℝ))*(k.factorial : ℝ)*
        (∑ p ∈ P, 1/(p : ℝ)^2)^k := by
  have hc := intervalIntegral.integral_comp_mul_left
    (fun u : ℝ ↦ ‖value P (fun _ ↦ 1) u‖^(2*k)) (a := -T) (b := T) (c := 2) (by norm_num)
  have hend : 2*(-T)=-(2*T) := by ring
  rw [hend,smul_eq_mul] at hc
  have hm := PrimePolynomialMoments.high_moment_bound k Q hQ0 P hP hQ
    (fun p ↦ 1/(p : ℂ)) (2*T) (by positivity)
  have he : (∑ p ∈ P, ‖1/(p : ℂ)‖^2) = ∑ p ∈ P, 1/(p : ℝ)^2 := by
    apply sum_congr rfl
    intro p hp
    simp only [norm_div,norm_one,Complex.norm_natCast,div_pow,one_pow]
  calc
    _ = (2 : ℝ)⁻¹*(∫ u in -(2*T)..2*T, ‖value P (fun _ ↦ 1) u‖^(2*k)) := hc
    _ ≤ (2 : ℝ)⁻¹*(Real.exp 1*(Real.sqrt Real.pi*(2*T)+2*Real.pi*((Q^k : ℕ) : ℝ))*
        (k.factorial : ℝ)*(∑ p ∈ P, ‖1/(p : ℂ)‖^2)^k) :=
      mul_le_mul_of_nonneg_left hm (by norm_num)
    _ = _ := by rw [he]; ring

theorem exceptional_budget (k Q : ℕ) (hQ0 : 0 < Q) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ p ∈ P, p ≤ Q) (hH : 0 < reciprocalMass P)
    (T : ℝ) (hT : 0 < T) :
    (reciprocalMass P/2)^(2*k)*volume.real (exceptional P T) ≤
      Real.exp 1*(Real.sqrt Real.pi*T+Real.pi*((Q^k : ℕ) : ℝ))*(k.factorial : ℝ)*
        (∑ p ∈ P, 1/(p : ℝ)^2)^k := by
  let μ := volume.restrict (Set.Ioc (-T) T)
  let F : ℝ → ℝ := fun t ↦ ‖value P (fun _ ↦ 1) (2*t)‖^(2*k)
  have hc := doubled_value_continuous P
  have hFc : Continuous F := by dsimp only [F]; fun_prop
  have hint : Integrable F μ := (hFc.intervalIntegrable (-T) T).1
  have hnonneg : 0 ≤ᵐ[μ] F := Filter.Eventually.of_forall (fun _ ↦ pow_nonneg (norm_nonneg _) _)
  have hm := mul_meas_ge_le_integral_of_nonneg hnonneg hint ((reciprocalMass P/2)^(2*k))
  have hlevel : μ.real {t : ℝ | reciprocalMass P/2 ≤ ‖value P (fun _ ↦ 1) (2*t)‖} ≤
      μ.real {t : ℝ | (reciprocalMass P/2)^(2*k) ≤ F t} := by
    apply measureReal_mono
    · intro t ht
      exact pow_le_pow_left₀ (by positivity : 0 ≤ reciprocalMass P/2) ht _
    · dsimp only [μ]
      finiteness
  have hset : volume.real (exceptional P T) =
      μ.real {t : ℝ | reciprocalMass P/2 ≤ ‖value P (fun _ ↦ 1) (2*t)‖} := by
    dsimp only [μ]
    rw [measureReal_restrict_apply (measurableSet_le measurable_const hc.norm.measurable)]
    congr 1
    ext t
    simp only [exceptional,Set.mem_inter_iff,Set.mem_ofPred_eq,and_comm]
  calc
    _ = (reciprocalMass P/2)^(2*k)*μ.real {t : ℝ | reciprocalMass P/2 ≤ ‖value P (fun _ ↦ 1) (2*t)‖} := by rw [hset]
    _ ≤ (reciprocalMass P/2)^(2*k)*μ.real {t : ℝ | (reciprocalMass P/2)^(2*k) ≤ F t} :=
      mul_le_mul_of_nonneg_left hlevel (by positivity)
    _ ≤ ∫ t : ℝ, F t ∂μ := hm
    _ ≤ _ := by
      change (∫ t in Set.Ioc (-T) T, ‖value P (fun _ ↦ 1) (2*t)‖^(2*k)) ≤ _
      rw [← intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
      exact doubled_high_moment k Q hQ0 P hP hQ T hT

theorem exceptional_measure_bound (k Q : ℕ) (hQ0 : 0 < Q) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ p ∈ P, p ≤ Q) (hH : 0 < reciprocalMass P)
    (T : ℝ) (hT : 0 < T) :
    volume.real (exceptional P T) ≤
      (Real.exp 1*(Real.sqrt Real.pi*T+Real.pi*((Q^k : ℕ) : ℝ))*(k.factorial : ℝ)*
        (∑ p ∈ P, 1/(p : ℝ)^2)^k)/(reciprocalMass P/2)^(2*k) := by
  apply (le_div_iff₀ (pow_pos (by positivity : 0 < reciprocalMass P/2) (2*k))).mpr
  simpa only [mul_comm] using exceptional_budget k Q hQ0 P hP hQ hH T hT
theorem normalized_measure_bound (Q : ℕ) (hQ0 : 0 < Q) (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ p ∈ P, p ≤ Q) (hH : 0 < reciprocalMass P)
    (T : ℝ) (hT : 0 < T) (hQT : (Q : ℝ) ≤ T) :
    volume.real (exceptional P T)/T ≤
      4*Real.exp 1*(Real.sqrt Real.pi+Real.pi)*(∑ p ∈ P, 1/(p : ℝ)^2)/(reciprocalMass P)^2 := by
  have hm := exceptional_measure_bound 1 Q hQ0 P hP hQ hH T hT
  simp only [Nat.factorial_one,Nat.cast_one,mul_one,pow_one] at hm
  have hc : Real.exp 1*(Real.sqrt Real.pi*T+Real.pi*(Q : ℝ)) ≤
      Real.exp 1*(Real.sqrt Real.pi+Real.pi)*T := by
    have hh := mul_le_mul_of_nonneg_left hQT Real.pi_pos.le
    have hb := mul_le_mul_of_nonneg_left
      (add_le_add (le_rfl : Real.sqrt Real.pi*T ≤ Real.sqrt Real.pi*T) hh) (Real.exp_pos 1).le
    nlinarith
  have hb := hm.trans (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_right hc (sum_nonneg (fun p hp ↦ by positivity))) (sq_nonneg _))
  have hdiv := div_le_div_of_nonneg_right hb hT.le
  have he : (Real.exp 1*(Real.sqrt Real.pi+Real.pi)*T*(∑ p ∈ P, 1/(p : ℝ)^2)/(reciprocalMass P/2)^2)/T =
      4*Real.exp 1*(Real.sqrt Real.pi+Real.pi)*(∑ p ∈ P, 1/(p : ℝ)^2)/(reciprocalMass P)^2 := by
    field_simp
    ring
  exact hdiv.trans_eq he

theorem slow_band_fraction_bound (N : ℕ) (hgeom : 2 ≤ SlowPrimeBandSieve.lower N)
    (hupper : 2 ≤ SlowPrimeBandSieve.upper N) (hH : 1 ≤ reciprocalMass (SlowPrimeBandSieve.primes N))
    (T : ℝ) (hT : SlowPrimeBandSieve.upper N ≤ T) :
    volume.real (exceptional (SlowPrimeBandSieve.primes N) T)/T ≤
      (8*Real.exp 1*(Real.sqrt Real.pi+Real.pi))/SlowPrimeBandSieve.lower N := by
  let P := SlowPrimeBandSieve.primes N
  have hHp : 0 < reciprocalMass P := by dsimp only [P]; linarith
  have hTp : 0 < T := by linarith
  have hQ0 : 0 < ⌊SlowPrimeBandSieve.upper N⌋₊ := by
    have hh : (1 : ℕ) ≤ ⌊SlowPrimeBandSieve.upper N⌋₊ :=
      (Nat.le_floor_iff (by linarith : 0 ≤ SlowPrimeBandSieve.upper N)).mpr (by norm_num; linarith)
    omega
  have hQT : (⌊SlowPrimeBandSieve.upper N⌋₊ : ℝ) ≤ T :=
    (Nat.floor_le (by linarith : 0 ≤ SlowPrimeBandSieve.upper N)).trans hT
  have hm := normalized_measure_bound ⌊SlowPrimeBandSieve.upper N⌋₊ hQ0 P
    (fun p hp ↦ (mem_filter.mp hp).2) (fun p hp ↦ (mem_Ioc.mp (mem_filter.mp hp).1).2) hHp T hTp hQT
  have hs := SlowPrimeBandSieve.square_tail_bound N hgeom
  have hsq : 1 ≤ (reciprocalMass P)^2 := by dsimp only [P]; nlinarith
  have hC : 0 ≤ 4*Real.exp 1*(Real.sqrt Real.pi+Real.pi) := by positivity
  calc
    _ ≤ 4*Real.exp 1*(Real.sqrt Real.pi+Real.pi)*(∑ p ∈ P, 1/(p : ℝ)^2)/(reciprocalMass P)^2 := hm
    _ ≤ 4*Real.exp 1*(Real.sqrt Real.pi+Real.pi)*(2/SlowPrimeBandSieve.lower N)/(reciprocalMass P)^2 :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hs hC) (sq_nonneg _)
    _ ≤ 4*Real.exp 1*(Real.sqrt Real.pi+Real.pi)*(2/SlowPrimeBandSieve.lower N)/1 :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hsq
    _ = _ := by ring

theorem common_repulsion_uniform (B ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
      ∀ T : ℝ, SlowPrimeBandSieve.upper N ≤ T →
      ∃ E : Set ℝ, MeasurableSet E ∧ E ⊆ Set.Ioc (-T) T ∧ volume.real E ≤ ε*T ∧
        ∀ t ∈ Set.Ioc (-T) T, t ∉ E → ∀ f : ℕ → ℝ,
          (∀ p ∈ SlowPrimeBandSieve.primes N, |f p| ≤ 1) → B ≤ distance (SlowPrimeBandSieve.primes N) f t := by
  have hsmall : Filter.Tendsto (fun N : ℕ ↦ (8*Real.exp 1*(Real.sqrt Real.pi+Real.pi))/SlowPrimeBandSieve.lower N)
      Filter.atTop (nhds 0) := by
    simpa only [div_eq_mul_inv,mul_zero,Function.comp_def] using
      (tendsto_inv_atTop_zero.comp SlowPrimeBandSieve.lower_tendsto).const_mul
        (8*Real.exp 1*(Real.sqrt Real.pi+Real.pi))
  have hevent : ∀ᶠ N : ℕ in Filter.atTop,
      1 ≤ N ∧ 2 ≤ SlowPrimeBandSieve.lower N ∧ 2 ≤ SlowPrimeBandSieve.upper N ∧
        max 1 (8*B) ≤ reciprocalMass (SlowPrimeBandSieve.primes N) ∧
          (8*Real.exp 1*(Real.sqrt Real.pi+Real.pi))/SlowPrimeBandSieve.lower N < ε := by
    filter_upwards [Filter.eventually_ge_atTop 1,SlowPrimeBandSieve.geometry_eventually,
      SlowPrimeBandSieve.upper_tendsto.eventually (Filter.eventually_ge_atTop 2),
      SlowPrimeBandSieve.reciprocal_mass_tendsto.eventually (Filter.eventually_ge_atTop (max 1 (8*B))),
      hsmall.eventually (eventually_lt_nhds hε)] with N hN hg hu hH hs
    exact ⟨hN,hg.1,hu,hH,hs⟩
  obtain ⟨N₀,hN₀⟩ := Filter.eventually_atTop.mp hevent
  refine ⟨max 1 N₀,le_max_left _ _,?_⟩
  intro N hN T hT
  obtain ⟨hNp,hlow,hu,hH,hs⟩ := hN₀ N (by omega)
  have hHone : 1 ≤ reciprocalMass (SlowPrimeBandSieve.primes N) := (le_max_left _ _).trans hH
  have hB : B ≤ reciprocalMass (SlowPrimeBandSieve.primes N)/8 := by
    have hh := (le_max_right 1 (8*B)).trans hH
    linarith
  refine ⟨exceptional (SlowPrimeBandSieve.primes N) T,exceptional_measurable _ _,?_,?_,?_⟩
  · exact fun t ht ↦ ht.1
  · have hm := slow_band_fraction_bound N hlow hu hHone T hT
    exact (div_le_iff₀ (by linarith : 0 < T)).mp (hm.trans hs.le)
  · intro t ht hnot f hf
    exact hB.trans (repulsion_off_exception _ T t ht hnot f hf).le
end CommonPrimeFrequencyException
