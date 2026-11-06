module

public import PaperP1.Analysis.PrimeBandDiscreteMoments
public import PaperP1.Asymptotics.SlowPrimeBandSieve
set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.SlowPrimeDiscrete
open Finset Nat MeasureTheory PaperP1 GaussianExponentialSums BoundedProductFibres
  PrimePolynomialMoments FiniteFibreSquareBudget Filter
open scoped Classical

theorem sampled_high_moment_bound {ι : Type*} (R : Finset ι) (τ : ι → ℝ)
    (T : ℝ) (hT : 0 < T) (htau : ∀ r ∈ R, -T ≤ τ r ∧ τ r ≤ T)
    (hsep : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → 1 ≤ |τ r-τ s|)
    (M : ℕ) (hM : 0 < M) (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (hPM : ∀ p ∈ P, p ≤ M) (c : ℕ → ℂ) (k : ℕ) :
    (∑ r ∈ R, ‖polynomial P c (fun p ↦ -Real.log p) (τ r)‖^(2*k)) ≤
      Real.exp 1*(Real.sqrt Real.pi*(T+1)+2*Real.pi*((M^k : ℕ) : ℝ))*
        (2+((k : ℝ)*Real.log M)^2)*(k.factorial : ℝ)*(∑ p ∈ P, ‖c p‖^2)^k := by
  let S := (tuples k P).image BoundedProductFibres.value
  let b : ℕ → ℂ := aggregate (tuples k P) BoundedProductFibres.value (fun x ↦ ∏ i, c (x i))
  have hS : ∀ n ∈ S, 1 ≤ n ∧ n ≤ M^k := by
    intro n hn
    obtain ⟨x,hx,rfl⟩ := mem_image.mp hn
    constructor
    · calc
        1 = ∏ _i : Fin k, (1 : ℕ) := by simp
        _ ≤ BoundedProductFibres.value x := prod_le_prod (fun i _ ↦ (hP _ (Fintype.mem_piFinset.mp hx i)).one_le)
    · calc
        BoundedProductFibres.value x ≤ ∏ _i : Fin k, M :=
          prod_le_prod (fun i _ ↦ hPM _ (Fintype.mem_piFinset.mp hx i))
        _ = M^k := by simp
  have hpower (t : ℝ) : (polynomial P c (fun p ↦ -Real.log p) t)^k=
      polynomial S b (fun n ↦ -Real.log n) t := by
    rw [power_expansion k P (fun p hp ↦ (hP p hp).pos) c t]
    exact aggregate_polynomial (tuples k P) BoundedProductFibres.value (fun x ↦ ∏ i, c (x i)) t
  have hnorm (t : ℝ) : ‖polynomial P c (fun p ↦ -Real.log p) t‖^(2*k)=
      ‖polynomial S b (fun n ↦ -Real.log n) t‖^2 := by
    rw [Nat.mul_comm 2 k,pow_mul,← norm_pow,hpower t]
  have hh := CenteredLogarithmicSampling.integer_band_sampled_mean_square R τ T hT htau hsep S b 1 (M^k)
    (by decide) (pow_pos hM k) hS
  have hc := coefficient_square_budget k P hP c
  change (∑ n ∈ S, ‖b n‖^2) ≤ (k.factorial : ℝ)*(∑ p ∈ P, ‖c p‖^2)^k at hc
  have hb := hh.trans (mul_le_mul_of_nonneg_left hc (by positivity))
  calc
    _ = ∑ r ∈ R, ‖polynomial S b (fun n ↦ -Real.log n) (τ r)‖^2 := sum_congr rfl (fun r _ ↦ hnorm (τ r))
    _ ≤ _ := by simpa only [Nat.cast_one,Real.log_one,sub_zero,Nat.cast_pow,Real.log_pow,mul_assoc] using hb

def cubicConstant : ℝ := 1056*Real.exp 1*(Real.sqrt Real.pi+Real.pi)

theorem cubicConstant_pos : 0 < cubicConstant := by dsimp only [cubicConstant]; positivity



theorem slow_cubic_moment {ι : Type*} (N : ℕ) (hlower : 2 ≤ SlowPrimeBandSieve.lower N)
    (hupper : 2 ≤ SlowPrimeBandSieve.upper N) (R : Finset ι) (τ : ι → ℝ) (T : ℝ)
    (hT : (SlowPrimeBandSieve.upper N)^3 ≤ T)
    (htau : ∀ r ∈ R, -T ≤ τ r ∧ τ r ≤ T)
    (hsep : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → 1 ≤ |τ r-τ s|) :
    (∑ r ∈ R, ‖DirichletPolynomialMeanValue.value (SlowPrimeBandSieve.primes N) (fun _ ↦ 1) (τ r)‖^6) ≤
      cubicConstant*T/SlowPrimeBandSieve.lower N := by
  let M : ℕ := ⌊SlowPrimeBandSieve.upper N⌋₊
  let P := SlowPrimeBandSieve.primes N
  let c : ℕ → ℂ := fun p ↦ 1/(p : ℂ)
  have hM : 0 < M := by
    have hh : 1 ≤ M := (Nat.le_floor_iff (by linarith : 0 ≤ SlowPrimeBandSieve.upper N)).mpr (by norm_num; linarith)
    omega
  have hMle : (M : ℝ) ≤ SlowPrimeBandSieve.upper N := Nat.floor_le (by linarith)
  have hM3 : ((M^3 : ℕ) : ℝ) ≤ T := by
    rw [Nat.cast_pow]
    exact (pow_le_pow_left₀ (Nat.cast_nonneg M) hMle 3).trans hT
  have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hupper 3
  have hT1 : 1 ≤ T := by norm_num at hpow; linarith
  have hTp : 0 < T := by linarith
  have hlowpos : 0 < SlowPrimeBandSieve.lower N := by linarith
  have hlog : Real.log (M : ℝ) ≤ SlowPrimeBandSieve.lower N :=
    Real.log_le_log (by exact_mod_cast hM) hMle
  have hcoef : (∑ p ∈ P, ‖c p‖^2) ≤ 2/SlowPrimeBandSieve.lower N := by
    calc
      _ = ∑ p ∈ P, 1/(p : ℝ)^2 := by
        apply sum_congr rfl
        intro p hp
        dsimp only [c]
        rw [norm_div,norm_one,Complex.norm_natCast,div_pow,one_pow]
      _ ≤ _ := SlowPrimeBandSieve.square_tail_bound N hlower
  have hm := sampled_high_moment_bound R τ T hTp htau hsep M hM P (fun p hp ↦ (mem_filter.mp hp).2)
    (fun p hp ↦ (mem_Ioc.mp (mem_filter.mp hp).1).2) c 3
  change (∑ r ∈ R, ‖DirichletPolynomialMeanValue.value P (fun _ ↦ 1) (τ r)‖^6) ≤
    Real.exp 1*(Real.sqrt Real.pi*(T+1)+2*Real.pi*((M^3 : ℕ) : ℝ))*
      (2+(3*Real.log (M : ℝ))^2)*6*(∑ p ∈ P, ‖c p‖^2)^3 at hm
  have hfreq : Real.sqrt Real.pi*(T+1)+2*Real.pi*((M^3 : ℕ) : ℝ) ≤ 2*(Real.sqrt Real.pi+Real.pi)*T := by
    have ha := mul_le_mul_of_nonneg_left (show T+1 ≤ 2*T by linarith) (Real.sqrt_nonneg Real.pi)
    have hb := mul_le_mul_of_nonneg_left hM3 (by positivity : 0 ≤ 2*Real.pi)
    nlinarith
  have hwidth : 2+(3*Real.log (M : ℝ))^2 ≤ 11*(SlowPrimeBandSieve.lower N)^2 := by
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ 3*Real.log (M : ℝ))
      (mul_le_mul_of_nonneg_left hlog (by norm_num : (0 : ℝ) ≤ 3)) 2
    nlinarith
  have hF := mul_le_mul_of_nonneg_left hfreq (Real.exp_pos 1).le
  have hFW := mul_le_mul hF hwidth (by positivity : 0 ≤ 2+(3*Real.log (M : ℝ))^2)
    (by positivity : 0 ≤ Real.exp 1*(2*(Real.sqrt Real.pi+Real.pi)*T))
  have hFW6 := mul_le_mul_of_nonneg_right hFW (by norm_num : (0 : ℝ) ≤ 6)
  have hAll := mul_le_mul hFW6 (pow_le_pow_left₀ (sum_nonneg (fun p _ ↦ sq_nonneg ‖c p‖)) hcoef 3)
    (by positivity : 0 ≤ (∑ p ∈ P, ‖c p‖^2)^3)
    (by positivity : 0 ≤ Real.exp 1*(2*(Real.sqrt Real.pi+Real.pi)*T)*(11*(SlowPrimeBandSieve.lower N)^2)*6)
  calc
    _ ≤ Real.exp 1*(2*(Real.sqrt Real.pi+Real.pi)*T)*(11*(SlowPrimeBandSieve.lower N)^2)*6*
        (2/SlowPrimeBandSieve.lower N)^3 := hm.trans hAll
    _ = _ := by dsimp only [cubicConstant]; field_simp [hlowpos.ne']; ring


theorem slow_large_values_card {ι : Type*} (N : ℕ) (hlower : 2 ≤ SlowPrimeBandSieve.lower N)
    (hupper : 2 ≤ SlowPrimeBandSieve.upper N) (hH : 1 ≤ PrimeAvoidanceSieve.reciprocalMass (SlowPrimeBandSieve.primes N))
    (R : Finset ι) (τ : ι → ℝ) (T : ℝ) (hT : (SlowPrimeBandSieve.upper N)^3 ≤ T)
    (htau : ∀ r ∈ R, -T ≤ τ r ∧ τ r ≤ T)
    (hsep : ∀ r ∈ R, ∀ s ∈ R, r ≠ s → 1 ≤ |τ r-τ s|)
    (hbig : ∀ r ∈ R, PrimeAvoidanceSieve.reciprocalMass (SlowPrimeBandSieve.primes N)/2 ≤
      ‖DirichletPolynomialMeanValue.value (SlowPrimeBandSieve.primes N) (fun _ ↦ 1) (τ r)‖) :
    (R.card : ℝ) ≤ 64*cubicConstant*T/SlowPrimeBandSieve.lower N := by
  have hl := sum_le_sum (s := R) (fun r hr ↦ pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1/2)
    (show (1/2 : ℝ) ≤ ‖DirichletPolynomialMeanValue.value (SlowPrimeBandSieve.primes N) (fun _ ↦ 1) (τ r)‖ from
      le_trans (by linarith) (hbig r hr)) 6)
  norm_num only [show (1/2 : ℝ)^6=1/64 by norm_num,sum_const,nsmul_eq_mul] at hl
  have hm := slow_cubic_moment N hlower hupper R τ T hT htau hsep
  calc
    _ = 64*((R.card : ℝ)*(1/64)) := by ring
    _ ≤ 64*(cubicConstant*T/SlowPrimeBandSieve.lower N) := mul_le_mul_of_nonneg_left (hl.trans hm) (by norm_num)
    _ = _ := by ring

theorem slow_large_values_small_uniform {ι : Type*} (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ (R : Finset ι) (τ : ι → ℝ) (T : ℝ),
      (SlowPrimeBandSieve.upper N)^3 ≤ T →
      (∀ r ∈ R, -T ≤ τ r ∧ τ r ≤ T) →
      (∀ r ∈ R, ∀ s ∈ R, r ≠ s → 1 ≤ |τ r-τ s|) →
      (∀ r ∈ R, PrimeAvoidanceSieve.reciprocalMass (SlowPrimeBandSieve.primes N)/2 ≤
        ‖DirichletPolynomialMeanValue.value (SlowPrimeBandSieve.primes N) (fun _ ↦ 1) (τ r)‖) →
      (R.card : ℝ) ≤ ε*T := by
  have hlim : Tendsto (fun N : ℕ ↦ 64*cubicConstant/SlowPrimeBandSieve.lower N) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv,mul_zero,Function.comp_def] using
      (tendsto_inv_atTop_zero.comp SlowPrimeBandSieve.lower_tendsto).const_mul (64*cubicConstant)
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp
    ((eventually_ge_atTop 1).and (SlowPrimeBandSieve.geometry_eventually.and
      ((SlowPrimeBandSieve.upper_tendsto.eventually (eventually_ge_atTop 2)).and
        ((SlowPrimeBandSieve.reciprocal_mass_tendsto.eventually (eventually_ge_atTop 1)).and
          (hlim.eventually (eventually_lt_nhds hε))))))
  refine ⟨max N₀ 1,le_max_right _ _,?_⟩
  intro N hN R τ T hT htau hsep hbig
  obtain ⟨_hN,hlower,hupper,hH,hsmall⟩ := hN₀ N ((le_max_left _ _).trans hN)
  have hTp : 0 ≤ T := (by positivity : 0 ≤ (SlowPrimeBandSieve.upper N)^3).trans hT
  calc
    _ ≤ 64*cubicConstant*T/SlowPrimeBandSieve.lower N := slow_large_values_card N hlower.1 hupper hH R τ T hT htau hsep hbig
    _ = (64*cubicConstant/SlowPrimeBandSieve.lower N)*T := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hsmall.le hTp
end PaperP1.SlowPrimeDiscrete
