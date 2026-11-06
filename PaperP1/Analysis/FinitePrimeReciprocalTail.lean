module

public import PaperP1.Analysis.FinitePrimeDirichletSeries

/-! # Actual finite-prime reciprocal tails with a uniform power decay bound -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FinitePrimeReciprocalTail
open Finset MeasureTheory PaperP1
open scoped Classical

def rootWeight : ℕ →* ℝ where
  toFun n := 1/Real.sqrt (n : ℝ)
  map_one' := by simp
  map_mul' m n := by rw [Nat.cast_mul,Real.sqrt_mul (Nat.cast_nonneg m),one_div,one_div,one_div,mul_inv_rev]; ring

def rootEuler (P : Finset ℕ) : ℝ := ∏ p ∈ P, (1-1/Real.sqrt (p : ℝ))⁻¹

def tail (P : Finset ℕ) (X : ℝ) : ℝ :=
  ∑' n : Nat.factoredNumbers P, if X < (n : ℝ) then 1/(n : ℝ) else 0

theorem root_prime_lt_one (p : ℕ) (hp : p.Prime) : ‖rootWeight p‖ < 1 := by
  have hpr : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hs : 1 < Real.sqrt (p : ℝ) := by nlinarith [Real.sq_sqrt (Nat.cast_nonneg p),Real.sqrt_nonneg (p : ℝ)]
  change ‖1/Real.sqrt (p : ℝ)‖ < 1
  rw [Real.norm_eq_abs,abs_of_nonneg (by positivity)]
  exact (div_lt_iff₀ (by linarith : 0 < Real.sqrt (p : ℝ))).mpr (by simpa using hs)

theorem root_series (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    Summable (fun n : Nat.factoredNumbers P ↦ (rootWeight n : ℝ)) ∧
      HasSum (fun n : Nat.factoredNumbers P ↦ (rootWeight n : ℝ)) (rootEuler P) := by
  have hh := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric
    (fun {p} hp ↦ root_prime_lt_one p hp) P
  rw [filter_eq_self.mpr hP] at hh
  refine ⟨?_,hh.2⟩
  apply Summable.of_norm
  exact hh.1

theorem rankin_term (X x : ℝ) (hX : 0 < X) (hXx : X < x) :
    1/x ≤ (1/Real.sqrt X)*(1/Real.sqrt x) := by
  have hx : 0 < x := hX.trans hXx
  have hsX : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX
  have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hmono := Real.sqrt_le_sqrt hXx.le
  have hprod : Real.sqrt X*Real.sqrt x ≤ x := by
    nlinarith [Real.sq_sqrt hx.le]
  calc
    _ ≤ 1/(Real.sqrt X*Real.sqrt x) := div_le_div_of_nonneg_left (by norm_num) (by positivity) hprod
    _ = _ := by ring

theorem tail_bound (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (X : ℝ) (hX : 0 < X) :
    tail P X ≤ (1/Real.sqrt X)*rootEuler P := by
  have hr := root_series P hP
  have hs : Summable (fun n : Nat.factoredNumbers P ↦ (1/Real.sqrt X)*(rootWeight n : ℝ)) := hr.1.mul_left _
  have hnonneg : ∀ n : Nat.factoredNumbers P, 0 ≤ (if X < (n : ℝ) then 1/(n : ℝ) else 0) := by
    intro n
    split_ifs <;> positivity
  have hterm : ∀ n : Nat.factoredNumbers P,
      (if X < (n : ℝ) then 1/(n : ℝ) else 0) ≤ (1/Real.sqrt X)*(rootWeight n : ℝ) := by
    intro n
    split_ifs with hn
    · exact rankin_term X n hX hn
    · change 0 ≤ (1/Real.sqrt X)*(1/Real.sqrt (n : ℝ))
      positivity
  have ht := Summable.of_nonneg_of_le hnonneg hterm hs
  have hm := ht.tsum_le_tsum hterm hs
  rw [tail]
  simpa only [tsum_mul_left,hr.2.tsum_eq] using hm

theorem real_factor_bound (r : ℝ) (hr : 0 ≤ r) (hrhalf : r ≤ 1/2) :
    (1-r)⁻¹ ≤ Real.exp (2*r) := by
  have hz : ‖(r : ℂ)‖ ≤ 1/2 := by simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr] using hrhalf
  have he := FiniteEulerLogBound.point_log_error (r : ℂ) hz
  have hpos : 0 < (1-r)⁻¹ := inv_pos.mpr (by linarith)
  have hn : ‖(1-(r : ℂ))⁻¹‖=(1-r)⁻¹ := by
    rw [← Complex.ofReal_one,← Complex.ofReal_sub,← Complex.ofReal_inv,Complex.norm_real,
      Real.norm_eq_abs,abs_of_pos hpos]
  rw [hn,Complex.ofReal_re,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr] at he
  have hs : r^2 ≤ r := by nlinarith
  have hl : Real.log ((1-r)⁻¹) ≤ 2*r := by linarith [(abs_le.mp he).2]
  have hx := Real.exp_le_exp.mpr hl
  simpa only [Real.exp_log hpos] using hx

theorem root_euler_bound (P : Finset ℕ) (L : ℝ) (hL : 4 ≤ L)
    (hP : ∀ p ∈ P, L ≤ (p : ℝ)) :
    rootEuler P ≤ Real.exp (2*(P.card : ℝ)/Real.sqrt L) := by
  have hLp : 0 < L := by linarith
  have hsL : 2 ≤ Real.sqrt L := by nlinarith [Real.sq_sqrt hLp.le,Real.sqrt_nonneg L]
  have hterm (p : ℕ) (hp : p ∈ P) : 1/Real.sqrt (p : ℝ) ≤ 1/Real.sqrt L :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) (Real.sqrt_le_sqrt (hP p hp))
  have hhalf : 1/Real.sqrt L ≤ 1/2 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) hsL
  calc
    _ ≤ ∏ p ∈ P, Real.exp (2/Real.sqrt (p : ℝ)) := by
      apply prod_le_prod₀
      · intro p hp
        have hh := (hterm p hp).trans hhalf
        exact inv_nonneg.mpr (by linarith)
      · intro p hp
        simpa only [mul_one_div] using real_factor_bound (1/Real.sqrt (p : ℝ)) (by positivity) ((hterm p hp).trans hhalf)
    _ = Real.exp (∑ p ∈ P, 2/Real.sqrt (p : ℝ)) := (Real.exp_sum _ _).symm
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      calc
        _ ≤ ∑ _p ∈ P, 2/Real.sqrt L := sum_le_sum (fun p hp ↦ by
          have hh := mul_le_mul_of_nonneg_left (hterm p hp) (by norm_num : (0 : ℝ) ≤ 2)
          simpa only [mul_one_div] using hh)
        _ = _ := by simp; ring
theorem slow_band_tail_bound_eventually :
    ∀ᶠ N : ℕ in Filter.atTop, tail (SlowPrimeBandSieve.primes N) (N : ℝ) ≤ (N : ℝ)^(-(1/4 : ℝ)) := by
  filter_upwards [SlowPrimeBandSieve.lower_tendsto.eventually (Filter.eventually_ge_atTop 64),
    Filter.eventually_ge_atTop 2] with N hlow hN
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hLpos : 0 < SlowPrimeBandSieve.lower N := by linarith
  have hsL : 8 ≤ Real.sqrt (SlowPrimeBandSieve.lower N) := by
    nlinarith [Real.sq_sqrt hLpos.le,Real.sqrt_nonneg (SlowPrimeBandSieve.lower N)]
  have hcard : ((SlowPrimeBandSieve.primes N).card : ℝ) ≤ Real.log N := by
    have hc : ((SlowPrimeBandSieve.primes N).card : ℝ) ≤ (⌊SlowPrimeBandSieve.upper N⌋₊ : ℝ) := by
      exact_mod_cast SlowPrimeBandSieve.prime_card_bound N
    exact hc.trans (Nat.floor_le hlog)
  have hprime : ∀ p ∈ SlowPrimeBandSieve.primes N, p.Prime := fun p hp ↦ (mem_filter.mp hp).2
  have hcut : ∀ p ∈ SlowPrimeBandSieve.primes N, SlowPrimeBandSieve.lower N ≤ (p : ℝ) := by
    intro p hp
    exact ((Nat.floor_lt hLpos.le).mp (mem_Ioc.mp (mem_filter.mp hp).1).1).le
  have he := root_euler_bound (SlowPrimeBandSieve.primes N) (SlowPrimeBandSieve.lower N) (by linarith) hcut
  have hexp : 2*((SlowPrimeBandSieve.primes N).card : ℝ)/Real.sqrt (SlowPrimeBandSieve.lower N) ≤ Real.log N/4 := by
    calc
      _ ≤ 2*Real.log N/Real.sqrt (SlowPrimeBandSieve.lower N) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcard (by norm_num)) (Real.sqrt_nonneg _)
      _ ≤ 2*Real.log N/8 := div_le_div_of_nonneg_left (by positivity) (by norm_num) hsL
      _ = _ := by ring
  have hroot := he.trans (Real.exp_le_exp.mpr hexp)
  calc
    _ ≤ (1/Real.sqrt (N : ℝ))*rootEuler (SlowPrimeBandSieve.primes N) :=
      tail_bound _ hprime (N : ℝ) hNr
    _ ≤ (1/Real.sqrt (N : ℝ))*Real.exp (Real.log N/4) := mul_le_mul_of_nonneg_left hroot (by positivity)
    _ = _ := by
      rw [Real.sqrt_eq_rpow,Real.rpow_def_of_pos hNr,Real.rpow_def_of_pos hNr,one_div,
        ← Real.exp_neg,← Real.exp_add]
      congr 1
      ring

theorem slow_band_tail_tendsto :
    Filter.Tendsto (fun N : ℕ ↦ tail (SlowPrimeBandSieve.primes N) (N : ℝ)) Filter.atTop (nhds 0) := by
  have hp := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1/4)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hp
  · apply Filter.Eventually.of_forall
    intro N
    unfold tail
    exact tsum_nonneg (fun n ↦ by split_ifs <;> positivity)
  · exact slow_band_tail_bound_eventually
end FinitePrimeReciprocalTail
