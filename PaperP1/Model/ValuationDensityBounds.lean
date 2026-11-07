module

public import PaperP1.Model.ValuationLayerCounts
public import Mathlib.Data.Nat.Log
public import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! # Exact density and effective errors for retained forced starts
The logarithmic depth covers the complete actual even-valuation set.
Its start count lies between (N-1)/(q+1)-3*depth and N/(q+1)+2*depth.
The normalized deterministic count tends to 1/(q+1) for each fixed
prime, with an error envelope tending to zero uniformly over primes
q<=N. Both full actual exponential moments inherit the explicit lower
budget. This is not a claim about the mean count or a new t threshold.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace PaperP1.ValuationDensityBounds

open Finset Filter ValuationLayerCounts PaperP1.Arithmetic

def depth (N q : ℕ) : ℕ := (Nat.clog q N+1)/2

def lowerBudget (N q : ℕ) : ℝ :=
  ((N : ℝ)-1)/((q : ℝ)+1)-3*(depth N q : ℝ)

def uniformError (N : ℕ) : ℝ := (3*(depth N 2 : ℝ)+1)/(N : ℝ)

theorem clog_le_twice_depth (N q : ℕ) : Nat.clog q N≤2*depth N q := by
  unfold depth
  omega

theorem cutoff_power {q : ℕ} (hq : 2≤q) (N : ℕ) : N≤q^(2*depth N q) := by
  exact (Nat.le_pow_clog (by omega : 1<q) N).trans
    (Nat.pow_le_pow_right (by omega : 0<q) (clog_le_twice_depth N q))

theorem parameters_positive {N q u : ℕ} (hu : u∈PrimeRunStarts.parameters N q) : 0<u := by
  exact (Nat.zero_lt_succ _).trans_le ((mem_Ico.mp hu).1)

theorem parameters_lt_size {N q u : ℕ} (hq : 2≤q)
    (hu : u∈PrimeRunStarts.parameters N q) : u<N := by
  obtain ⟨hlo,hhi⟩ := mem_Ico.mp hu
  change N/q+1≤u at hlo
  change u<N/q+1+(N/q-1) at hhi
  have hmul := (Nat.mul_le_mul_right (N/q) hq).trans (Nat.mul_div_le N q)
  omega

theorem factorization_lt_depth {N q u : ℕ} (hq : Nat.Prime q)
    (hu : u∈PrimeRunStarts.parameters N q) : u.factorization q<2*depth N q := by
  have hu0 : u≠0 := (parameters_positive hu).ne'
  by_contra h
  have hdiv : q^(2*depth N q)∣u := (hq.pow_dvd_iff_le_factorization hu0).mpr (by omega)
  have hle := Nat.le_of_dvd (parameters_positive hu) hdiv
  have hlt := parameters_lt_size hq.two_le hu
  have hcut := cutoff_power hq.two_le N
  omega

theorem retained_parameters_eq_layers {N q : ℕ} (hq : Nat.Prime q) :
    ValuationPrimeCylinder.retainedParameters N q=
      (range (depth N q)).biUnion (parameterLayer N q) := by
  ext u
  constructor
  · intro hu
    obtain ⟨hu,hbit⟩ := mem_filter.mp hu
    obtain ⟨j,hj⟩ := (ValuationPrimeCylinder.parity_condition_iff_even q u).mp hbit
    have heq : u.factorization q=2*j := by omega
    have hlt := factorization_lt_depth hq hu
    have hu0 : u≠0 := (parameters_positive hu).ne'
    apply mem_biUnion.mpr
    refine ⟨j,mem_range.mpr (by omega),?_⟩
    apply mem_filter.mpr
    refine ⟨hu,?_,?_⟩
    · exact (hq.pow_dvd_iff_le_factorization hu0).mpr (by omega)
    · intro hdiv
      have hle := (hq.pow_dvd_iff_le_factorization hu0).mp hdiv
      omega
  · intro hu
    obtain ⟨j,_hj,hu⟩ := mem_biUnion.mp hu
    exact parameterLayer_subset hq.pos hu

theorem starts_card_eq_layer_sum {N q : ℕ} (hq : Nat.Prime q) :
    (ValuationPrimeCylinder.starts N q).card=
      ∑ j ∈ range (depth N q),(parameterLayer N q j).card := by
  rw [valuation_starts_card N q hq.pos,retained_parameters_eq_layers hq]
  apply card_biUnion
  intro i _hi j _hj hij
  exact layers_disjoint _ _ _ hij

theorem inverse_power_tail {q : ℕ} (hq : 2≤q) (N : ℕ) :
    (N : ℝ)*(1/(q : ℝ))^(2*depth N q)≤1 := by
  have hcut : (N : ℝ)≤(q : ℝ)^(2*depth N q) := by exact_mod_cast cutoff_power hq N
  have hp : (0 : ℝ)<(q : ℝ)^(2*depth N q) := by positivity
  rw [one_div_pow,← div_eq_mul_one_div]
  exact (div_le_one hp).mpr hcut

theorem budget_le_chosen_depth {q : ℕ} (hq : 2≤q) (N : ℕ) :
    lowerBudget N q≤budget N q (depth N q) := by
  have htail := inverse_power_tail hq N
  have hden : (0 : ℝ)<(q : ℝ)+1 := by positivity
  unfold lowerBudget budget
  apply sub_le_sub_right
  apply (div_le_iff₀ hden).mpr
  have heq : (N : ℝ)/((q : ℝ)+1)*(1-(1/(q : ℝ))^(2*depth N q))*((q : ℝ)+1)=
      (N : ℝ)*(1-(1/(q : ℝ))^(2*depth N q)) := by field_simp
  rw [heq]
  nlinarith

theorem starts_card_lower {N q : ℕ} (hq : 2≤q) (hqN : q≤N) :
    lowerBudget N q≤((ValuationPrimeCylinder.starts N q).card : ℝ) :=
  (budget_le_chosen_depth hq N).trans (finite_geometric_lower hq hqN (depth N q))

theorem card_layer_real_upper (U B q j : ℕ) (hU : 1≤U) (hq : 0<q) :
    ((layer U B q j).card : ℝ)≤(B : ℝ)*coefficient q j+2 := by
  have ha := (card_translated_multiples_real_bounds U B (q^(2*j)) hU (pow_pos hq _)).2
  have hb := (card_translated_multiples_real_bounds U B (q^(2*j+1)) hU (pow_pos hq _)).1
  have hcard := card_le_card (next_power_multiples_subset U B q j)
  rw [card_layer,Nat.cast_sub hcard]
  change (((Ico U (U+B)).filter fun u ↦ q^(2*j)∣u).card : ℝ)-
    (((Ico U (U+B)).filter fun u ↦ q^(2*j+1)∣u).card : ℝ)≤(B : ℝ)*coefficient q j+2
  simp only [Nat.cast_pow] at ha hb
  have heq : (B : ℝ)*coefficient q j=
      (B : ℝ)/(q : ℝ)^(2*j)-(B : ℝ)/(q : ℝ)^(2*j+1) := by
    simp only [coefficient,one_div_pow]
    ring
  rw [heq]
  linarith

theorem parameter_layer_real_upper {N q : ℕ} (hq : 2≤q) (j : ℕ) :
    ((parameterLayer N q j).card : ℝ)≤(N : ℝ)/q*coefficient q j+2 := by
  have hlen : ((N/q-1 : ℕ) : ℝ)≤(N : ℝ)/q := by
    have hsub : ((N/q-1 : ℕ) : ℝ)≤((N/q : ℕ) : ℝ) := by exact_mod_cast Nat.sub_le (N/q) 1
    exact hsub.trans Nat.cast_div_le
  have hc := coefficient_nonneg (by omega : 1≤q) j
  have hcard := card_layer_real_upper (N/q+1) (N/q-1) q j
    (Nat.succ_le_succ (Nat.zero_le _)) (by omega)
  have hmul := mul_le_mul_of_nonneg_right hlen hc
  change ((parameterLayer N q j).card : ℝ)≤((N/q-1 : ℕ) : ℝ)*coefficient q j+2 at hcard
  linarith

theorem starts_card_upper {N q : ℕ} (hq : Nat.Prime q) :
    ((ValuationPrimeCylinder.starts N q).card : ℝ)≤
      (N : ℝ)/((q : ℝ)+1)+2*(depth N q : ℝ) := by
  have hsum := sum_le_sum (fun j (_hj : j∈range (depth N q)) ↦ parameter_layer_real_upper (N:=N) hq.two_le j)
  have heq : (∑ j ∈ range (depth N q),((N : ℝ)/q*coefficient q j+2))=
      (N : ℝ)/q*(∑ j ∈ range (depth N q),coefficient q j)+2*(depth N q : ℝ) := by
    rw [sum_add_distrib]
    simp only [← mul_sum,sum_const,card_range,nsmul_eq_mul]
    ring
  rw [heq,sum_coefficients q (depth N q) hq.pos] at hsum
  rw [starts_card_eq_layer_sum hq,Nat.cast_sum]
  have hqne : (q : ℝ)≠0 := by exact_mod_cast hq.ne_zero
  have hid : (N : ℝ)/q*((q : ℝ)/((q : ℝ)+1)*(1-(1/(q : ℝ))^(2*depth N q)))=
      (N : ℝ)/((q : ℝ)+1)*(1-(1/(q : ℝ))^(2*depth N q)) := by field_simp
  rw [hid] at hsum
  have hp : 0≤(1/(q : ℝ))^(2*depth N q) := by positivity
  have hmain : (0 : ℝ)≤(N : ℝ)/((q : ℝ)+1) := by positivity
  nlinarith

theorem effective_count_bounds {N q : ℕ} (hq : Nat.Prime q) (hqN : q≤N) :
    ((N : ℝ)-1)/((q : ℝ)+1)-3*(depth N q : ℝ)≤
      ((ValuationPrimeCylinder.starts N q).card : ℝ) ∧
    ((ValuationPrimeCylinder.starts N q).card : ℝ)≤
      (N : ℝ)/((q : ℝ)+1)+2*(depth N q : ℝ) :=
  ⟨starts_card_lower hq.two_le hqN,starts_card_upper hq⟩

theorem count_error_bound {N q : ℕ} (hq : Nat.Prime q) (hqN : q≤N) :
    |((ValuationPrimeCylinder.starts N q).card : ℝ)-(N : ℝ)/((q : ℝ)+1)|≤
      3*(depth N q : ℝ)+1/((q : ℝ)+1) := by
  obtain ⟨hlo,hhi⟩ := effective_count_bounds hq hqN
  have hsplit : ((N : ℝ)-1)/((q : ℝ)+1)=(N : ℝ)/((q : ℝ)+1)-1/((q : ℝ)+1) := by ring
  rw [hsplit] at hlo
  have hk : (0 : ℝ)≤depth N q := Nat.cast_nonneg _
  have hd : (0 : ℝ)≤1/((q : ℝ)+1) := by positivity
  apply abs_le.mpr
  constructor <;> linarith

theorem normalized_error_bound {N q : ℕ} (hq : Nat.Prime q) (hqN : q≤N) :
    |((ValuationPrimeCylinder.starts N q).card : ℝ)/(N : ℝ)-1/((q : ℝ)+1)|≤
      (3*(depth N q : ℝ)+1/((q : ℝ)+1))/(N : ℝ) := by
  have hNP : (0 : ℝ)<N := by exact_mod_cast hq.pos.trans_le hqN
  have h := div_le_div_of_nonneg_right (count_error_bound hq hqN) hNP.le
  have habs : |(((ValuationPrimeCylinder.starts N q).card : ℝ)-(N : ℝ)/((q : ℝ)+1))/(N : ℝ)|≤
      (3*(depth N q : ℝ)+1/((q : ℝ)+1))/(N : ℝ) := by
    rw [abs_div,abs_of_pos hNP]
    exact h
  have heq : (((ValuationPrimeCylinder.starts N q).card : ℝ)-(N : ℝ)/((q : ℝ)+1))/(N : ℝ)=
      ((ValuationPrimeCylinder.starts N q).card : ℝ)/(N : ℝ)-1/((q : ℝ)+1) := by
    field_simp
  simpa only [heq] using habs

theorem positive_exponential_lower {N q : ℕ} (hq : Nat.Prime q) (hqN : q≤N)
    (t : ℝ) (ht : 0≤t) :
    Real.exp (t*lowerBudget N q-
      (LocalDefectBound.primeCount (SupportedPrimeCylinder.cutoff N q) : ℝ)*Real.log 2)≤
        PositiveStarts.exponentialMoment (Model.dyadicBlock N) (q-1) t :=
  (Real.exp_le_exp.mpr (sub_le_sub_right
    (mul_le_mul_of_nonneg_left (starts_card_lower hq.two_le hqN) ht) _)).trans
      (ValuationPrimeCylinder.positive_exponential_card_lower hq hqN t ht)

theorem total_exponential_lower {N q : ℕ} (hq : Nat.Prime q) (hqN : q≤N)
    (t : ℝ) (ht : 0≤t) :
    Real.exp (t*lowerBudget N q-
      (LocalDefectBound.primeCount (SupportedPrimeCylinder.cutoff N q) : ℝ)*Real.log 2)≤
        PrimeRunCylinder.totalExponentialMoment N (q-1) t :=
  (positive_exponential_lower hq hqN t ht).trans (PrimeRunCylinder.positive_le_total N (q-1) t ht)

theorem depth_le_clog (N q : ℕ) : depth N q≤Nat.clog q N := by
  unfold depth
  omega

theorem depth_real_upper {N q : ℕ} (hq : 2≤q) (hN : 1≤N) :
    (depth N q : ℝ)≤Real.logb (q : ℝ) N+1 := by
  have hb : (1 : ℝ)<q := by exact_mod_cast (by omega : 1<q)
  have hx : (1 : ℝ)≤N := by exact_mod_cast hN
  have hceil := (Nat.ceil_lt_add_one (Real.logb_nonneg hb hx)).le
  rw [Real.natCeil_logb_natCast q N] at hceil
  exact (show (depth N q : ℝ)≤(Nat.clog q N : ℝ) by exact_mod_cast depth_le_clog N q).trans hceil

theorem depth_div_tendsto_zero {q : ℕ} (hq : 2≤q) :
    Tendsto (fun N : ℕ ↦ (depth N q : ℝ)/(N : ℝ)) atTop (nhds 0) := by
  have hinv : Tendsto (fun N : ℕ ↦ (1 : ℝ)/N) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hlog : Tendsto (fun N : ℕ ↦ Real.logb (q : ℝ) N/(N : ℝ)) atTop (nhds 0) := by
    have h := (Real.tendsto_pow_logb_div_mul_add_atTop (b:=(q : ℝ)) 1 0 1 one_ne_zero).comp
      (tendsto_natCast_atTop_atTop (R:=ℝ))
    simpa only [Function.comp_def,pow_one,one_mul,add_zero] using h
  have hmajor : Tendsto (fun N : ℕ ↦ (Real.logb (q : ℝ) N+1)/(N : ℝ)) atTop (nhds 0) := by
    simpa only [zero_add,← add_div] using hlog.add hinv
  apply squeeze_zero' (Eventually.of_forall (fun N ↦ by positivity)) _ hmajor
  filter_upwards [eventually_ge_atTop 1] with N hN
  exact div_le_div_of_nonneg_right (depth_real_upper hq hN) (Nat.cast_nonneg _)

theorem normalized_error_tendsto_zero {q : ℕ} (hq : Nat.Prime q) :
    Tendsto (fun N : ℕ ↦ ((ValuationPrimeCylinder.starts N q).card : ℝ)/(N : ℝ)-
      1/((q : ℝ)+1)) atTop (nhds 0) := by
  have hinv : Tendsto (fun N : ℕ ↦ (1 : ℝ)/N) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hmajor : Tendsto (fun N : ℕ ↦
      (3*(depth N q : ℝ)+1/((q : ℝ)+1))/(N : ℝ)) atTop (nhds 0) := by
    have h := ((depth_div_tendsto_zero hq.two_le).const_mul 3).add
      (hinv.const_mul (1/((q : ℝ)+1)))
    simpa only [mul_zero,add_zero,← mul_div_assoc,mul_one,← add_div] using h
  apply squeeze_zero_norm' _ hmajor
  filter_upwards [eventually_ge_atTop q] with N hN
  simpa only [Real.norm_eq_abs] using normalized_error_bound hq hN

theorem retained_start_density {q : ℕ} (hq : Nat.Prime q) :
    Tendsto (fun N : ℕ ↦ ((ValuationPrimeCylinder.starts N q).card : ℝ)/(N : ℝ))
      atTop (nhds (1/((q : ℝ)+1))) := by
  have h := (normalized_error_tendsto_zero hq).add_const (1/((q : ℝ)+1))
  simpa only [sub_add_cancel,zero_add] using h

theorem depth_anti_base {q r : ℕ} (hq : 2≤q) (hqr : q≤r) (N : ℕ) :
    depth N r≤depth N q := by
  have hlog : Nat.clog r N≤Nat.clog q N := Nat.clog_anti_left (by omega : 1<q) hqr
  unfold depth
  omega

theorem normalized_error_uniform_bound {N q : ℕ} (hq : Nat.Prime q) (hqN : q≤N) :
    |((ValuationPrimeCylinder.starts N q).card : ℝ)/(N : ℝ)-1/((q : ℝ)+1)|≤
      uniformError N := by
  have hk : (depth N q : ℝ)≤depth N 2 := by
    exact_mod_cast depth_anti_base (by norm_num : 2≤2) hq.two_le N
  have hd : (1 : ℝ)/((q : ℝ)+1)≤1 := by
    apply (div_le_one (by positivity : (0 : ℝ)<(q : ℝ)+1)).mpr
    have hqR : (0 : ℝ)≤q := Nat.cast_nonneg q
    linarith
  apply (normalized_error_bound hq hqN).trans
  unfold uniformError
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  linarith

theorem uniform_error_tendsto_zero : Tendsto uniformError atTop (nhds 0) := by
  change Tendsto (fun N : ℕ ↦ (3*(depth N 2 : ℝ)+1)/(N : ℝ)) atTop (nhds 0)
  have hinv : Tendsto (fun N : ℕ ↦ (1 : ℝ)/N) atTop (nhds 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop (R:=ℝ))
  have h := ((depth_div_tendsto_zero (by norm_num : 2≤2)).const_mul 3).add hinv
  simpa only [mul_zero,zero_add,← mul_div_assoc,← add_div] using h

theorem uniform_density_approximation (ε : ℝ) (hε : 0<ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀≤N → ∀ q : ℕ, Nat.Prime q → q≤N →
      |((ValuationPrimeCylinder.starts N q).card : ℝ)/(N : ℝ)-1/((q : ℝ)+1)|≤ε := by
  have hevent := uniform_error_tendsto_zero.eventually (eventually_lt_nhds hε)
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp hevent
  exact ⟨N₀,fun N hN q hq hqN ↦
    (normalized_error_uniform_bound hq hqN).trans (hN₀ N hN).le⟩

end PaperP1.ValuationDensityBounds
