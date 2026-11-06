module

public import PaperP1.Analysis.PowerSelbergLevel
public import PaperP1.PNT.LogGrowth
public import PaperP1.Analysis.SmoothPrefixComparison


set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.SmoothRoughPopulation
open Finset Nat Filter PaperP1 SmoothPrefixComparison
open scoped Classical

def exponent (a : ℝ) : ℝ := min a (1/8)

def constant (a : ℝ) : ℝ := 8/exponent a+1

theorem exponent_pos (a : ℝ) (ha : 0 < a) : 0 < exponent a := by
  exact lt_min ha (by norm_num)

theorem roughSet_mono (Y Z K : ℕ) (hZY : Z ≤ Y) : roughSet Y K ⊆ roughSet Z K := by
  intro d hd
  rcases mem_filter.mp hd with ⟨hdK,hcop⟩
  exact mem_filter.mpr ⟨hdK,Nat.Coprime.of_dvd_left (primorial_dvd_primorial hZY) hcop⟩

theorem sieve_bound (Y Z K : ℕ) (hZ : 1 ≤ Z) (hK : 1 ≤ K) (hZY : Z ≤ Y) :
    ((roughSet Y K).card : ℝ) ≤ 2*(K : ℝ)/Real.log ((Z+1 : ℕ) : ℝ)+(Z : ℝ)^4 := by
  have he : NormalizedWindowSets.values 2 (K-1) = Ioc 0 K := by
    rw [NormalizedWindowSets.values_eq_interval (by norm_num)]
    ext n
    simp only [mem_Ico,mem_Ioc]
    omega
  have hh := SelbergLambdaError.actual_primorial_sieve 2 (K-1) Z (by norm_num) hZ
  rw [he,show K-1+1=K by omega] at hh
  have hc : ((roughSet Y K).card : ℝ) ≤ ((roughSet Z K).card : ℝ) := by
    exact_mod_cast card_le_card (roughSet_mono Y Z K hZY)
  exact hc.trans hh

theorem power_bound (a : ℝ) (ha : 0 < a) (N : ℕ) (hN : 2 ≤ N) :
    ((roughSet ⌊(N : ℝ)^a⌋₊ (4*N)).card : ℝ) ≤
      (8/exponent a)*(N : ℝ)/Real.log (N : ℝ)+Real.sqrt (N : ℝ) := by
  have hNR : 1 < (N : ℝ) := by exact_mod_cast (by omega : 1<N)
  have hNP : 0 < (N : ℝ) := by linarith only [hNR]
  have hη : 0 < exponent a := exponent_pos a ha
  let Z := PowerSelbergLevel.level (exponent a) (N : ℝ)
  have hZ : 1 ≤ Z := PowerSelbergLevel.level_pos _ _ hη.le hNR.le
  have hZY : Z ≤ ⌊(N : ℝ)^a⌋₊ :=
    Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le hNR.le (min_le_left _ _))
  have hLog : 0 < Real.log (N : ℝ) := Real.log_pos hNR
  have hLogZ : exponent a*Real.log (N : ℝ) ≤ Real.log ((Z+1 : ℕ) : ℝ) := by
    have hTop : (N : ℝ)^(exponent a) ≤ ((Z+1 : ℕ) : ℝ) := by
      simpa only [Z,PowerSelbergLevel.level,Nat.cast_add,Nat.cast_one] using
        (Nat.lt_floor_add_one ((N : ℝ)^(exponent a))).le
    have hh := Real.log_le_log (Real.rpow_pos_of_pos hNP (exponent a)) hTop
    rw [Real.log_rpow hNP] at hh
    exact hh
  have hFourth : (Z : ℝ)^4 ≤ Real.sqrt (N : ℝ) := by
    calc
      _ ≤ (N : ℝ)^(4*exponent a) := PowerSelbergLevel.level_fourth_bound _ _ hNP
      _ ≤ (N : ℝ)^(1/2 : ℝ) := Real.rpow_le_rpow_of_exponent_le hNR.le (by
        have hh : exponent a ≤ 1/8 := min_le_right _ _
        linarith only [hh])
      _ = _ := (Real.sqrt_eq_rpow _).symm
  have hMain : 2*((4*N : ℕ) : ℝ)/Real.log ((Z+1 : ℕ) : ℝ) ≤
      (8/exponent a)*(N : ℝ)/Real.log (N : ℝ) := by
    calc
      _ ≤ 2*((4*N : ℕ) : ℝ)/(exponent a*Real.log (N : ℝ)) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hLogZ
      _ = _ := by push_cast; field_simp; ring
  exact (sieve_bound _ Z (4*N) hZ (by omega) hZY).trans (add_le_add hMain hFourth)

theorem constant_pos (a : ℝ) (ha : 0 < a) : 0 < constant a := by
  have hη := exponent_pos a ha
  unfold constant
  positivity

theorem eventual_bound (a : ℝ) (ha : 0 < a) : ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀,
    ((roughSet ⌊(N : ℝ)^a⌋₊ (4*N)).card : ℝ) ≤
      constant a*(N : ℝ)/Real.log (N : ℝ) := by
  have hLim := (PNT.tendsto_pow_log_div_pow_atTop (1/2) 1 (by norm_num)).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨N₁,hTail⟩ := eventually_atTop.mp (hLim.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ)<1)))
  refine ⟨max 2 N₁,by omega,?_⟩
  intro N hN
  have hNR : 1 < (N : ℝ) := by exact_mod_cast (by omega : 1<N)
  have hLog : 0 < Real.log (N : ℝ) := Real.log_pos hNR
  have hNP : 0 < (N : ℝ) := by linarith only [hNR]
  have hSqrtP : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr hNP
  have hSmall : Real.log (N : ℝ)/Real.sqrt (N : ℝ) ≤ 1 := by
    simpa only [Function.comp_apply,Real.rpow_one,Real.sqrt_eq_rpow] using (hTail N (by omega)).le
  have hLogSqrt : Real.log (N : ℝ) ≤ Real.sqrt (N : ℝ) :=
    (div_le_iff₀ hSqrtP).mp hSmall |>.trans_eq (one_mul _)
  have hSqrt : Real.sqrt (N : ℝ) ≤ (N : ℝ)/Real.log (N : ℝ) := by
    apply (le_div_iff₀ hLog).mpr
    calc
      _ ≤ Real.sqrt (N : ℝ)*Real.sqrt (N : ℝ) :=
        mul_le_mul_of_nonneg_left hLogSqrt hSqrtP.le
      _ = _ := Real.mul_self_sqrt hNP.le
  calc
    _ ≤ (8/exponent a)*(N : ℝ)/Real.log (N : ℝ)+Real.sqrt (N : ℝ) := power_bound a ha N (by omega)
    _ ≤ (8/exponent a)*(N : ℝ)/Real.log (N : ℝ)+(N : ℝ)/Real.log (N : ℝ) := add_le_add_right hSqrt _
    _ = _ := by unfold constant; ring

end PaperP1.SmoothRoughPopulation
