module

public import PaperP1.Analysis.SquareRootGramBound
public import PaperP1.PNT.LogGrowth

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.SparseGramEnvelope
open Finset Filter PaperP1
open scoped Classical

def separation (N : ℕ) : ℝ := (N : ℝ)^(1/4 : ℝ)
def height (N : ℕ) : ℝ := (N : ℝ)^(5/4 : ℝ)
def cardEnvelope (N : ℕ) : ℝ := (N : ℝ)^(1/100 : ℝ)
def normalizedCap (N : ℕ) : ℝ := cardEnvelope N*SquareRootGramBound.cap N (separation N) (height N)/(N : ℝ)
def squareEnvelope (N : ℕ) : ℝ :=
  128*(Real.sqrt 2*(N : ℝ)^(-71/200 : ℝ)+(N : ℝ)^(-21/200 : ℝ))*(1+Real.log (N : ℝ))

theorem sqrt_rpow (x a : ℝ) (hx : 0 ≤ x) : Real.sqrt (x^a)=x^(a/2) := by
  rw [Real.sqrt_eq_rpow,← Real.rpow_mul hx]
  congr 1
  ring

theorem square_identity (N : ℕ) (hN : 1 ≤ N) : (normalizedCap N)^2=squareEnvelope N := by
  let x := (N : ℝ)
  have hx : 0 < x := by
    dsimp only [x]
    exact_mod_cast (show 0 < N by omega)
  have hlog : 0 ≤ Real.log (N : ℝ) := Real.log_natCast_nonneg N
  have hcard : (cardEnvelope N)^2=x^(1/50 : ℝ) := by
    rw [cardEnvelope,← Real.rpow_two,← Real.rpow_mul hx.le]
    norm_num
  have hheight : Real.sqrt (2*height N)=Real.sqrt 2*x^(5/8 : ℝ) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),height,sqrt_rpow _ _ hx.le]
    norm_num
  have hsep : Real.sqrt (separation N)=x^(1/8 : ℝ) := by
    rw [separation,sqrt_rpow _ _ hx.le]
    norm_num
  have hcap : (SquareRootGramBound.cap N (separation N) (height N))^2=
      128*(x*Real.sqrt (2*height N)+x^2/Real.sqrt (separation N))*(1+Real.log x) := by
    rw [SquareRootGramBound.cap]
    exact Real.sq_sqrt (by positivity)
  have hq1 : x^(1/50 : ℝ)*x*x^(5/8 : ℝ)/x^2=x^(-71/200 : ℝ) := by
    calc
      _ = x^((1/50 : ℝ)+1+(5/8 : ℝ)-2) := by
        rw [Real.rpow_sub hx,Real.rpow_add hx,Real.rpow_add hx,Real.rpow_one,Real.rpow_two]
      _ = _ := by norm_num
  have hq2 : x^(1/50 : ℝ)/x^(1/8 : ℝ)=x^(-21/200 : ℝ) := by
    rw [← Real.rpow_sub hx]
    norm_num
  rw [normalizedCap,div_pow,mul_pow,hcard,hcap,hheight,hsep]
  calc
    _ = 128*(Real.sqrt 2*(x^(1/50 : ℝ)*x*x^(5/8 : ℝ)/x^2)+x^(1/50 : ℝ)/x^(1/8 : ℝ))*(1+Real.log x) := by
      have hp : x^(1/8 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hx _).ne'
      field_simp [hx.ne',hp]
      ring
    _ = _ := by rw [hq1,hq2]; rfl

theorem decaying_log_power (a : ℝ) (ha : 0 < a) :
    Tendsto (fun N : ℕ ↦ (N : ℝ)^(-a)*(1+Real.log (N : ℝ))) atTop (nhds 0) := by
  have hnat := tendsto_natCast_atTop_atTop (R := ℝ)
  have h0 := (PNT.tendsto_pow_log_div_pow_atTop a 0 ha).comp hnat
  have h1 := (PNT.tendsto_pow_log_div_pow_atTop a 1 ha).comp hnat
  have hh : Tendsto (fun N : ℕ ↦ 1/(N : ℝ)^a+Real.log (N : ℝ)/(N : ℝ)^a) atTop (nhds 0) := by
    simpa only [Function.comp_def,Real.rpow_zero,Real.rpow_one,add_zero] using h0.add h1
  apply hh.congr'
  apply Filter.Eventually.of_forall
  intro N
  dsimp only
  rw [Real.rpow_neg (Nat.cast_nonneg N)]
  ring

theorem squareEnvelope_tendsto : Tendsto squareEnvelope atTop (nhds 0) := by
  have h1 := (decaying_log_power (71/200 : ℝ) (by norm_num)).const_mul (128*Real.sqrt 2)
  have h2 := (decaying_log_power (21/200 : ℝ) (by norm_num)).const_mul 128
  have hh := h1.add h2
  have he : (fun N : ℕ ↦ 128*Real.sqrt 2*((N : ℝ)^(-(71/200 : ℝ))*(1+Real.log (N : ℝ)))+
      128*((N : ℝ)^(-(21/200 : ℝ))*(1+Real.log (N : ℝ))))=squareEnvelope := by
    funext N
    unfold squareEnvelope
    ring
  simpa only [he,mul_zero,add_zero] using hh

theorem normalizedCap_nonneg (N : ℕ) : 0 ≤ normalizedCap N := by
  unfold normalizedCap cardEnvelope
  exact div_nonneg (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg N) _)
    (SquareRootGramBound.cap_nonneg N (separation N) (height N))) (Nat.cast_nonneg N)

theorem normalizedCap_tendsto : Tendsto normalizedCap atTop (nhds 0) := by
  have hh : Tendsto (fun N : ℕ ↦ Real.sqrt (squareEnvelope N)) atTop (nhds 0) := by
    simpa only [Function.comp_def,Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp squareEnvelope_tendsto
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [← square_identity N hN,Real.sqrt_sq (normalizedCap_nonneg N)]

theorem uniform_small (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 1 ≤ N₀ ∧ ∀ N ≥ N₀, normalizedCap N ≤ ε := by
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp (normalizedCap_tendsto.eventually (eventually_lt_nhds hε))
  exact ⟨max 1 N₀,le_max_left _ _,fun N hN ↦ (hN₀ N (by omega)).le⟩
end PaperP1.SparseGramEnvelope
