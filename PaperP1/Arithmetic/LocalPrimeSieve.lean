module

public import PaperP1.Arithmetic.SelbergLambdaError
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # An actual uniform local prime sieve and logarithmic prime weights -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LocalPrimeSieve
open Finset Nat PaperP1
open scoped Classical

theorem prime_coprime_primorial (p Z : ℕ) (hp : Nat.Prime p) (hZ : Z < p) :
    (primorial Z).Coprime p := by
  apply Nat.Coprime.symm
  apply hp.coprime_iff_not_dvd.mpr
  intro hd
  exact (not_le_of_gt hZ) (hp.dvd_primorial_iff.mp hd)

theorem window_prime_bound (x L Z : ℕ) (hx : 2 ≤ x) (hZ : 1 ≤ Z) :
    (((NormalizedWindowSets.values x L).filter Nat.Prime).card : ℝ) ≤
      (Z : ℝ)+2*((L+1 : ℕ) : ℝ)/Real.log ((Z+1 : ℕ) : ℝ)+(Z : ℝ)^4 := by
  have hsub : (NormalizedWindowSets.values x L).filter Nat.Prime ⊆
      Icc 1 Z ∪ (NormalizedWindowSets.values x L).filter (fun n ↦ (primorial Z).Coprime n) := by
    intro p hp
    have hprime := (mem_filter.mp hp).2
    by_cases hpZ : p ≤ Z
    · exact mem_union_left _ (mem_Icc.mpr ⟨hprime.pos,hpZ⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨(mem_filter.mp hp).1,
        prime_coprime_primorial p Z hprime (lt_of_not_ge hpZ)⟩)
  have hc := (card_le_card hsub).trans (card_union_le _ _)
  have hcr : (((NormalizedWindowSets.values x L).filter Nat.Prime).card : ℝ) ≤
      (Z : ℝ)+(((NormalizedWindowSets.values x L).filter (fun n ↦ (primorial Z).Coprime n)).card : ℝ) := by
    exact_mod_cast (by simpa only [Nat.card_Icc,Nat.add_sub_cancel] using hc)
  have hs := SelbergLambdaError.actual_primorial_sieve x L Z hx hZ
  linarith

theorem real_level_optimization (W : ℝ) (hW : 1 < W) :
    (⌊W^(1/8 : ℝ)⌋₊ : ℝ)+2*W/Real.log ((⌊W^(1/8 : ℝ)⌋₊+1 : ℕ) : ℝ)+
      (⌊W^(1/8 : ℝ)⌋₊ : ℝ)^4 ≤ 20*W/Real.log W := by
  let Z := ⌊W^(1/8 : ℝ)⌋₊
  have hW0 : 0 < W := by linarith
  have hW1 : 1 ≤ W := hW.le
  have hrootpos : 0 < W^(1/8 : ℝ) := Real.rpow_pos_of_pos hW0 _
  have hZle : (Z : ℝ) ≤ W^(1/8 : ℝ) := Nat.floor_le hrootpos.le
  have hZplus : W^(1/8 : ℝ) < ((Z+1 : ℕ) : ℝ) := by
    simpa only [Nat.cast_add,Nat.cast_one] using (Nat.lt_floor_add_one (W^(1/8 : ℝ)))
  have hlog : 0 < Real.log W := Real.log_pos hW
  have hZlog : (1/8 : ℝ)*Real.log W ≤ Real.log ((Z+1 : ℕ) : ℝ) := by
    rw [← Real.log_rpow hW0]
    exact Real.log_le_log hrootpos hZplus.le
  have hlogZpos : 0 < Real.log ((Z+1 : ℕ) : ℝ) := lt_of_lt_of_le (by positivity) hZlog
  have hmain : 2*W/Real.log ((Z+1 : ℕ) : ℝ) ≤ 16*W/Real.log W := by
    calc
      _ ≤ 2*W/((1/8 : ℝ)*Real.log W) := div_le_div_of_nonneg_left (by positivity) (by positivity) hZlog
      _ = _ := by ring
  have hZhalf : (Z : ℝ) ≤ W^(1/2 : ℝ) :=
    hZle.trans (Real.rpow_le_rpow_of_exponent_le hW1 (by norm_num))
  have hZfour : (Z : ℝ)^4 ≤ W^(1/2 : ℝ) := by
    calc
      _ ≤ (W^(1/8 : ℝ))^4 := pow_le_pow_left₀ (Nat.cast_nonneg Z) hZle _
      _ = _ := by rw [← Real.rpow_mul_natCast hW0.le]; norm_num
  have hhalfpos : 0 < W^(1/2 : ℝ) := Real.rpow_pos_of_pos hW0 _
  have hhalfsq : (W^(1/2 : ℝ))^2=W := by
    rw [← Real.rpow_mul_natCast hW0.le]; norm_num
  have hloghalf := Real.log_le_sub_one_of_pos hhalfpos
  rw [Real.log_rpow hW0] at hloghalf
  have hlogsmall : Real.log W ≤ 2*W^(1/2 : ℝ) := by linarith
  have herror : 2*W^(1/2 : ℝ) ≤ 4*W/Real.log W := by
    apply (le_div_iff₀ hlog).mpr
    nlinarith [mul_le_mul_of_nonneg_left hlogsmall hhalfpos.le]
  calc
    _ ≤ 16*W/Real.log W+2*W^(1/2 : ℝ) := by dsimp only [Z] at *; linarith
    _ ≤ 16*W/Real.log W+4*W/Real.log W := add_le_add le_rfl herror
    _ = _ := by ring

theorem window_prime_uniform (x L : ℕ) (hx : 2 ≤ x) (hL : 1 ≤ L) :
    (((NormalizedWindowSets.values x L).filter Nat.Prime).card : ℝ) ≤
      20*((L+1 : ℕ) : ℝ)/Real.log ((L+1 : ℕ) : ℝ) := by
  let W : ℝ := ((L+1 : ℕ) : ℝ)
  let Z := ⌊W^(1/8 : ℝ)⌋₊
  have hW : 1 < W := by dsimp [W]; exact_mod_cast (by omega : 1 < L+1)
  have hroot1 : (1 : ℝ) ≤ W^(1/8 : ℝ) := Real.one_le_rpow hW.le (by norm_num)
  have hZ : 1 ≤ Z := Nat.le_floor (by simpa only [Nat.cast_one] using hroot1)
  exact (window_prime_bound x L Z hx hZ).trans (real_level_optimization W hW)

theorem interval_prime_uniform (x H : ℕ) (hx : 1 ≤ x) (hH : 2 ≤ H) :
    (((Ico x (x+H)).filter Nat.Prime).card : ℝ) ≤ 20*(H : ℝ)/Real.log (H : ℝ) := by
  have he : NormalizedWindowSets.values (x+1) (H-1)=Ico x (x+H) := by
    rw [NormalizedWindowSets.values_eq_interval (by omega)]
    congr 1; omega
  have hb := window_prime_uniform (x+1) (H-1) (by omega) (by omega)
  simpa only [he,Nat.sub_add_cancel (by omega : 1 ≤ H)] using hb

theorem interval_prime_log_weight (A H : ℕ) (hA : 1 ≤ A) (hH : 2 ≤ H)
    (hwidth : A+H ≤ H^2) :
    (∑ p ∈ (Ico A (A+H)).filter Nat.Prime, Real.log (p : ℝ)) ≤ 40*(H : ℝ) := by
  have hH1 : (1 : ℝ) < H := by exact_mod_cast (by omega : 1 < H)
  have hlogH : 0 < Real.log (H : ℝ) := Real.log_pos hH1
  have hlogend : 0 ≤ Real.log ((A+H : ℕ) : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ A+H))
  have hlogcap : Real.log ((A+H : ℕ) : ℝ) ≤ 2*Real.log (H : ℝ) := by
    calc
      _ ≤ Real.log ((H : ℝ)^2) := Real.log_le_log
        (by exact_mod_cast (by omega : 0 < A+H)) (by exact_mod_cast hwidth)
      _ = _ := by rw [Real.log_pow]; norm_num
  calc
    _ ≤ ∑ p ∈ (Ico A (A+H)).filter Nat.Prime, Real.log ((A+H : ℕ) : ℝ) := by
      apply sum_le_sum
      intro p hp
      apply Real.log_le_log
      · exact_mod_cast (mem_filter.mp hp).2.pos
      · exact_mod_cast (mem_Ico.mp (mem_filter.mp hp).1).2.le
    _ = (((Ico A (A+H)).filter Nat.Prime).card : ℝ)*Real.log ((A+H : ℕ) : ℝ) := by simp
    _ ≤ (20*(H : ℝ)/Real.log (H : ℝ))*Real.log ((A+H : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_right (interval_prime_uniform A H hA hH) hlogend
    _ ≤ (20*(H : ℝ)/Real.log (H : ℝ))*(2*Real.log (H : ℝ)) :=
      mul_le_mul_of_nonneg_left hlogcap (by positivity)
    _ = _ := by field_simp; ring

theorem interval_prime_reciprocal_log_weight (A H : ℕ) (hA : 1 ≤ A) (hH : 2 ≤ H)
    (hwidth : A+H ≤ H^2) :
    (∑ p ∈ (Ico A (A+H)).filter Nat.Prime, Real.log (p : ℝ)/(p : ℝ)) ≤
      40*(H : ℝ)/(A : ℝ) := by
  have hApos : (0 : ℝ) < A := by exact_mod_cast hA
  calc
    _ ≤ ∑ p ∈ (Ico A (A+H)).filter Nat.Prime, Real.log (p : ℝ)/(A : ℝ) := by
      apply sum_le_sum
      intro p hp
      apply div_le_div_of_nonneg_left
      · exact Real.log_nonneg (by exact_mod_cast (mem_filter.mp hp).2.one_le)
      · exact hApos
      · exact_mod_cast (mem_Ico.mp (mem_filter.mp hp).1).1
    _ = (∑ p ∈ (Ico A (A+H)).filter Nat.Prime, Real.log (p : ℝ))/(A : ℝ) := by
      simp only [div_eq_mul_inv,sum_mul]
    _ ≤ _ := div_le_div_of_nonneg_right (interval_prime_log_weight A H hA hH hwidth) hApos.le
end PaperP1.LocalPrimeSieve

