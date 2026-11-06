module

public import PaperP1.Analysis.LogarithmicExponentialSum
public import Mathlib.Algebra.Order.Floor.Ring
public import PaperP1.Analysis.LogarithmicDifferencingBound

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.LogarithmicSquareRootBound
open Finset PaperP1
open scoped Classical

def choice (N : ℕ) (r : ℝ) : ℕ := min N ⌈(N : ℝ)/r⌉₊

theorem choice_bounds (N : ℕ) (hN : 0 < N) (r : ℝ) (hr : 1 ≤ r) (hrN : r ≤ N) :
    0 < choice N r ∧ choice N r ≤ N ∧ (N : ℝ)/r ≤ (choice N r : ℝ) ∧
      (choice N r : ℝ) ≤ 2*(N : ℝ)/r := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hrp : 0 < r := by linarith
  let R := (N : ℝ)/r
  have hRone : 1 ≤ R := (one_le_div hrp).mpr hrN
  have hRpos : 0 < R := div_pos hNr hrp
  have hRleN : R ≤ N := by
    apply (div_le_iff₀ hrp).mpr
    have hp := mul_nonneg hNr.le (sub_nonneg.mpr hr)
    nlinarith
  have hLH : R ≤ (choice N r : ℝ) := by
    rw [choice,Nat.cast_min]
    exact le_min hRleN (Nat.le_ceil R)
  have hUH : (choice N r : ℝ) ≤ 2*(N : ℝ)/r := by
    calc
      _ ≤ (⌈R⌉₊ : ℝ) := by exact_mod_cast (Nat.min_le_right N ⌈R⌉₊)
      _ ≤ R+1 := (Nat.ceil_lt_add_one hRpos.le).le
      _ ≤ 2*R := by linarith
      _ = _ := by dsimp only [R]; ring
  exact ⟨by exact_mod_cast hRpos.trans_le hLH,Nat.min_le_left _ _,hLH,hUH⟩

theorem trivial_bound (N : ℕ) (t : ℝ) :
    ‖∑ n ∈ Ico N (2*N), LogarithmicExponentialSum.function t n‖ ≤ (N : ℝ) := by
  calc
    _ ≤ ∑ n ∈ Ico N (2*N), ‖LogarithmicExponentialSum.function t n‖ := norm_sum_le _ _
    _ = _ := by
      simp only [LogarithmicExponentialSum.function_norm,sum_const,nsmul_eq_mul,Nat.card_Ico,mul_one]
      have he : 2*N-N=N := by omega
      rw [he]

theorem square_bound (N : ℕ) (hN : 0 < N) (t : ℝ) (ht : 1 ≤ |t|) :
    ‖∑ n ∈ Ico N (2*N), LogarithmicExponentialSum.function t n‖^2 ≤
      128*((N : ℝ)*Real.sqrt |t|+(N : ℝ)^2/Real.sqrt |t|)*(1+Real.log (N : ℝ)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have htpos : 0 < |t| := by linarith
  have htne : t ≠ 0 := abs_pos.mp htpos
  let r := Real.sqrt |t|
  let L := 1+Real.log (N : ℝ)
  let K := (N : ℝ)*r+(N : ℝ)^2/r
  have hrnonneg : 0 ≤ r := Real.sqrt_nonneg _
  have hrsq : r^2=|t| := Real.sq_sqrt (abs_nonneg t)
  have hr1 : 1 ≤ r := by nlinarith
  have hrpos : 0 < r := by linarith
  have hL1 : 1 ≤ L := by have hl := Real.log_natCast_nonneg N; dsimp only [L]; linarith
  have hLnonneg : 0 ≤ L := by linarith
  have hKnonneg : 0 ≤ K := by dsimp only [K]; positivity
  change ‖∑ n ∈ Ico N (2*N), LogarithmicExponentialSum.function t n‖^2 ≤ 128*K*L
  by_cases hqN : |t| ≤ (N : ℝ)^2
  · have hrN : r ≤ N := by nlinarith
    obtain ⟨hH,hHN,hLH,hUH⟩ := choice_bounds N hN r hr1 hrN
    let H := choice N r
    have hHr : (0 : ℝ) < H := by exact_mod_cast hH
    have hlow : (N : ℝ) ≤ (H : ℝ)*r := (div_le_iff₀ hrpos).mp hLH
    have hupp : (H : ℝ)*r ≤ 2*(N : ℝ) := (le_div_iff₀ hrpos).mp hUH
    have hb1 : 2*(N : ℝ)^2/(H : ℝ) ≤ 2*(N : ℝ)*r := by
      apply (div_le_iff₀ hHr).mpr
      have hm := mul_le_mul_of_nonneg_right hlow (by positivity : 0 ≤ 2*(N : ℝ))
      nlinarith only [hm]
    have hb2 : 96*(N : ℝ)^3/((H : ℝ)*|t|) ≤ 96*(N : ℝ)^2/r := by
      apply (div_le_div_iff₀ (mul_pos hHr htpos) hrpos).mpr
      rw [← hrsq]
      have hm := mul_le_mul_of_nonneg_right hlow (by positivity : 0 ≤ 96*(N : ℝ)^2*r)
      nlinarith only [hm]
    have hb3 : 4*|t| * (H : ℝ) ≤ 8*(N : ℝ)*r := by
      rw [← hrsq]
      have hm := mul_le_mul_of_nonneg_right hupp (by positivity : 0 ≤ 4*r)
      nlinarith only [hm]
    have hb2L := mul_le_mul_of_nonneg_right hb2 hLnonneg
    have hb3L := mul_le_mul_of_nonneg_right hb3 hLnonneg
    have hb1L : 2*(N : ℝ)*r ≤ 2*(N : ℝ)*r*L := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hL1 (show 0 ≤ 2*(N : ℝ)*r by positivity)
    have he := LogarithmicDifferencingBound.expanded_bound N H hH hHN t htne
    calc
      _ ≤ 2*(N : ℝ)^2/(H : ℝ)+96*(N : ℝ)^3/((H : ℝ)*|t|)*L+4*|t| * (H : ℝ)*L := he
      _ ≤ (10*(N : ℝ)*r+96*(N : ℝ)^2/r)*L := by
        nlinarith only [hb1,hb2L,hb3L,hb1L]
      _ ≤ (128*((N : ℝ)*r+(N : ℝ)^2/r))*L := by
        apply mul_le_mul_of_nonneg_right ?_ hLnonneg
        have h1 : 0 ≤ (N : ℝ)*r := by positivity
        have h2 : 0 ≤ (N : ℝ)^2/r := by positivity
        simp only [div_eq_mul_inv] at h2 ⊢
        nlinarith
      _ = _ := by rfl
  · have hrN : (N : ℝ) ≤ r := by nlinarith
    have htriv := pow_le_pow_left₀ (norm_nonneg _) (trivial_bound N t) 2
    have hK : (N : ℝ)^2 ≤ K := by
      have h2 : 0 ≤ (N : ℝ)^2/r := by positivity
      have hp := mul_le_mul_of_nonneg_left hrN hNr.le
      dsimp only [K]
      nlinarith
    have hKL : K ≤ K*L := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hL1 hKnonneg
    have hprod : 0 ≤ K*L := mul_nonneg hKnonneg hLnonneg
    nlinarith only [htriv,hK,hKL,hprod]
end PaperP1.LogarithmicSquareRootBound
