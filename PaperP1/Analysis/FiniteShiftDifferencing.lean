module

public import PaperP1.Analysis.ShiftedCorrelations

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.FiniteShiftDifferencing
open Finset PaperP1 FiniteDifferencing
open scoped Classical

theorem window_sum {β : Type*} [AddCommMonoid β] (N B : ℕ) (S : Finset ℕ)
    (hS : ∀ h ∈ S, h < B) (a : ℕ → β) :
    (∑ n ∈ range (N+B), ∑ h ∈ S, shifted N a h n)=S.card • (∑ n ∈ range N, a n) := by
  rw [sum_comm]
  calc
    _ = ∑ _h ∈ S, ∑ n ∈ range N, a n := sum_congr rfl (fun h hh ↦ shifted_sum N B h (hS h hh) a)
    _ = _ := by simp

theorem window_cauchy (N B : ℕ) (S : Finset ℕ) (hS : ∀ h ∈ S, h < B) (a : ℕ → ℂ) :
    (S.card : ℝ)^2*‖∑ n ∈ range N, a n‖^2 ≤
      ((N+B : ℕ) : ℝ)*(∑ n ∈ range (N+B), ‖∑ h ∈ S, shifted N a h n‖^2) := by
  have hc := FiniteGramLargeValues.complex_cauchy_square (range (N+B))
    (fun n ↦ ∑ h ∈ S, shifted N a h n) (fun _n ↦ (1 : ℂ))
  have hcard : (∑ _n ∈ range (N+B), ‖(1 : ℂ)‖^2)=((N+B : ℕ) : ℝ) := by simp
  rw [hcard] at hc
  simp only [mul_one] at hc
  rw [window_sum N B S hS a] at hc
  simp only [nsmul_eq_mul,norm_mul,Complex.norm_natCast,mul_pow] at hc
  simpa only [mul_comm] using hc

theorem window_energy_bound (N B : ℕ) (S : Finset ℕ) (a : ℕ → ℂ) :
    (∑ n ∈ range (N+B), ‖∑ h ∈ S, shifted N a h n‖^2) ≤
      ∑ h ∈ S, ∑ k ∈ S, ‖∑ n ∈ range (N+B), shifted N a h n*star (shifted N a k n)‖ := by
  have he := FiniteGramLargeValues.square_expansion (range (N+B)) S
    (fun _h ↦ (1 : ℂ)) (fun h n ↦ shifted N a h n)
  simp only [one_mul,star_one,mul_one,FiniteGramLargeValues.gram] at he
  have hn := congrArg norm he
  rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sum_nonneg (fun _n _hn ↦ sq_nonneg _))] at hn
  rw [hn]
  calc
    _ ≤ ∑ h ∈ S, ‖∑ k ∈ S, ∑ n ∈ range (N+B), shifted N a h n*star (shifted N a k n)‖ := norm_sum_le _ _
    _ ≤ _ := sum_le_sum (fun _h _hh ↦ norm_sum_le _ _)

theorem normalized_correlation_bound (N B : ℕ) (S : Finset ℕ) (hS : ∀ h ∈ S, h < B)
    (hCard : 0 < S.card) (a : ℕ → ℂ) :
    ‖∑ n ∈ range N, a n‖^2 ≤
      (((N+B : ℕ) : ℝ)/(S.card : ℝ)^2)*(∑ h ∈ S, ∑ k ∈ S, ‖ShiftedCorrelations.correlation N a (Nat.dist h k)‖) := by
  have hRaw := (window_cauchy N B S hS a).trans (mul_le_mul_of_nonneg_left
    (window_energy_bound N B S a) (Nat.cast_nonneg _))
  have hEq : (∑ h ∈ S, ∑ k ∈ S, ‖∑ n ∈ range (N+B), shifted N a h n*star (shifted N a k n)‖)=
      ∑ h ∈ S, ∑ k ∈ S, ‖ShiftedCorrelations.correlation N a (Nat.dist h k)‖ := by
    apply sum_congr rfl
    intro h hh
    apply sum_congr rfl
    intro k hk
    exact ShiftedCorrelations.shifted_norm_eq N B h k (hS h hh) (hS k hk) a
  rw [hEq] at hRaw
  have hp : 0 < (S.card : ℝ)^2 := sq_pos_of_pos (by exact_mod_cast hCard)
  calc
    _ ≤ (((N+B : ℕ) : ℝ)*(∑ h ∈ S, ∑ k ∈ S, ‖ShiftedCorrelations.correlation N a (Nat.dist h k)‖))/(S.card : ℝ)^2 :=
      (le_div_iff₀ hp).mpr (by nlinarith only [hRaw])
    _ = _ := by ring

theorem unit_off_diagonal_bound (N B : ℕ) (S : Finset ℕ) (hS : ∀ h ∈ S, h < B)
    (hCard : 0 < S.card) (a : ℕ → ℂ) (ha : ∀ n ∈ range N, ‖a n‖ ≤ 1)
    (E : ℝ) (hE : 0 ≤ E)
    (hCorr : ∀ h ∈ S, ∀ k ∈ S, h ≠ k → ‖ShiftedCorrelations.correlation N a (Nat.dist h k)‖ ≤ E) :
    ‖∑ n ∈ range N, a n‖^2 ≤ ((N+B : ℕ) : ℝ)*((N : ℝ)/(S.card : ℝ)+E) := by
  have hDiag : ‖ShiftedCorrelations.correlation N a 0‖ ≤ (N : ℝ) := by
    rw [ShiftedCorrelations.zero_correlation_norm]
    have hh := sum_le_sum (s := range N) (fun n hn ↦ pow_le_pow_left₀ (norm_nonneg _) (ha n hn) 2)
    simpa using hh
  have hPoint (h : ℕ) (hh : h ∈ S) (k : ℕ) (hk : k ∈ S) :
      ‖ShiftedCorrelations.correlation N a (Nat.dist h k)‖ ≤ (if k=h then (N : ℝ) else 0)+E := by
    by_cases he : k=h
    · subst k
      simpa only [Nat.dist_self,ite_true] using hDiag.trans (le_add_of_nonneg_right hE)
    · simpa only [ite_eq_right he,zero_add] using hCorr h hh k hk (Ne.symm he)
  have hSum : (∑ h ∈ S, ∑ k ∈ S, ‖ShiftedCorrelations.correlation N a (Nat.dist h k)‖) ≤
      (S.card : ℝ)*(N : ℝ)+(S.card : ℝ)^2*E := by
    calc
      _ ≤ ∑ h ∈ S, ∑ k ∈ S, ((if k=h then (N : ℝ) else 0)+E) :=
        sum_le_sum (fun h hh ↦ sum_le_sum (fun k hk ↦ hPoint h hh k hk))
      _ = ∑ _h ∈ S, ((N : ℝ)+(S.card : ℝ)*E) := by
        apply sum_congr rfl
        intro h hh
        simp [sum_add_distrib,hh]
      _ = _ := by simp; ring
  have hCp : (0 : ℝ) < S.card := by exact_mod_cast hCard
  calc
    _ ≤ (((N+B : ℕ) : ℝ)/(S.card : ℝ)^2)*
        (∑ h ∈ S, ∑ k ∈ S, ‖ShiftedCorrelations.correlation N a (Nat.dist h k)‖) :=
      normalized_correlation_bound N B S hS hCard a
    _ ≤ (((N+B : ℕ) : ℝ)/(S.card : ℝ)^2)*((S.card : ℝ)*(N : ℝ)+(S.card : ℝ)^2*E) :=
      mul_le_mul_of_nonneg_left hSum (by positivity)
    _ = _ := by field_simp [hCp.ne']
end PaperP1.FiniteShiftDifferencing
