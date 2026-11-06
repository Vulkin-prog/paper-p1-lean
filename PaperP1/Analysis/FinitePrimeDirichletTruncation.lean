module

public import PaperP1.Analysis.FinitePrimeReciprocalTail
public import Mathlib.Data.Nat.Factorization.Induction

/-! # Actual finite integer truncation of finite-prime Dirichlet series -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FinitePrimeDirichletTruncation
open Finset PaperP1 LogarithmicPhase DirichletRamareApproximation
  FinitePrimeReciprocalTail
open scoped Classical

def indices (P : Finset ℕ) (X : ℕ) : Finset (Nat.factoredNumbers P) :=
  (Icc 1 X).subtype (fun n ↦ n ∈ Nat.factoredNumbers P)

def total (P : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑' n : Nat.factoredNumbers P, twist a n t

def truncated (P : Finset ℕ) (X : ℕ) (a : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ n ∈ indices P X, twist a n t

theorem truncated_continuous (P : Finset ℕ) (X : ℕ) (a : ℕ → ℂ) : Continuous (truncated P X a) := by
  apply continuous_finsetSum
  intro n hn
  exact twist_continuous a n

theorem reciprocal_summable (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    Summable (fun n : Nat.factoredNumbers P ↦ 1/(n : ℝ)) := by
  have hs := (FinitePrimeDirichletSeries.summable_and_hasSum P hP (1 : ℕ →* ℝ) (by intro p hp; simp) 0).1
  simpa only [MonoidHom.one_apply,Complex.ofReal_one,twist_norm,norm_one] using hs

theorem norm_summable (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (a : ℕ → ℂ)
    (ha : ∀ n ∈ Nat.factoredNumbers P, ‖a n‖ ≤ 1) (t : ℝ) :
    Summable (fun n : Nat.factoredNumbers P ↦ ‖twist a n t‖) := by
  apply Summable.of_nonneg_of_le (fun n ↦ norm_nonneg _) _ (reciprocal_summable P hP)
  intro n
  rw [twist_norm]
  exact div_le_div_of_nonneg_right (ha n n.property) (Nat.cast_nonneg (n : ℕ))

theorem complement_reciprocal (P : Finset ℕ) (X : ℕ) :
    (∑' n : {n : Nat.factoredNumbers P // n ∉ indices P X}, 1/((n.val : ℕ) : ℝ)) = tail P (X : ℝ) := by
  have he := _root_.tsum_subtype ({n : Nat.factoredNumbers P | n ∉ indices P X})
    (fun n : Nat.factoredNumbers P ↦ 1/(n : ℝ))
  have hcast : (∑' n : {n : Nat.factoredNumbers P // n ∉ indices P X}, 1/((n.val : ℕ) : ℝ)) =
      ∑' n : Nat.factoredNumbers P, ({n : Nat.factoredNumbers P | n ∉ indices P X} : Set _).indicator (fun n ↦ 1/(n : ℝ)) n := by
    convert he using 1
  rw [hcast]
  unfold tail
  apply tsum_congr
  intro n
  have hnpos : 1 ≤ (n : ℕ) := by have hh := n.property.1; omega
  have hmem : n ∉ indices P X ↔ X < (n : ℕ) := by
    simp only [indices,Finset.mem_subtype,Finset.mem_Icc]
    omega
  by_cases hn : X < (n : ℕ)
  · have hreal : (X : ℝ) < n := by exact_mod_cast hn
    simp [hmem,hn,hreal]
  · have hreal : ¬(X : ℝ) < n := by exact_mod_cast hn
    simp [hmem,hn,hreal]

theorem truncation_error (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (X : ℕ) (a : ℕ → ℂ)
    (ha : ∀ n ∈ Nat.factoredNumbers P, ‖a n‖ ≤ 1) (t : ℝ) :
    ‖total P a t-truncated P X a t‖ ≤ tail P (X : ℝ) := by
  have hs := norm_summable P hP a ha t
  have hc : Summable (fun n : Nat.factoredNumbers P ↦ twist a n t) := Summable.of_norm hs
  have he := hc.sum_add_tsum_subtype_compl (indices P X)
  change truncated P X a t+(∑' n : {n : Nat.factoredNumbers P // n ∉ indices P X}, twist a n t)=total P a t at he
  have hd : total P a t-truncated P X a t =
      ∑' n : {n : Nat.factoredNumbers P // n ∉ indices P X}, twist a n t := by rw [← he]; abel
  rw [hd]
  have hnorm := hs.subtype (fun n ↦ n ∉ indices P X)
  have hrecip := (reciprocal_summable P hP).subtype (fun n ↦ n ∉ indices P X)
  calc
    _ ≤ ∑' n : {n : Nat.factoredNumbers P // n ∉ indices P X}, ‖twist a n t‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : {n : Nat.factoredNumbers P // n ∉ indices P X}, 1/((n.val : ℕ) : ℝ) :=
      hnorm.tsum_le_tsum (fun n ↦ by rw [twist_norm]; exact div_le_div_of_nonneg_right (ha n n.val.property) (Nat.cast_nonneg _)) hrecip
    _ = _ := complement_reciprocal P X

theorem slow_band_uniform_truncation :
    ∀ᶠ N : ℕ in Filter.atTop, ∀ a : ℕ → ℂ,
      (∀ n ∈ Nat.factoredNumbers (SlowPrimeBandSieve.primes N), ‖a n‖ ≤ 1) → ∀ t : ℝ,
      ‖total (SlowPrimeBandSieve.primes N) a t-truncated (SlowPrimeBandSieve.primes N) N a t‖ ≤
        (N : ℝ)^(-(1/4 : ℝ)) := by
  filter_upwards [slow_band_tail_bound_eventually] with N htail a ha t
  exact (truncation_error (SlowPrimeBandSieve.primes N) (fun p hp ↦ (mem_filter.mp hp).2) N a ha t).trans htail

theorem real_hom_bound (f : ℕ →* ℝ) (hf : ∀ p : ℕ, p.Prime → |f p| ≤ 1) (n : ℕ) (hn : n ≠ 0) :
    |f n| ≤ 1 := by
  induction n using Nat.recOnMul with
  | zero => exact False.elim (hn rfl)
  | one => simp
  | prime p hp => exact hf p hp
  | mul a b ha hb =>
    have hne := Nat.mul_ne_zero_iff.mp hn
    rw [f.map_mul,abs_mul]
    exact (mul_le_mul (ha hne.1) (hb hne.2) (abs_nonneg _) (by norm_num)).trans_eq (by norm_num)
end FinitePrimeDirichletTruncation
