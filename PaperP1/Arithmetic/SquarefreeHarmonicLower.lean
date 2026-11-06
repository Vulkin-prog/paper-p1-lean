module

public import PaperP1.Analysis.ReciprocalSquareTail
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.NumberTheory.Primorial
public import PaperP1.Arithmetic.OptimalSelbergWeights
public import PaperP1.Arithmetic.ReciprocalDivisibilitySieve

/-! # A logarithmic Selberg denominator from actual squarefree harmonic sums -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SquarefreeHarmonicLower
open Finset Nat PaperP1
open scoped Classical

def squarefreeSet (Z : ℕ) : Finset ℕ := (Icc 1 Z).filter Squarefree

def squarefreeHarmonic (Z : ℕ) : ℝ := ∑ d ∈ squarefreeSet Z, 1/(d : ℝ)

theorem harmonic_le_twice_squarefree (Z : ℕ) :
    (∑ n ∈ Icc 1 Z, 1/(n : ℝ)) ≤ 2*squarefreeHarmonic Z := by
  let R := (Icc 1 Z) ×ˢ squarefreeSet Z
  let f : ℕ × ℕ → ℕ := fun q ↦ q.1^2*q.2
  have hsub : Icc 1 Z ⊆ R.image f := by
    intro n hn
    have hn0 : 0 < n := (mem_Icc.mp hn).1
    obtain ⟨a,b,ha,hb,he,hs⟩ := Nat.sq_mul_squarefree_of_pos hn0
    have ha_le : a ≤ n := Nat.le_of_dvd hn0 ⟨b^2,by nlinarith [he]⟩
    have hb_le : b ≤ n := Nat.le_of_dvd hn0 ⟨b*a,by nlinarith [he]⟩
    apply mem_image.mpr
    refine ⟨(b,a),?_,he⟩
    exact mem_product.mpr ⟨mem_Icc.mpr ⟨hb,hb_le.trans (mem_Icc.mp hn).2⟩,
      mem_filter.mpr ⟨mem_Icc.mpr ⟨ha,ha_le.trans (mem_Icc.mp hn).2⟩,hs⟩⟩
  calc
    _ ≤ ∑ n ∈ R.image f, 1/(n : ℝ) :=
      sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ ↦ by positivity)
    _ ≤ ∑ q ∈ R, 1/(f q : ℝ) := sum_image_le_of_nonneg (fun _ _ ↦ by positivity)
    _ = (∑ b ∈ Icc 1 Z, 1/(b : ℝ)^2)*squarefreeHarmonic Z := by
      dsimp only [R,squarefreeHarmonic]
      rw [sum_product,sum_mul_sum]
      apply sum_congr rfl
      intro b hb
      apply sum_congr rfl
      intro a ha
      simp only [f,Nat.cast_mul,Nat.cast_pow,one_div_mul_one_div]
    _ ≤ 2*squarefreeHarmonic Z := by
      have hh := ReciprocalSquareTail.interval_bound 1 Z (by decide)
      norm_num only [Nat.cast_one,div_one] at hh
      exact mul_le_mul_of_nonneg_right hh (sum_nonneg (fun _ _ ↦ by positivity))

theorem logarithmic_lower (Z : ℕ) :
    Real.log ((Z+1 : ℕ) : ℝ)/2 ≤ squarefreeHarmonic Z := by
  have hh := harmonic_le_twice_squarefree Z
  have hlog := log_add_one_le_harmonic Z
  have he : (harmonic Z : ℝ)=∑ n ∈ Icc 1 Z, 1/(n : ℝ) := by
    simp only [harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast,one_div]
  rw [he] at hlog
  linarith

theorem selberg_term_ge_density (s : BoundingSieve) (d : ℕ) (hd : d ∣ s.prodPrimes) :
    s.nu d ≤ s.selbergTerms d := by
  rw [BoundingSieve.selbergTerms_apply]
  have hp : (1 : ℝ) ≤ ∏ p ∈ d.primeFactors, (1-s.nu p)⁻¹ := by
    apply one_le_prod₀
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors hp
    have hpd := (Nat.dvd_of_mem_primeFactors hp).trans hd
    have hpos := s.nu_pos_of_prime p hprime hpd
    have hlt := s.nu_lt_one_of_prime p hprime hpd
    apply (one_le_inv₀ (by linarith : 0 < 1-s.nu p)).mpr
    linarith
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hp (s.nu_pos_of_dvd_prodPrimes hd).le

theorem squarefree_divides_primorial (Z d : ℕ) (hd : d ∈ squarefreeSet Z) :
    d ∣ primorial Z := by
  have hsd := (mem_filter.mp hd).2
  exact hsd.dvd_primorial.trans (primorial_dvd_primorial (mem_Icc.mp (mem_filter.mp hd).1).2)

theorem denominator_log_lower (x L Z : ℕ) :
    Real.log ((Z+1 : ℕ) : ℝ)/2 ≤ OptimalSelbergWeights.denominator
      (ReciprocalDivisibilitySieve.sieve x L (primorial Z) (squarefree_primorial Z)) Z := by
  let s := ReciprocalDivisibilitySieve.sieve x L (primorial Z) (squarefree_primorial Z)
  have hsub : squarefreeSet Z ⊆ OptimalSelbergWeights.levelSet s Z := by
    intro d hd
    exact mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨squarefree_divides_primorial Z d hd,
      primorial_ne_zero Z⟩,(mem_Icc.mp (mem_filter.mp hd).1).2⟩
  calc
    _ ≤ squarefreeHarmonic Z := logarithmic_lower Z
    _ ≤ ∑ d ∈ squarefreeSet Z, s.selbergTerms d := by
      apply sum_le_sum
      intro d hd
      exact selberg_term_ge_density s d (squarefree_divides_primorial Z d hd)
    _ ≤ ∑ d ∈ OptimalSelbergWeights.levelSet s Z, s.selbergTerms d := by
      apply sum_le_sum_of_subset_of_nonneg hsub
      intro d hd hnot
      exact (s.selbergTerms_pos (Nat.dvd_of_mem_divisors (mem_filter.mp hd).1)).le
    _ = _ := rfl
end PaperP1.SquarefreeHarmonicLower
