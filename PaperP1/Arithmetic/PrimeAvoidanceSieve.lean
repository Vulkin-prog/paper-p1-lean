module

public import PaperP1.Arithmetic.PrimeDivisibilityMoments

/-! # An unconditional finite second-moment sieve for actual prime-avoiding integers -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimeAvoidanceSieve
open Finset PaperP1 PrimeDivisibilityMoments
open scoped Classical

def reciprocalMass (P : Finset ℕ) : ℝ := ∑ p ∈ P, 1/(p : ℝ)

def avoiding (P : Finset ℕ) (X : ℕ) : Finset ℕ :=
  (Ioc 0 X).filter fun n ↦ ∀ p ∈ P, ¬p ∣ n

theorem centered_count (P : Finset ℕ) (n : ℕ) :
    (PrimeDivisorWeights.count P n : ℝ)-reciprocalMass P =
      ∑ p ∈ P, (indicator p n-1/(p : ℝ)) := by
  simp only [sum_sub_distrib,reciprocalMass,PrimeDivisorWeights.count,
    PrimeDivisorWeights.factors,indicator,sum_boole]

theorem variance_identity (P : Finset ℕ) (X : ℕ) :
    (∑ n ∈ Ioc 0 X, ((PrimeDivisorWeights.count P n : ℝ)-reciprocalMass P)^2) =
      ∑ p ∈ P, ∑ q ∈ P, ∑ n ∈ Ioc 0 X,
        (indicator p n-1/(p : ℝ))*(indicator q n-1/(q : ℝ)) := by
  simp_rw [centered_count,pow_two,sum_mul,mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro p hp
  rw [sum_comm]

theorem variance_bound (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (X : ℕ) :
    (∑ n ∈ Ioc 0 X, ((PrimeDivisorWeights.count P n : ℝ)-reciprocalMass P)^2) ≤
      (X : ℝ)*reciprocalMass P + (P.card : ℝ)^2 := by
  have hpair (p : ℕ) (hp : p ∈ P) (q : ℕ) (hq : q ∈ P) :
      (∑ n ∈ Ioc 0 X, (indicator p n-1/(p : ℝ))*(indicator q n-1/(q : ℝ))) ≤
        (if p=q then (X : ℝ)/(p : ℝ) else 0)+1 := by
    by_cases he : p=q
    · subst q
      have hd := diagonal_bound X p (hP p hp).two_le
      simpa only [ite_true,pow_two] using (hd.trans (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)))
    · have hc := (Nat.coprime_primes (hP p hp) (hP q hq)).mpr he
      simpa only [he,ite_false,zero_add] using off_diagonal_bound X p q (hP p hp).two_le (hP q hq).two_le hc
  rw [variance_identity]
  calc
    _ ≤ ∑ p ∈ P, ∑ q ∈ P, ((if p=q then (X : ℝ)/(p : ℝ) else 0)+1) :=
      sum_le_sum (fun p hp ↦ sum_le_sum (fun q hq ↦ hpair p hp q hq))
    _ = ∑ p ∈ P, ((X : ℝ)/(p : ℝ)+(P.card : ℝ)) := by
      apply sum_congr rfl
      intro p hp
      simp [sum_add_distrib,hp]
    _ = _ := by
      rw [sum_add_distrib,reciprocalMass,mul_sum]
      simp only [sum_const,nsmul_eq_mul]
      congr 1
      · apply sum_congr rfl
        intro p hp
        ring
      · ring

theorem avoidance_budget (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (X : ℕ) :
    ((avoiding P X).card : ℝ)*(reciprocalMass P)^2 ≤
      (X : ℝ)*reciprocalMass P + (P.card : ℝ)^2 := by
  have hz (n : ℕ) (hn : n ∈ avoiding P X) : PrimeDivisorWeights.count P n = 0 := by
    rw [PrimeDivisorWeights.count,card_eq_zero]
    apply eq_empty_iff_forall_notMem.mpr
    intro p hp
    exact (mem_filter.mp hn).2 p (mem_filter.mp hp).1 (mem_filter.mp hp).2
  have hsum : ((avoiding P X).card : ℝ)*(reciprocalMass P)^2 =
      ∑ n ∈ avoiding P X, ((PrimeDivisorWeights.count P n : ℝ)-reciprocalMass P)^2 := by
    symm
    calc
      _ = ∑ _n ∈ avoiding P X, (reciprocalMass P)^2 := by
        apply sum_congr rfl
        intro n hn
        rw [hz n hn,Nat.cast_zero,zero_sub,neg_sq]
      _ = _ := by simp
  rw [hsum]
  exact (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun n hn hnot ↦ sq_nonneg _)).trans
    (variance_bound P hP X)

theorem avoidance_card (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (X : ℕ)
    (hH : 0 < reciprocalMass P) :
    ((avoiding P X).card : ℝ) ≤
      (X : ℝ)/reciprocalMass P + (P.card : ℝ)^2/(reciprocalMass P)^2 := by
  have hh := (le_div_iff₀ (sq_pos_of_pos hH)).mpr (avoidance_budget P hP X)
  have he : ((X : ℝ)*reciprocalMass P+(P.card : ℝ)^2)/(reciprocalMass P)^2 =
      (X : ℝ)/reciprocalMass P+(P.card : ℝ)^2/(reciprocalMass P)^2 := by field_simp
  simpa only [he] using hh
end PrimeAvoidanceSieve
