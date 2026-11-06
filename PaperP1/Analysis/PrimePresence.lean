module

public import PaperP1.Analysis.ValuationDamping

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.PrimePresence
open Finset Nat PaperP1
open scoped Classical

def present (Q : Finset ℕ) (n : ℕ) : ℝ := if 0 < PrimeDivisorWeights.count Q n then 1 else 0

theorem present_bounds (Q : Finset ℕ) (n : ℕ) : 0 ≤ present Q n ∧ present Q n ≤ 1 := by
  unfold present
  split_ifs <;> norm_num

theorem present_abs_bound (Q : Finset ℕ) (n : ℕ) : |present Q n| ≤ 1 := by
  rw [abs_of_nonneg (present_bounds Q n).1]
  exact (present_bounds Q n).2

theorem count_zero_iff (Q : Finset ℕ) (n : ℕ) :
    PrimeDivisorWeights.count Q n=0 ↔ ∀ p ∈ Q, ¬p ∣ n := by
  constructor
  · intro hc p hp hd
    have hh := PrimeDivisorWeights.count_pos hp hd
    omega
  · intro hnot
    unfold PrimeDivisorWeights.count PrimeDivisorWeights.factors
    rw [Finset.card_eq_zero]
    apply eq_empty_iff_forall_notMem.mpr
    intro p hp
    exact hnot p (mem_filter.mp hp).1 (mem_filter.mp hp).2

theorem multiplicity_zero_iff (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) (n : ℕ) (hn : n ≠ 0) :
    ValuationDamping.multiplicity Q n=0 ↔ PrimeDivisorWeights.count Q n=0 := by
  constructor
  · intro hm
    apply (count_zero_iff Q n).mpr
    intro p hp hd
    have hfac := ((hQ p hp).dvd_iff_one_le_factorization hn).mp hd
    have hsingle : n.factorization p ≤ ValuationDamping.multiplicity Q n := by
      change n.factorization p ≤ ∑ q ∈ Q, n.factorization q
      exact single_le_sum (fun _q _hq ↦ Nat.zero_le _) hp
    omega
  · intro hc
    have hnot := (count_zero_iff Q n).mp hc
    unfold ValuationDamping.multiplicity
    apply sum_eq_zero
    intro p hp
    exact Nat.factorization_eq_zero_of_not_dvd (hnot p hp)

theorem present_zero_damping (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) (n : ℕ) (hn : n ≠ 0) :
    present Q n=1-ValuationDamping.damping Q 0 n := by
  rw [ValuationDamping.damping_positive Q 0 n hn]
  by_cases hc : PrimeDivisorWeights.count Q n=0
  · have hm := (multiplicity_zero_iff Q hQ n hn).mpr hc
    simp [present,hc,hm]
  · have hm : ValuationDamping.multiplicity Q n ≠ 0 :=
      fun hh ↦ hc ((multiplicity_zero_iff Q hQ n hn).mp hh)
    have hp : 0 < PrimeDivisorWeights.count Q n := Nat.pos_of_ne_zero hc
    simp [present,hp,zero_pow hm]

theorem present_damped_difference (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime)
    (f : ℕ →* ℝ) (n : ℕ) (hn : n ≠ 0) :
    f n*present Q n=f n-ValuationDamping.damped Q f 0 n := by
  change f n*present Q n=f n-f n*ValuationDamping.damping Q 0 n
  rw [present_zero_damping Q hQ n hn]
  ring

theorem factors_mul_outside (Q : Finset ℕ) (hQ : ∀ q ∈ Q, q.Prime) (p : ℕ) (hp : p.Prime)
    (hpQ : p ∉ Q) (m : ℕ) : PrimeDivisorWeights.factors Q (p*m)=PrimeDivisorWeights.factors Q m := by
  ext q
  simp only [PrimeDivisorWeights.factors,mem_filter]
  constructor
  · intro hq
    refine ⟨hq.1,?_⟩
    rcases (hQ q hq.1).dvd_mul.mp hq.2 with hd | hd
    · have he : q=p := (Nat.prime_dvd_prime_iff_eq (hQ q hq.1) hp).mp hd
      exact False.elim (hpQ (he ▸ hq.1))
    · exact hd
  · intro hq
    exact ⟨hq.1,dvd_mul_of_dvd_right hq.2 p⟩

theorem count_mul_outside (Q : Finset ℕ) (hQ : ∀ q ∈ Q, q.Prime) (p : ℕ) (hp : p.Prime)
    (hpQ : p ∉ Q) (m : ℕ) : PrimeDivisorWeights.count Q (p*m)=PrimeDivisorWeights.count Q m := by
  rw [PrimeDivisorWeights.count,PrimeDivisorWeights.count,factors_mul_outside Q hQ p hp hpQ m]

theorem present_mul_outside (Q : Finset ℕ) (hQ : ∀ q ∈ Q, q.Prime) (p : ℕ) (hp : p.Prime)
    (hpQ : p ∉ Q) (m : ℕ) : present Q (p*m)=present Q m := by
  rw [present,present,count_mul_outside Q hQ p hp hpQ m]

theorem complex_coefficient_bound (Q : Finset ℕ) (f : ℕ → ℂ) (n : ℕ) (hf : ‖f n‖ ≤ 1) :
    ‖(present Q n : ℂ)*f n‖ ≤ 1 := by
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
  exact (mul_le_mul (present_abs_bound Q n) hf (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)
end PaperP1.PrimePresence
