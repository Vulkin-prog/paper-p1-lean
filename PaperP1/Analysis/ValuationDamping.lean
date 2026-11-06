module

public import PaperP1.Arithmetic.PrimeDivisorWeights
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.ValuationDamping
open Finset Nat MeasureTheory PaperP1
open scoped Classical

def multiplicity (P : Finset ℕ) (n : ℕ) : ℕ := ∑ p ∈ P, n.factorization p

theorem multiplicity_one (P : Finset ℕ) : multiplicity P 1 = 0 := by simp [multiplicity]

theorem multiplicity_mul (P : Finset ℕ) (m n : ℕ) (hm : m ≠ 0) (hn : n ≠ 0) :
    multiplicity P (m*n)=multiplicity P m+multiplicity P n := by
  simp [multiplicity,Nat.factorization_mul hm hn,Finsupp.add_apply,sum_add_distrib]

theorem multiplicity_prime (P : Finset ℕ) (p : ℕ) (hp : p.Prime) :
    multiplicity P p = if p ∈ P then 1 else 0 := by
  simp [multiplicity,hp.factorization,Finsupp.single_apply]

theorem multiplicity_eq_count (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (n : ℕ) (hn : n ≠ 0) (hsq : ∀ p ∈ P, ¬p^2 ∣ n) :
    multiplicity P n=PrimeDivisorWeights.count P n := by
  have he (p : ℕ) (hp : p ∈ P) : n.factorization p = if p ∣ n then 1 else 0 := by
    by_cases hd : p ∣ n
    · have h1 := ((hP p hp).dvd_iff_one_le_factorization hn).mp hd
      have h2 : ¬2 ≤ n.factorization p := by
        intro hh
        exact hsq p hp (((hP p hp).pow_dvd_iff_le_factorization hn).mpr hh)
      simp only [hd,ite_true]
      omega
    · simp [hd,Nat.factorization_eq_zero_of_not_dvd hd]
  unfold multiplicity PrimeDivisorWeights.count PrimeDivisorWeights.factors
  rw [card_eq_sum_ones,sum_filter]
  exact sum_congr rfl he

def damping (P : Finset ℕ) (z : ℝ) : ℕ →* ℝ where
  toFun := fun n ↦ if n=0 then 0 else z^(multiplicity P n)
  map_one' := by simp [multiplicity_one]
  map_mul' := by
    intro m n
    by_cases hm : m=0
    · simp [hm]
    by_cases hn : n=0
    · simp [hn]
    simp [hm,hn,mul_ne_zero hm hn,multiplicity_mul P m n hm hn,pow_add]

theorem damping_zero (P : Finset ℕ) (z : ℝ) : damping P z 0=0 := by simp [damping]

theorem damping_positive (P : Finset ℕ) (z : ℝ) (n : ℕ) (hn : n ≠ 0) :
    damping P z n=z^(multiplicity P n) := by simp [damping,hn]

theorem damping_prime (P : Finset ℕ) (z : ℝ) (p : ℕ) (hp : p.Prime) :
    damping P z p=if p ∈ P then z else 1 := by
  rw [damping_positive P z p hp.ne_zero,multiplicity_prime P p hp]
  split_ifs <;> simp

theorem damping_bound (P : Finset ℕ) (z : ℝ) (hz : |z| ≤ 1) (n : ℕ) :
    |damping P z n| ≤ 1 := by
  by_cases hn : n=0
  · simp [hn,damping_zero]
  rw [damping_positive P z n hn,abs_pow]
  exact pow_le_one₀ (abs_nonneg z) hz

def damped (P : Finset ℕ) (f : ℕ →* ℝ) (z : ℝ) : ℕ →* ℝ := f*damping P z

theorem damped_positive (P : Finset ℕ) (f : ℕ →* ℝ) (z : ℝ) (n : ℕ) (hn : n ≠ 0) :
    damped P f z n=f n*z^(multiplicity P n) := by
  change f n*damping P z n=_
  rw [damping_positive P z n hn]

theorem damped_zero (P : Finset ℕ) (f : ℕ →* ℝ) (z : ℝ) : damped P f z 0=0 := by
  change f 0*damping P z 0=0
  rw [damping_zero,mul_zero]

theorem damped_continuous (P : Finset ℕ) (f : ℕ →* ℝ) (n : ℕ) :
    Continuous (fun z : ℝ ↦ damped P f z n) := by
  by_cases hn : n=0
  · subst n
    simpa only [damped_zero] using (continuous_const : Continuous (fun _z : ℝ ↦ (0 : ℝ)))
  · simp_rw [damped_positive P f _ n hn]
    exact continuous_const.mul (continuous_id.pow _)

theorem damped_prime_bound (P : Finset ℕ) (f : ℕ →* ℝ)
    (hf : ∀ p : ℕ, p.Prime → |f p| ≤ 1) (z : ℝ) (hz : |z| ≤ 1) :
    ∀ p : ℕ, p.Prime → |damped P f z p| ≤ 1 := by
  intro p hp
  change |f p*damping P z p| ≤ 1
  rw [abs_mul]
  exact (mul_le_mul (hf p hp) (damping_bound P z hz p) (abs_nonneg _) zero_le_one).trans_eq (mul_one 1)

theorem damped_integral (P : Finset ℕ) (f : ℕ →* ℝ) (n : ℕ) (hn : n ≠ 0) :
    (∫ z in (0 : ℝ)..1, damped P f z n)=f n/((multiplicity P n+1 : ℕ) : ℝ) := by
  simp_rw [damped_positive P f _ n hn]
  rw [intervalIntegral.integral_const_mul,integral_pow]
  simp [div_eq_mul_inv]

theorem count_denominator_integral (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (f : ℕ →* ℝ) (n : ℕ) (hn : n ≠ 0) (hsq : ∀ p ∈ P, ¬p^2 ∣ n) :
    (∫ z in (0 : ℝ)..1, damped P f z n)=f n/((PrimeDivisorWeights.count P n+1 : ℕ) : ℝ) := by
  rw [damped_integral P f n hn,multiplicity_eq_count P hP n hn hsq]
end PaperP1.ValuationDamping
