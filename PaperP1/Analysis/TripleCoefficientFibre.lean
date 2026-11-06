module

public import PaperP1.Arithmetic.MultiplicativeLogConvolution
public import PaperP1.Analysis.FiniteGaussianPerron
public import PaperP1.Analysis.PrimeFactorCauchy
set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.TripleCoefficientFibre
open Finset Nat MeasureTheory PaperP1
open scoped Classical ArithmeticFunction

def triples (P Q S : Finset ℕ) : Finset ((ℕ × ℕ) × ℕ) := (P ×ˢ Q) ×ˢ S

def level (z : (ℕ × ℕ) × ℕ) : ℕ := (z.1.1*z.1.2)*z.2

def primeDivisors (m : ℕ) : Finset ℕ := m.divisors.filter Nat.Prime

theorem level_pos (P Q S : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime)
    (hS : ∀ n ∈ S, 0 < n) (z : (ℕ × ℕ) × ℕ) (hz : z ∈ triples P Q S) : 0 < level z := by
  have hz' := mem_product.mp hz
  have hpq := mem_product.mp hz'.1
  exact Nat.mul_pos (Nat.mul_pos (hP _ hpq.1).pos (hQ _ hpq.2).pos) (hS _ hz'.2)

theorem prime_divisor_log_bound (m : ℕ) : (∑ p ∈ primeDivisors m, Real.log (p : ℝ)) ≤ Real.log (m : ℝ) := by
  calc
    _ = ∑ p ∈ primeDivisors m, Λ p := by
      apply sum_congr rfl
      intro p hp
      exact (ArithmeticFunction.vonMangoldt_apply_prime (mem_filter.mp hp).2).symm
    _ ≤ ∑ d ∈ m.divisors, Λ d := sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      (fun d _ _ ↦ ArithmeticFunction.vonMangoldt_nonneg)
    _ = _ := ArithmeticFunction.vonMangoldt_sum

theorem fibre_mass_bound (P Q S : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime)
    (hS : ∀ n ∈ S, 0 < n) (m : ℕ) :
    (∑ z ∈ (triples P Q S).filter (fun z ↦ level z=m),
      Real.log (z.1.1 : ℝ)*Real.log (z.1.2 : ℝ)) ≤ (Real.log (m : ℝ))^2 := by
  let E := (triples P Q S).filter (fun z ↦ level z=m)
  have hinj : Set.InjOn (Prod.fst : ((ℕ × ℕ) × ℕ) → ℕ × ℕ) (E : Set ((ℕ × ℕ) × ℕ)) := by
    intro z hz z' hz' he
    have hmem := mem_product.mp (mem_filter.mp hz).1
    have hpq := mem_product.mp hmem.1
    have hprod : 0 < z.1.1*z.1.2 := Nat.mul_pos (hP _ hpq.1).pos (hQ _ hpq.2).pos
    have hh : (z.1.1*z.1.2)*z.2=(z'.1.1*z'.1.2)*z'.2 :=
      (mem_filter.mp hz).2.trans (mem_filter.mp hz').2.symm
    have hn : z.2=z'.2 := by
      apply Nat.eq_of_mul_eq_mul_left hprod
      simpa only [he] using hh
    exact Prod.ext he hn
  have hmap : E.image Prod.fst ⊆ (primeDivisors m) ×ˢ (primeDivisors m) := by
    intro pq hpq
    obtain ⟨z,hz,rfl⟩ := mem_image.mp hpq
    have hmem := mem_product.mp (mem_filter.mp hz).1
    have hpq := mem_product.mp hmem.1
    have he := (mem_filter.mp hz).2
    have hmpos : 0 < m := by rw [← he]; exact level_pos P Q S hP hQ hS z (mem_filter.mp hz).1
    have hpdiv : z.1.1 ∣ m := by
      refine ⟨z.1.2*z.2,?_⟩
      rw [← he]
      dsimp only [level]
      ring
    have hqdiv : z.1.2 ∣ m := by
      refine ⟨z.1.1*z.2,?_⟩
      rw [← he]
      dsimp only [level]
      ring
    exact mem_product.mpr
      ⟨mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hpdiv,hmpos.ne'⟩,hP _ hpq.1⟩,
       mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hqdiv,hmpos.ne'⟩,hQ _ hpq.2⟩⟩
  calc
    _ ≤ ∑ pq ∈ (primeDivisors m) ×ˢ (primeDivisors m), Real.log (pq.1 : ℝ)*Real.log (pq.2 : ℝ) := by
      apply sum_le_sum_of_injOn Prod.fst hinj hmap
      · intro z hz
        exact le_rfl
      · intro pq hpq hnot
        exact mul_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)
    _ = (∑ p ∈ primeDivisors m, Real.log (p : ℝ))^2 := by
      rw [pow_two,sum_mul_sum,sum_product]
    _ ≤ _ := pow_le_pow_left₀ (sum_nonneg (fun p _ ↦ Real.log_natCast_nonneg p)) (prime_divisor_log_bound m) 2

theorem coefficient_fibre_bound (P Q S : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime)
    (hS : ∀ n ∈ S, 0 < n) (a : ((ℕ × ℕ) × ℕ) → ℂ) (A : ℝ) (hA : 0 ≤ A)
    (ha : ∀ z ∈ triples P Q S, ‖a z‖ ≤ A*(Real.log (z.1.1 : ℝ)*Real.log (z.1.2 : ℝ))) (m : ℕ) :
    (∑ z ∈ (triples P Q S).filter (fun z ↦ level z=m), ‖a z‖) ≤ A*(Real.log (m : ℝ))^2 := by
  calc
    _ ≤ ∑ z ∈ (triples P Q S).filter (fun z ↦ level z=m),
        A*(Real.log (z.1.1 : ℝ)*Real.log (z.1.2 : ℝ)) := sum_le_sum (fun z hz ↦ ha z (mem_filter.mp hz).1)
    _ = A*(∑ z ∈ (triples P Q S).filter (fun z ↦ level z=m),
        Real.log (z.1.1 : ℝ)*Real.log (z.1.2 : ℝ)) := by rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (fibre_mass_bound P Q S hP hQ hS m) hA

def coefficient (f : ℕ → ℂ) (X : ℕ) (z : (ℕ × ℕ) × ℕ) : ℂ :=
  ((Real.log (z.1.1 : ℝ)*Real.log (z.1.2 : ℝ)/Real.log ((X : ℝ)/(z.1.1 : ℝ)) : ℝ) : ℂ)*
    f z.1.1*f z.1.2*f z.2

theorem coefficient_norm_bound (f : ℕ → ℂ) (hf : ∀ n : ℕ, 0 < n → ‖f n‖ ≤ 1)
    (X : ℕ) (P Q S : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ 2*p ≤ X)
    (hQ : ∀ q ∈ Q, q.Prime) (hS : ∀ n ∈ S, 0 < n)
    (z : (ℕ × ℕ) × ℕ) (hz : z ∈ triples P Q S) :
    ‖coefficient f X z‖ ≤ (1/Real.log 2)*(Real.log (z.1.1 : ℝ)*Real.log (z.1.2 : ℝ)) := by
  have hz' := mem_product.mp hz
  have hpq := mem_product.mp hz'.1
  have hp := hP _ hpq.1
  have hq := hQ _ hpq.2
  have hn := hS _ hz'.2
  have hpR : (0 : ℝ) < z.1.1 := by exact_mod_cast hp.1.pos
  have htwo : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlog : Real.log 2 ≤ Real.log ((X : ℝ)/(z.1.1 : ℝ)) := by
    apply Real.log_le_log (by norm_num)
    apply (le_div_iff₀ hpR).mpr
    exact_mod_cast hp.2
  have hlog0 : 0 < Real.log ((X : ℝ)/(z.1.1 : ℝ)) := lt_of_lt_of_le htwo hlog
  have hlogp : 0 ≤ Real.log (z.1.1 : ℝ) := Real.log_natCast_nonneg _
  have hlogq : 0 ≤ Real.log (z.1.2 : ℝ) := Real.log_natCast_nonneg _
  have hcoef : 0 ≤ Real.log (z.1.1 : ℝ)*Real.log (z.1.2 : ℝ)/Real.log ((X : ℝ)/(z.1.1 : ℝ)) := by positivity
  have hunit : ‖f z.1.1‖*‖f z.1.2‖*‖f z.2‖ ≤ 1 := by
    have hpq : ‖f z.1.1‖*‖f z.1.2‖ ≤ 1 := by
      have hh := mul_le_mul (hf _ hp.1.pos) (hf _ hq.pos) (norm_nonneg _) (by norm_num)
      simpa only [one_mul] using hh
    have hh := mul_le_mul hpq (hf _ hn) (norm_nonneg _) (by norm_num)
    simpa only [one_mul] using hh
  rw [coefficient,norm_mul,norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hcoef]
  calc
    _ = (Real.log (z.1.1 : ℝ)*Real.log (z.1.2 : ℝ)/Real.log ((X : ℝ)/(z.1.1 : ℝ)))*
        (‖f z.1.1‖*‖f z.1.2‖*‖f z.2‖) := by ring
    _ ≤ (Real.log (z.1.1 : ℝ)*Real.log (z.1.2 : ℝ)/Real.log ((X : ℝ)/(z.1.1 : ℝ)))*1 :=
      mul_le_mul_of_nonneg_left hunit hcoef
    _ ≤ _ := by
      rw [mul_one]
      have hh := div_le_div_of_nonneg_left (mul_nonneg hlogp hlogq) htwo hlog
      convert hh using 1; ring

theorem actual_coefficient_fibre_bound (f : ℕ → ℂ) (hf : ∀ n : ℕ, 0 < n → ‖f n‖ ≤ 1)
    (X : ℕ) (P Q S : Finset ℕ) (hP : ∀ p ∈ P, p.Prime ∧ 2*p ≤ X)
    (hQ : ∀ q ∈ Q, q.Prime) (hS : ∀ n ∈ S, 0 < n) (m : ℕ) :
    (∑ z ∈ (triples P Q S).filter (fun z ↦ level z=m), ‖coefficient f X z‖) ≤
      (1/Real.log 2)*(Real.log (m : ℝ))^2 := by
  apply coefficient_fibre_bound P Q S (fun p hp ↦ (hP p hp).1) hQ hS (coefficient f X) (1/Real.log 2) (by positivity)
  intro z hz
  exact coefficient_norm_bound f hf X P Q S hP hQ hS z hz

theorem polynomial_factorization (f : ℕ → ℂ) (X : ℕ) (P Q S : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime) (hS : ∀ n ∈ S, 0 < n) (t : ℝ) :
    FiniteGaussianPerron.polynomial (triples P Q S) (coefficient f X) level t=
      WeightedPrimeMean.value P (PrimeFactorCauchy.bandCoefficient f (X : ℝ)) t*
        WeightedPrimeMean.value Q f t*FiniteGaussianPerron.polynomial S f id t := by
  simp only [FiniteGaussianPerron.polynomial,triples,sum_product,WeightedPrimeMean.value,
    GaussianExponentialSums.polynomial,PrimeFactorCauchy.bandCoefficient,mul_sum,sum_mul]
  conv_rhs =>
    rw [sum_comm]
    arg 2
    ext q
    rw [sum_comm]
  conv_rhs => rw [sum_comm]
  apply sum_congr rfl
  intro p hp
  apply sum_congr rfl
  intro q hq
  apply sum_congr rfl
  intro n hn
  have hpR : (0 : ℝ) < p := by exact_mod_cast (hP p hp).pos
  have hqR : (0 : ℝ) < q := by exact_mod_cast (hQ q hq).pos
  have hnR : (0 : ℝ) < n := by exact_mod_cast hS n hn
  have hphase : LogarithmicPhase.phase (-Real.log (((p*q)*n : ℕ) : ℝ)) t=
      LogarithmicPhase.phase (-Real.log (p : ℝ)) t*LogarithmicPhase.phase (-Real.log (q : ℝ)) t*
        LogarithmicPhase.phase (-Real.log (n : ℝ)) t := by
    rw [Nat.cast_mul,Nat.cast_mul,Real.log_mul (mul_ne_zero hpR.ne' hqR.ne') hnR.ne',Real.log_mul hpR.ne' hqR.ne']
    simp only [neg_add,LogarithmicPhase.phase_add]
  dsimp only [coefficient,level,id_eq]
  rw [hphase]
  push_cast
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring
end PaperP1.TripleCoefficientFibre

