module

public import PaperP1.Analysis.FullEulerBound
public import PaperP1.Analysis.FinitePrimeDirichletSeries

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.ComplexEuler
open Finset Nat MeasureTheory PaperP1 LogarithmicPhase Filter
open scoped Classical

theorem complex_hom_bound (g : ℕ →* ℂ) (hg : ∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) (n : ℕ) (hn : n ≠ 0) : ‖g n‖ ≤ 1 := by
  induction n using Nat.recOnMul with
  | zero => exact False.elim (hn rfl)
  | one => simp
  | prime p hp => exact hg p hp
  | mul a b ha hb =>
    have hne := Nat.mul_ne_zero_iff.mp hn
    rw [g.map_mul,norm_mul]
    exact (mul_le_mul (ha hne.1) (hb hne.2) (norm_nonneg _) (by norm_num)).trans_eq (by norm_num)

def twistHom (g : ℕ →* ℂ) (t : ℝ) : ℕ →* ℂ where
  toFun n := DirichletRamareApproximation.twist g n t
  map_one' := by simp [DirichletRamareApproximation.twist,phase]
  map_mul' m n := DirichletRamareApproximation.twist_mul g (fun a b ↦ g.map_mul a b) t m n

def product (P : Finset ℕ) (g : ℕ →* ℂ) (t : ℝ) : ℂ :=
  FiniteEulerLogBound.product P (fun p ↦ DirichletRamareApproximation.twist g p t)

theorem prime_half (g : ℕ →* ℂ) (hg : ∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) (p : ℕ) (hp : p.Prime) (t : ℝ) :
    ‖DirichletRamareApproximation.twist g p t‖ ≤ 1/2 := by
  rw [DirichletRamareApproximation.twist_norm]
  exact (div_le_div_of_nonneg_right (hg p hp) (Nat.cast_nonneg p)).trans
    (div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by exact_mod_cast hp.two_le))

theorem summable_and_hasSum (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (g : ℕ →* ℂ) (hg : ∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) (t : ℝ) :
    Summable (fun n : Nat.factoredNumbers P ↦ ‖DirichletRamareApproximation.twist g n t‖) ∧
      HasSum (fun n : Nat.factoredNumbers P ↦ DirichletRamareApproximation.twist g n t) (product P g t) := by
  have hprime : ∀ {p : ℕ}, p.Prime → ‖twistHom g t p‖ < 1 := by
    intro p hp
    exact lt_of_le_of_lt (prime_half g hg p hp t) (by norm_num)
  have hh := EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_geometric hprime P
  have he : P.filter Nat.Prime=P := filter_eq_self.mpr hP
  rw [he] at hh
  exact hh

theorem total_eq_product (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (g : ℕ →* ℂ) (hg : ∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) (t : ℝ) :
    FinitePrimeDirichletTruncation.total P g t=product P g t := (summable_and_hasSum P hP g hg t).2.tsum_eq

theorem product_continuous (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (g : ℕ →* ℂ) (hg : ∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) : Continuous (product P g) := by
  unfold product FiniteEulerLogBound.product
  apply continuous_finsetProd
  intro p hp
  exact (continuous_const.sub (DirichletRamareApproximation.twist_continuous g p)).inv₀
    (fun t ↦ FiniteEulerLogBound.factor_ne _ (prime_half g hg p (hP p hp) t))


theorem product_log_bound (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (g : ℕ →* ℂ) (hg : ∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) (t : ℝ) :
    ‖product P g t‖ ≤ Real.exp (PrimeAvoidanceSieve.reciprocalMass P+(∑ p ∈ P, 1/(p : ℝ)^2)) := by
  have hn (p : ℕ) (hp : p ∈ P) : ‖DirichletRamareApproximation.twist g p t‖ ≤ 1/(p : ℝ) := by
    rw [DirichletRamareApproximation.twist_norm]
    exact div_le_div_of_nonneg_right (hg p (hP p hp)) (Nat.cast_nonneg p)
  have hh := FiniteEulerLogBound.norm_product_bound P (fun p ↦ DirichletRamareApproximation.twist g p t)
    (fun p hp ↦ prime_half g hg p (hP p hp) t)
  have hr : (∑ p ∈ P, (DirichletRamareApproximation.twist g p t).re) ≤ PrimeAvoidanceSieve.reciprocalMass P :=
    sum_le_sum (fun p hp ↦ (Complex.re_le_norm _).trans (hn p hp))
  have hs : (∑ p ∈ P, ‖DirichletRamareApproximation.twist g p t‖^2) ≤ ∑ p ∈ P, 1/(p : ℝ)^2 := by
    apply sum_le_sum
    intro p hp
    simpa only [div_pow,one_pow] using pow_le_pow_left₀ (norm_nonneg _) (hn p hp) 2
  exact hh.trans (Real.exp_le_exp.mpr (add_le_add hr hs))

theorem product_global_bound (X : ℕ) (hX : 2 ≤ X) (g : ℕ →* ℂ)
    (hg : ∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) (t : ℝ) :
    ‖product (FixedEulerTruncation.primes X) g t‖ ≤ FullEulerBound.eulerConstant*Real.log (X : ℝ) := by
  have hP := FixedEulerTruncation.primes_prime X
  have hH := FullEulerBound.harmonic_upper X hX
  have hs := FullEulerBound.prime_square_bound (FixedEulerTruncation.primes X) hP
  have hl : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < X))
  calc
    _ ≤ Real.exp (PrimeAvoidanceSieve.reciprocalMass (FixedEulerTruncation.primes X)+
        (∑ p ∈ FixedEulerTruncation.primes X, 1/(p : ℝ)^2)) := product_log_bound _ hP g hg t
    _ ≤ Real.exp (Real.log (Real.log (X : ℝ))+FullEulerBound.harmonicConstant+1) := Real.exp_le_exp.mpr (by linarith)
    _ = _ := by
      rw [show Real.log (Real.log (X : ℝ))+FullEulerBound.harmonicConstant+1=
          (FullEulerBound.harmonicConstant+1)+Real.log (Real.log (X : ℝ)) by ring,Real.exp_add,Real.exp_log hl]
      rfl

theorem total_global_bound (X : ℕ) (hX : 2 ≤ X) (g : ℕ →* ℂ)
    (hg : ∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) (t : ℝ) :
    ‖FinitePrimeDirichletTruncation.total (FixedEulerTruncation.primes X) g t‖ ≤ FullEulerBound.eulerConstant*Real.log (X : ℝ) := by
  rw [total_eq_product _ (FixedEulerTruncation.primes_prime X) g hg t]
  exact product_global_bound X hX g hg t

theorem total_continuous (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (g : ℕ →* ℂ) (hg : ∀ p : ℕ, p.Prime → ‖g p‖ ≤ 1) :
    Continuous (FinitePrimeDirichletTruncation.total P g) := by
  exact FixedEulerTruncation.total_continuous P hP g (fun n hn ↦ complex_hom_bound g hg n hn.1)
end PaperP1.ComplexEuler
