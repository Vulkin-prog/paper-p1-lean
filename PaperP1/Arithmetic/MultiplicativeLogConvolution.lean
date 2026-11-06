module

public import PaperP1.Arithmetic.PrimeLogMertens
public import Mathlib.Analysis.SpecialFunctions.Log.Sum

/-! # Actual logarithmic and prime convolutions for completely multiplicative functions -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.MultiplicativeLogConvolution
open Finset Nat PaperP1
open scoped Classical ArithmeticFunction

def summatory (f : ℕ →* ℂ) (X : ℕ) : ℂ := ∑ n ∈ Icc 1 X, f n

def logarithmic (f : ℕ →* ℂ) (X : ℕ) : ℂ := ∑ n ∈ Icc 1 X, f n*(Real.log (n : ℝ) : ℂ)

def mangoldt (f : ℕ →* ℂ) (X : ℕ) : ℂ :=
  ∑ d ∈ Icc 1 X, (Λ d : ℂ)*f d*summatory f (X/d)

def prime (f : ℕ →* ℂ) (X : ℕ) : ℂ :=
  ∑ p ∈ (Icc 1 X).filter Nat.Prime, (Real.log (p : ℝ) : ℂ)*f p*summatory f (X/p)

theorem multiples_eq_image (X d : ℕ) (hd : 0 < d) :
    (Icc 1 X).filter (fun n ↦ d ∣ n)=(Icc 1 (X/d)).image (fun m ↦ d*m) := by
  ext n
  rw [mem_filter,mem_Icc,mem_image]
  constructor
  · rintro ⟨⟨hn0,hnX⟩,hdn⟩
    obtain ⟨m,rfl⟩ := hdn
    refine ⟨m,mem_Icc.mpr ⟨?_,?_⟩,rfl⟩
    · nlinarith
    · exact (Nat.le_div_iff_mul_le hd).mpr (by nlinarith)
  · rintro ⟨m,hm,rfl⟩
    have hm' := mem_Icc.mp hm
    exact ⟨⟨Nat.mul_pos hd hm'.1,by simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hd).mp hm'.2⟩,
      dvd_mul_right _ _⟩

theorem multiples_sum (X d : ℕ) (hd : 0 < d) (g : ℕ → ℂ) :
    (∑ n ∈ Icc 1 X, if d ∣ n then g n else 0)=∑ m ∈ Icc 1 (X/d), g (d*m) := by
  rw [← sum_filter,multiples_eq_image X d hd,sum_image]
  intro a ha b hb he
  exact Nat.eq_of_mul_eq_mul_left hd he

theorem log_divisor_sum (n X : ℕ) (hn : 0 < n) (hnX : n ≤ X) :
    Real.log (n : ℝ)=∑ d ∈ Icc 1 X, if d ∣ n then Λ d else 0 := by
  have he : (Icc 1 X).filter (fun d ↦ d ∣ n)=n.divisors := by
    ext d
    rw [mem_filter,mem_Icc,Nat.mem_divisors]
    constructor
    · exact fun h ↦ ⟨h.2,hn.ne'⟩
    · intro h
      exact ⟨⟨Nat.pos_of_mem_divisors (Nat.mem_divisors.mpr h),(Nat.le_of_dvd hn h.1).trans hnX⟩,h.1⟩
  rw [← sum_filter,he,ArithmeticFunction.vonMangoldt_sum]

theorem logarithmic_eq_mangoldt (f : ℕ →* ℂ) (X : ℕ) : logarithmic f X=mangoldt f X := by
  calc
    _ = ∑ n ∈ Icc 1 X, ∑ d ∈ Icc 1 X, if d ∣ n then (Λ d : ℂ)*f n else 0 := by
      unfold logarithmic
      apply sum_congr rfl
      intro n hn
      rw [log_divisor_sum n X (mem_Icc.mp hn).1 (mem_Icc.mp hn).2,Complex.ofReal_sum,mul_sum]
      apply sum_congr rfl
      intro d hd
      by_cases hdn : d ∣ n
      · simp only [hdn,ite_true]
        ring
      · simp only [ite_eq_right hdn,Complex.ofReal_zero,mul_zero]
    _ = ∑ d ∈ Icc 1 X, ∑ n ∈ Icc 1 X, if d ∣ n then (Λ d : ℂ)*f n else 0 := sum_comm
    _ = _ := by
      unfold mangoldt
      apply sum_congr rfl
      intro d hd
      rw [multiples_sum X d (mem_Icc.mp hd).1]
      simp only [map_mul,summatory,mul_sum]
      apply sum_congr rfl
      intro m hm
      ring

theorem summatory_norm (f : ℕ →* ℂ) (hf : ∀ n : ℕ, 0 < n → ‖f n‖ ≤ 1) (X : ℕ) :
    ‖summatory f X‖ ≤ X := by
  calc
    _ ≤ ∑ n ∈ Icc 1 X, ‖f n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Icc 1 X, (1 : ℝ) := sum_le_sum (fun n hn ↦ hf n (mem_Icc.mp hn).1)
    _ = _ := by simp [Nat.card_Icc]

theorem mangoldt_sub_prime (f : ℕ →* ℂ) (X : ℕ) :
    mangoldt f X-prime f X=∑ d ∈ Icc 1 X,
      ((if d.Prime then 0 else Λ d : ℝ) : ℂ)*f d*summatory f (X/d) := by
  unfold mangoldt prime
  rw [sum_filter,← sum_sub_distrib]
  apply sum_congr rfl
  intro d hd
  by_cases hp : d.Prime
  · simp only [hp,ite_true,ArithmeticFunction.vonMangoldt_apply_prime hp,Complex.ofReal_zero,zero_mul,sub_self]
  · simp only [hp,ite_false,sub_zero]

theorem prime_power_error (f : ℕ →* ℂ) (hf : ∀ n : ℕ, 0 < n → ‖f n‖ ≤ 1) (X : ℕ) :
    ‖mangoldt f X-prime f X‖ ≤ (X : ℝ)*PrimeLogMertens.primePowerTotal := by
  rw [mangoldt_sub_prime]
  have hpoint (d : ℕ) (hd : d ∈ Icc 1 X) :
      ‖((if d.Prime then 0 else Λ d : ℝ) : ℂ)*f d*summatory f (X/d)‖ ≤
        (X : ℝ)*PrimeLogMertens.primePowerTerm d := by
    let c : ℝ := if d.Prime then 0 else Λ d
    have hc : 0 ≤ c := by dsimp only [c]; split_ifs <;> positivity [ArithmeticFunction.vonMangoldt_nonneg (n := d)]
    have hpair : ‖f d‖*‖summatory f (X/d)‖ ≤ ((X/d : ℕ) : ℝ) := by
      calc
        _ ≤ 1*((X/d : ℕ) : ℝ) := mul_le_mul (hf d (mem_Icc.mp hd).1) (summatory_norm f hf (X/d))
          (norm_nonneg _) (by norm_num)
        _ = _ := one_mul _
    calc
      _ = c*(‖f d‖*‖summatory f (X/d)‖) := by
        rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hc]
        ring
      _ ≤ c*((X/d : ℕ) : ℝ) := mul_le_mul_of_nonneg_left hpair hc
      _ ≤ c*((X : ℝ)/(d : ℝ)) := mul_le_mul_of_nonneg_left Nat.cast_div_le hc
      _ = _ := by dsimp only [c,PrimeLogMertens.primePowerTerm]; ring
  calc
    _ ≤ ∑ d ∈ Icc 1 X, ‖((if d.Prime then 0 else Λ d : ℝ) : ℂ)*f d*summatory f (X/d)‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ Icc 1 X, (X : ℝ)*PrimeLogMertens.primePowerTerm d := sum_le_sum hpoint
    _ = (X : ℝ)*∑ d ∈ Icc 1 X, PrimeLogMertens.primePowerTerm d := by rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (PrimeLogMertens.primePowerTerm_summable.sum_le_tsum _
        (fun d _ ↦ PrimeLogMertens.primePowerTerm_nonneg d)) (Nat.cast_nonneg X)

theorem logarithmic_deficit (f : ℕ →* ℂ) (hf : ∀ n : ℕ, 0 < n → ‖f n‖ ≤ 1)
    (X : ℕ) :
    ‖summatory f X*(Real.log (X : ℝ) : ℂ)-logarithmic f X‖ ≤ X := by
  have he : summatory f X*(Real.log (X : ℝ) : ℂ)-logarithmic f X=
      ∑ n ∈ Icc 1 X, f n*((Real.log (X : ℝ)-Real.log (n : ℝ) : ℝ) : ℂ) := by
    unfold summatory logarithmic
    rw [sum_mul,← sum_sub_distrib]
    apply sum_congr rfl
    intro n hn
    push_cast
    ring
  rw [he]
  have hpoint (n : ℕ) (hn : n ∈ Icc 1 X) :
      ‖f n*((Real.log (X : ℝ)-Real.log (n : ℝ) : ℝ) : ℂ)‖ ≤
        Real.log (X : ℝ)-Real.log (n : ℝ) := by
    have hlog : 0 ≤ Real.log (X : ℝ)-Real.log (n : ℝ) := sub_nonneg.mpr
      (Real.log_le_log (by exact_mod_cast (mem_Icc.mp hn).1) (by exact_mod_cast (mem_Icc.mp hn).2))
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hlog]
    exact (mul_le_mul_of_nonneg_right (hf n (mem_Icc.mp hn).1) hlog).trans_eq (one_mul _)
  calc
    _ ≤ ∑ n ∈ Icc 1 X, ‖f n*((Real.log (X : ℝ)-Real.log (n : ℝ) : ℝ) : ℂ)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Icc 1 X, (Real.log (X : ℝ)-Real.log (n : ℝ)) := sum_le_sum hpoint
    _ ≤ (X : ℝ) := by
      have hset : Icc 1 X=Ioc 0 X := by ext n; simp only [mem_Icc,mem_Ioc]; omega
      have hh := Real.le_sum_log_nat (N := X)
      rw [← hset] at hh
      rw [sum_sub_distrib,sum_const,nsmul_eq_mul,Nat.card_Icc,Nat.add_sub_cancel]
      linarith

theorem prime_reconstruction (f : ℕ →* ℂ) (hf : ∀ n : ℕ, 0 < n → ‖f n‖ ≤ 1)
    (X : ℕ) :
    ‖summatory f X*(Real.log (X : ℝ) : ℂ)-prime f X‖ ≤
      (1+PrimeLogMertens.primePowerTotal)*(X : ℝ) := by
  have he : summatory f X*(Real.log (X : ℝ) : ℂ)-prime f X=
      (summatory f X*(Real.log (X : ℝ) : ℂ)-logarithmic f X)+(mangoldt f X-prime f X) := by
    rw [← logarithmic_eq_mangoldt]
    ring
  rw [he]
  have hh := (norm_add_le _ _).trans (add_le_add (logarithmic_deficit f hf X) (prime_power_error f hf X))
  nlinarith

theorem normalized_prime_reconstruction (f : ℕ →* ℂ)
    (hf : ∀ n : ℕ, 0 < n → ‖f n‖ ≤ 1) (X : ℕ) (hX : 2 ≤ X) :
    ‖summatory f X-prime f X/(Real.log (X : ℝ) : ℂ)‖ ≤
      (1+PrimeLogMertens.primePowerTotal)*(X : ℝ)/Real.log (X : ℝ) := by
  have hlog : 0 < Real.log (X : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < X))
  have hlogC : (Real.log (X : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hlog.ne'
  have he : summatory f X-prime f X/(Real.log (X : ℝ) : ℂ)=
      (summatory f X*(Real.log (X : ℝ) : ℂ)-prime f X)/(Real.log (X : ℝ) : ℂ) := by
    field_simp
  rw [he,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hlog]
  exact div_le_div_of_nonneg_right (prime_reconstruction f hf X) hlog.le
end PaperP1.MultiplicativeLogConvolution


