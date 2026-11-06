module

public import PaperP1.Arithmetic.MultiplicativeLogConvolution

/-! # Actual triple prime convolution with real quotient denominators -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RealTripleConvolution
open Finset Nat PaperP1 MultiplicativeLogConvolution
open scoped Classical

def restricted (f : ℕ →* ℂ) (X : ℕ) (P : Finset ℕ) : ℂ :=
  ∑ p ∈ P, (Real.log (p : ℝ) : ℂ)*f p*summatory f (X/p)

def triple (f : ℕ →* ℂ) (X : ℕ) (P : Finset ℕ) : ℂ :=
  ∑ p ∈ P, ((Real.log (p : ℝ)/Real.log ((X : ℝ)/(p : ℝ)) : ℝ) : ℂ)*f p*prime f (X/p)

def reciprocalWeight (X : ℕ) (P : Finset ℕ) : ℝ :=
  ∑ p ∈ P, Real.log (p : ℝ)/((p : ℝ)*Real.log ((X : ℝ)/(p : ℝ)))

theorem logarithmic_deficit_real (f : ℕ →* ℂ) (hf : ∀ n : ℕ, 0 < n → ‖f n‖ ≤ 1)
    (X : ℕ) (R : ℝ) (hX : 1 ≤ X) (hXR : (X : ℝ) ≤ R) :
    ‖summatory f X*(Real.log R : ℂ)-logarithmic f X‖ ≤ R := by
  have hXpos : (0 : ℝ) < X := by exact_mod_cast hX
  have hRpos : 0 < R := lt_of_lt_of_le hXpos hXR
  have hlog : 0 ≤ Real.log R-Real.log (X : ℝ) := sub_nonneg.mpr (Real.log_le_log hXpos hXR)
  have hh := Real.log_le_sub_one_of_pos (div_pos hRpos hXpos)
  rw [Real.log_div hRpos.ne' hXpos.ne'] at hh
  have hmass : (X : ℝ)*(Real.log R-Real.log (X : ℝ)) ≤ R-X := by
    have hm := mul_le_mul_of_nonneg_left hh hXpos.le
    have he : (X : ℝ)*(R/(X : ℝ)-1)=R-X := by field_simp
    rwa [he] at hm
  have he : summatory f X*(Real.log R : ℂ)-logarithmic f X=
      (summatory f X*(Real.log (X : ℝ) : ℂ)-logarithmic f X)+
        summatory f X*((Real.log R-Real.log (X : ℝ) : ℝ) : ℂ) := by push_cast; ring
  rw [he]
  have hnorm : ‖summatory f X*((Real.log R-Real.log (X : ℝ) : ℝ) : ℂ)‖ ≤ R-X := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hlog]
    exact (mul_le_mul_of_nonneg_right (summatory_norm f hf X) hlog).trans hmass
  have he2 := (norm_add_le _ _).trans (add_le_add (logarithmic_deficit f hf X) hnorm)
  linarith

theorem real_denominator_reconstruction (f : ℕ →* ℂ)
    (hf : ∀ n : ℕ, 0 < n → ‖f n‖ ≤ 1) (X : ℕ) (R : ℝ)
    (hX : 1 ≤ X) (hXR : (X : ℝ) ≤ R) (hR : 1 < R) :
    ‖summatory f X-prime f X/(Real.log R : ℂ)‖ ≤
      (1+PrimeLogMertens.primePowerTotal)*R/Real.log R := by
  have hlog : 0 < Real.log R := Real.log_pos hR
  have hlogC : (Real.log R : ℂ) ≠ 0 := by exact_mod_cast hlog.ne'
  have he : summatory f X*(Real.log R : ℂ)-prime f X=
      (summatory f X*(Real.log R : ℂ)-logarithmic f X)+(mangoldt f X-prime f X) := by
    rw [← logarithmic_eq_mangoldt]
    ring
  have hn : ‖summatory f X*(Real.log R : ℂ)-prime f X‖ ≤
      (1+PrimeLogMertens.primePowerTotal)*R := by
    rw [he]
    have hh := (norm_add_le _ _).trans (add_le_add
      (logarithmic_deficit_real f hf X R hX hXR) (prime_power_error f hf X))
    nlinarith [PrimeLogMertens.primePowerTotal_nonneg]
  have hid : summatory f X-prime f X/(Real.log R : ℂ)=
      (summatory f X*(Real.log R : ℂ)-prime f X)/(Real.log R : ℂ) := by field_simp
  rw [hid,norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hlog]
  exact div_le_div_of_nonneg_right hn hlog.le

theorem quotient_reconstruction (f : ℕ →* ℂ) (hf : ∀ n : ℕ, 0 < n → ‖f n‖ ≤ 1)
    (X p : ℕ) (hp : 0 < p) (hXp : 2*p ≤ X) :
    ‖summatory f (X/p)-prime f (X/p)/(Real.log ((X : ℝ)/(p : ℝ)) : ℂ)‖ ≤
      (1+PrimeLogMertens.primePowerTotal)*((X : ℝ)/(p : ℝ))/Real.log ((X : ℝ)/(p : ℝ)) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hfloor : 1 ≤ X/p := by
    apply (Nat.le_div_iff_mul_le hp).mpr
    nlinarith
  have hR : 1 < (X : ℝ)/(p : ℝ) := by
    apply (lt_div_iff₀ hpR).mpr
    norm_num only [one_mul]
    exact_mod_cast (show p < X by omega)
  exact real_denominator_reconstruction f hf (X/p) ((X : ℝ)/(p : ℝ)) hfloor Nat.cast_div_le hR

theorem triple_error (f : ℕ →* ℂ) (hf : ∀ n : ℕ, 0 < n → ‖f n‖ ≤ 1)
    (X : ℕ) (P : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p ∧ 2*p ≤ X) :
    ‖restricted f X P-triple f X P‖ ≤
      (1+PrimeLogMertens.primePowerTotal)*(X : ℝ)*reciprocalWeight X P := by
  have he : restricted f X P-triple f X P=∑ p ∈ P,
      (Real.log (p : ℝ) : ℂ)*f p*(summatory f (X/p)-prime f (X/p)/(Real.log ((X : ℝ)/(p : ℝ)) : ℂ)) := by
    unfold restricted triple
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro p hp
    push_cast
    ring
  rw [he]
  have hpoint (p : ℕ) (hp : p ∈ P) :
      ‖(Real.log (p : ℝ) : ℂ)*f p*(summatory f (X/p)-prime f (X/p)/(Real.log ((X : ℝ)/(p : ℝ)) : ℂ))‖ ≤
        (1+PrimeLogMertens.primePowerTotal)*(X : ℝ)*
          (Real.log (p : ℝ)/((p : ℝ)*Real.log ((X : ℝ)/(p : ℝ)))) := by
    have hprime := (hP p hp).1
    have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hprime.one_le)
    rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hlogp]
    have hb := quotient_reconstruction f hf X p hprime.pos (hP p hp).2
    have hnormf := hf p hprime.pos
    calc
      _ ≤ (Real.log (p : ℝ)*1)*
          ((1+PrimeLogMertens.primePowerTotal)*((X : ℝ)/(p : ℝ))/Real.log ((X : ℝ)/(p : ℝ))) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left hnormf hlogp
        · exact hb
        · exact norm_nonneg _
        · positivity
      _ = _ := by ring
  calc
    _ ≤ ∑ p ∈ P, ‖(Real.log (p : ℝ) : ℂ)*f p*(summatory f (X/p)-prime f (X/p)/(Real.log ((X : ℝ)/(p : ℝ)) : ℂ))‖ := norm_sum_le _ _
    _ ≤ ∑ p ∈ P, (1+PrimeLogMertens.primePowerTotal)*(X : ℝ)*
        (Real.log (p : ℝ)/((p : ℝ)*Real.log ((X : ℝ)/(p : ℝ)))) := sum_le_sum hpoint
    _ = _ := by rw [reciprocalWeight,mul_sum]

theorem triple_expansion (f : ℕ →* ℂ) (X : ℕ) (P : Finset ℕ) :
    triple f X P=∑ p ∈ P, ∑ q ∈ (Icc 1 (X/p)).filter Nat.Prime,
      ∑ n ∈ Icc 1 (X/(p*q)),
        ((Real.log (p : ℝ)*Real.log (q : ℝ)/Real.log ((X : ℝ)/(p : ℝ)) : ℝ) : ℂ)*f p*f q*f n := by
  unfold triple prime summatory
  apply sum_congr rfl
  intro p hp
  rw [mul_sum]
  apply sum_congr rfl
  intro q hq
  simp only [Nat.div_div_eq_div_mul,mul_sum]
  apply sum_congr rfl
  intro n hn
  push_cast
  ring
end PaperP1.RealTripleConvolution
