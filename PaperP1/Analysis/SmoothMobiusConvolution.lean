module

public import PaperP1.Arithmetic.OrdinarySmoothIndicator
public import PaperP1.Arithmetic.LocalPrimeSieve
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius


set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.SmoothMobiusConvolution
open Finset Nat ArithmeticFunction PaperP1
open scoped Classical ArithmeticFunction

def roughMobius (Y : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n ↦ if (primorial Y).Coprime n then (moebius n : ℝ) else 0, by simp⟩

theorem roughMobius_apply (Y n : ℕ) :
    roughMobius Y n = if (primorial Y).Coprime n then (moebius n : ℝ) else 0 := rfl

theorem roughMobius_multiplicative (Y : ℕ) : (roughMobius Y).IsMultiplicative := by
  refine ⟨by simp [roughMobius_apply], ?_⟩
  intro m n hmn
  have hmu := isMultiplicative_moebius.map_mul_of_coprime hmn
  simp only [roughMobius_apply, Nat.coprime_mul_iff_right, hmu, Int.cast_mul]
  split_ifs <;> simp_all

theorem roughMobius_abs (Y n : ℕ) : |roughMobius Y n| ≤ 1 := by
  rw [roughMobius_apply]
  split_ifs
  · exact_mod_cast (abs_moebius_le_one (n := n))
  · norm_num

theorem indicator_pow (Y n k : ℕ) (hY : 1 ≤ Y) :
    OrdinarySmoothIndicator.value Y (n^k) = (OrdinarySmoothIndicator.value Y n)^k := by
  induction k with
  | zero => simp [OrdinarySmoothIndicator.value_one Y hY]
  | succ k hk => rw [pow_succ, OrdinarySmoothIndicator.value_mul, hk, pow_succ]

theorem small_prime_power (Y p k : ℕ) (hp : p.Prime) (hpY : p ≤ Y) :
    roughMobius Y (p^k) = if k=0 then 1 else 0 := by
  by_cases hk : k=0
  · simp [hk,roughMobius_apply]
  have hnp : ¬ (primorial Y).Coprime (p^k) := by
    intro hc
    have hcp := (Nat.coprime_pow_right_iff (Nat.pos_of_ne_zero hk) _ _).mp hc
    have hd : p ∣ primorial Y := hp.dvd_primorial_iff.mpr hpY
    exact hp.not_dvd_one (hcp.gcd_eq_one ▸ Nat.dvd_gcd hd (dvd_refl p))
  simp [roughMobius_apply,hnp,hk]

theorem large_prime_power (Y p k : ℕ) (hp : p.Prime) (hYp : Y < p) :
    roughMobius Y (p^k) = (moebius (p^k) : ℝ) := by
  have hc := (LocalPrimeSieve.prime_coprime_primorial p Y hp hYp).pow_right k
  simp [roughMobius_apply,hc]

theorem convolution (Y : ℕ) (hY : 1 ≤ Y) :
    (zeta * roughMobius Y : ArithmeticFunction ℝ) = OrdinarySmoothIndicator.arithmetic Y := by
  apply (IsMultiplicative.eq_iff_eq_on_prime_powers _
    (isMultiplicative_zeta.natCast.mul (roughMobius_multiplicative Y)) _
    (OrdinarySmoothIndicator.isMultiplicative Y hY)).mpr
  intro p k hp
  change (zeta * roughMobius Y : ArithmeticFunction ℝ) (p^k) =
    OrdinarySmoothIndicator.value Y (p^k)
  rw [indicator_pow Y p k hY]
  by_cases hpY : p ≤ Y
  · have hv : OrdinarySmoothIndicator.value Y p = 1 := by
      simp [OrdinarySmoothIndicator.value,hp.ne_zero,
        OrdinarySmoothCensus.largestPrimeFactor_prime hp,hpY]
    rw [hv,one_pow,coe_zeta_mul_apply,Nat.sum_divisors_prime_pow hp]
    simp_rw [small_prime_power Y p _ hp hpY]
    simp
  · have hv : OrdinarySmoothIndicator.value Y p = 0 := by
      simp [OrdinarySmoothIndicator.value,OrdinarySmoothCensus.largestPrimeFactor_prime hp,hpY]
    have he : (zeta * roughMobius Y : ArithmeticFunction ℝ) (p^k) =
        (zeta * (moebius : ArithmeticFunction ℝ)) (p^k) := by
      rw [coe_zeta_mul_apply,coe_zeta_mul_apply,Nat.sum_divisors_prime_pow hp,
        Nat.sum_divisors_prime_pow hp]
      apply sum_congr rfl
      intro i hi
      exact large_prime_power Y p i hp (lt_of_not_ge hpY)
    rw [he,coe_zeta_mul_coe_moebius,hv]
    by_cases hk : k=0
    · simp [hk]
    · simp [hk,hp.ne_one]

theorem divisor_sum (Y n : ℕ) (hY : 1 ≤ Y) :
    OrdinarySmoothIndicator.value Y n = ∑ d ∈ n.divisors, roughMobius Y d := by
  have he := congrArg (fun f : ArithmeticFunction ℝ ↦ f n) (convolution Y hY)
  rw [coe_zeta_mul_apply] at he
  exact he.symm

end PaperP1.SmoothMobiusConvolution
