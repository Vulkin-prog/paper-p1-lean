module

public import PaperP1.Analysis.NearLognormalKernel
public import PaperP1.Analysis.FarLognormalKernel
public import PaperP1.Analysis.DilatedFarLognormalKernel
public import PaperP1.Analysis.LognormalDilatedKernel
public import PaperP1.Analysis.PrimeSelbergCoefficients


set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.LognormalSelbergKernel
open Finset Filter PaperP1
open scoped Classical

def value (A t : ℝ) (Z : ℕ) : ℂ :=
  ∑ d ∈ PrimeSelbergCoefficients.support Z,
    (PrimeSelbergCoefficients.coefficient Z d : ℂ)*LognormalDilatedKernel.multipleValue A t d

theorem main_identity (A t : ℝ) (Z : ℕ) (hZ : 1 ≤ Z) :
    (∑ d ∈ PrimeSelbergCoefficients.support Z,
      (PrimeSelbergCoefficients.coefficient Z d : ℂ)*(1/(d : ℝ) : ℝ)*LognormalDilatedKernel.mainValue A t)=
      (1/PrimeSelbergCoefficients.denominator Z : ℝ)*LognormalDilatedKernel.mainValue A t := by
  calc
    _ = ((∑ d ∈ PrimeSelbergCoefficients.support Z,
        PrimeSelbergCoefficients.coefficient Z d/(d : ℝ) : ℝ) : ℂ)*LognormalDilatedKernel.mainValue A t := by
      push_cast
      rw [sum_mul]
      apply sum_congr rfl
      intro d hd
      simp only [div_eq_mul_inv,one_mul]
    _ = _ := by rw [PrimeSelbergCoefficients.main_mass Z hZ]

theorem difference_identity (A t : ℝ) (Z : ℕ) (hZ : 1 ≤ Z) :
    value A t Z-(1/PrimeSelbergCoefficients.denominator Z : ℝ)*LognormalDilatedKernel.mainValue A t=
      ∑ d ∈ PrimeSelbergCoefficients.support Z, (PrimeSelbergCoefficients.coefficient Z d : ℂ)*
        (LognormalDilatedKernel.multipleValue A t d-(1/(d : ℝ) : ℝ)*LognormalDilatedKernel.mainValue A t) := by
  rw [value,← main_identity A t Z hZ,← sum_sub_distrib]
  apply sum_congr rfl
  intro d hd
  ring

theorem near_bound (A t : ℝ) (Z : ℕ) (hZ : 1 ≤ Z) (hA : 0 < A)
    (hScale : 2*(Z : ℝ)^2 ≤ A) (ht : |t| ≤ (A/(Z : ℝ)^2)^(1/4 : ℝ)) :
    ‖value A t Z-(1/PrimeSelbergCoefficients.denominator Z : ℝ)*LognormalDilatedKernel.mainValue A t‖ ≤
      NearLognormalKernel.constant*(Z : ℝ)^4*A^(3/4 : ℝ) := by
  have hZ1 : (1 : ℝ) ≤ Z := by exact_mod_cast hZ
  have hZ2 : 0 < (Z : ℝ)^2 := by positivity
  have hC := NearLognormalKernel.constant_pos
  have hBaseScale : 2 ≤ A/(Z : ℝ)^2 := (le_div_iff₀ hZ2).mpr hScale
  have hPoint : ∀ d ∈ PrimeSelbergCoefficients.support Z,
      ‖(PrimeSelbergCoefficients.coefficient Z d : ℂ)*
        (LognormalDilatedKernel.multipleValue A t d-(1/(d : ℝ) : ℝ)*LognormalDilatedKernel.mainValue A t)‖ ≤
        |PrimeSelbergCoefficients.coefficient Z d| *(NearLognormalKernel.constant*A^(3/4 : ℝ)) := by
    intro d hd
    by_cases hc : PrimeSelbergCoefficients.coefficient Z d=0
    · simp only [hc,Complex.ofReal_zero,zero_mul,norm_zero,abs_zero,le_refl]
    · have hDd : d ≤ Z^2 := by
        by_contra hnot
        exact hc (PrimeSelbergCoefficients.coefficient_support Z d hd (lt_of_not_ge hnot))
      have hD1 : 1 ≤ d := Nat.pos_of_mem_divisors hd
      have hD1R : (1 : ℝ) ≤ d := by exact_mod_cast hD1
      have hDP : (0 : ℝ) < d := by linarith only [hD1R]
      have hDR : (d : ℝ) ≤ (Z : ℝ)^2 := by exact_mod_cast hDd
      have hLocalScale : A/(Z : ℝ)^2 ≤ A/(d : ℝ) := div_le_div_of_nonneg_left hA.le hDP hDR
      have hLocalFrequency : |t| ≤ (A/(d : ℝ))^(1/4 : ℝ) := ht.trans
        (Real.rpow_le_rpow (div_nonneg hA.le hZ2.le) hLocalScale (by norm_num))
      have hLocal := LognormalDilatedKernel.near_bound A t d hA hDP
        (hBaseScale.trans hLocalScale) hLocalFrequency
      have hPower := Real.rpow_le_rpow (div_nonneg hA.le hDP.le)
        (div_le_self hA.le hD1R) (by norm_num : (0 : ℝ) ≤ 3/4)
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left
        (hLocal.trans (mul_le_mul_of_nonneg_left hPower NearLognormalKernel.constant_pos.le)) (abs_nonneg _)
  rw [difference_identity A t Z hZ]
  calc
    _ ≤ ∑ d ∈ PrimeSelbergCoefficients.support Z,
        ‖(PrimeSelbergCoefficients.coefficient Z d : ℂ)*
          (LognormalDilatedKernel.multipleValue A t d-(1/(d : ℝ) : ℝ)*LognormalDilatedKernel.mainValue A t)‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ PrimeSelbergCoefficients.support Z,
        |PrimeSelbergCoefficients.coefficient Z d| *(NearLognormalKernel.constant*A^(3/4 : ℝ)) := sum_le_sum hPoint
    _ = (∑ d ∈ PrimeSelbergCoefficients.support Z, |PrimeSelbergCoefficients.coefficient Z d|)*
        (NearLognormalKernel.constant*A^(3/4 : ℝ)) := by rw [sum_mul]
    _ ≤ (Z : ℝ)^4*(NearLognormalKernel.constant*A^(3/4 : ℝ)) := mul_le_mul_of_nonneg_right
      (PrimeSelbergCoefficients.absolute_mass Z hZ) (by positivity)
    _ = _ := by ring

theorem far_bound (κ B : ℝ) (hκ : 0 < κ) (hB : 0 < B) :
    ∃ A₀ : ℝ, 8 ≤ A₀ ∧ ∀ A ≥ A₀, ∀ Z : ℕ, 1 ≤ Z → (Z : ℝ)^2 ≤ Real.sqrt A →
      ∀ t : ℝ, A^κ ≤ |t| → |t| ≤ A^B →
        ‖value A t Z‖ ≤ FarLognormalKernel.coefficient (2*B)*(Z : ℝ)^4*
          A^(1-DilatedFarLognormalKernel.decay κ B) := by
  obtain ⟨A₀,hA₀,hFar⟩ := DilatedFarLognormalKernel.uniform_bound κ B hκ hB
  refine ⟨A₀,hA₀,?_⟩
  intro A hA Z hZ hScale t hLower hUpper
  have hAP : 0 < A := by linarith only [hA₀.trans hA]
  have hC := FarLognormalKernel.coefficient_pos (2*B)
  have hPoint : ∀ d ∈ PrimeSelbergCoefficients.support Z,
      ‖(PrimeSelbergCoefficients.coefficient Z d : ℂ)*LognormalDilatedKernel.multipleValue A t d‖ ≤
        |PrimeSelbergCoefficients.coefficient Z d| *
          (FarLognormalKernel.coefficient (2*B)*A^(1-DilatedFarLognormalKernel.decay κ B)) := by
    intro d hd
    by_cases hc : PrimeSelbergCoefficients.coefficient Z d=0
    · simp only [hc,Complex.ofReal_zero,zero_mul,norm_zero,abs_zero,le_refl]
    · have hDd : d ≤ Z^2 := by
        by_contra hnot
        exact hc (PrimeSelbergCoefficients.coefficient_support Z d hd (lt_of_not_ge hnot))
      have hDR : (d : ℝ) ≤ Real.sqrt A := (by exact_mod_cast hDd : (d : ℝ) ≤ (Z : ℝ)^2).trans hScale
      rw [norm_mul,Complex.norm_real,Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hFar A hA d (Nat.pos_of_mem_divisors hd) hDR t hLower hUpper) (abs_nonneg _)
  unfold value
  calc
    _ ≤ ∑ d ∈ PrimeSelbergCoefficients.support Z,
        ‖(PrimeSelbergCoefficients.coefficient Z d : ℂ)*LognormalDilatedKernel.multipleValue A t d‖ := norm_sum_le _ _
    _ ≤ ∑ d ∈ PrimeSelbergCoefficients.support Z,
        |PrimeSelbergCoefficients.coefficient Z d| *
          (FarLognormalKernel.coefficient (2*B)*A^(1-DilatedFarLognormalKernel.decay κ B)) := sum_le_sum hPoint
    _ = (∑ d ∈ PrimeSelbergCoefficients.support Z, |PrimeSelbergCoefficients.coefficient Z d|)*
        (FarLognormalKernel.coefficient (2*B)*A^(1-DilatedFarLognormalKernel.decay κ B)) := by rw [sum_mul]
    _ ≤ (Z : ℝ)^4*(FarLognormalKernel.coefficient (2*B)*A^(1-DilatedFarLognormalKernel.decay κ B)) :=
      mul_le_mul_of_nonneg_right (PrimeSelbergCoefficients.absolute_mass Z hZ) (by positivity)
    _ = _ := by ring
end PaperP1.LognormalSelbergKernel
