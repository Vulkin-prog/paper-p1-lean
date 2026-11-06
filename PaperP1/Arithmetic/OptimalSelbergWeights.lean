module

public import PaperP1.Arithmetic.DivisorUpperTransform
public import Mathlib.Tactic.FieldSimp

/-! # Actual normalized Selberg weights, exact main sum and support bounds -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OptimalSelbergWeights
open Finset Nat ArithmeticFunction PaperP1
open scoped Classical ArithmeticFunction.Moebius

def levelSet (s : BoundingSieve) (Z : ℕ) : Finset ℕ := s.prodPrimes.divisors.filter (fun d ↦ d ≤ Z)

def denominator (s : BoundingSieve) (Z : ℕ) : ℝ := ∑ d ∈ levelSet s Z, s.selbergTerms d

def target (s : BoundingSieve) (Z d : ℕ) : ℝ :=
  if d ∈ levelSet s Z then (μ d : ℝ)*s.selbergTerms d/denominator s Z else 0

def weight (s : BoundingSieve) (Z d : ℕ) : ℝ :=
  DivisorUpperTransform.upperInverse s.prodPrimes (target s Z) d/s.nu d

theorem denominator_pos (s : BoundingSieve) (Z : ℕ) (hZ : 1 ≤ Z) : 0 < denominator s Z := by
  apply sum_pos'
  · intro d hd
    exact (s.selbergTerms_pos (Nat.dvd_of_mem_divisors (mem_filter.mp hd).1)).le
  · refine ⟨1,mem_filter.mpr ⟨Nat.one_mem_divisors.mpr s.prodPrimes_ne_zero,hZ⟩,?_⟩
    exact s.selbergTerms_pos (one_dvd _)

theorem moebius_sq_real (s : BoundingSieve) (d : ℕ) (hd : d ∣ s.prodPrimes) : (μ d : ℝ)^2=1 := by
  exact_mod_cast moebius_sq_eq_one_of_squarefree (s.squarefree_of_dvd_prodPrimes hd)

theorem inner_transform (s : BoundingSieve) (Z l : ℕ) (hl : l ∣ s.prodPrimes) :
    (∑ d ∈ s.prodPrimes.divisors, if l ∣ d then s.nu d*weight s Z d else 0)=target s Z l := by
  calc
    _ = ∑ d ∈ s.prodPrimes.divisors, if l ∣ d then
        DivisorUpperTransform.upperInverse s.prodPrimes (target s Z) d else 0 := by
      apply sum_congr rfl
      intro d hd
      by_cases hld : l ∣ d
      · rw [ite_eq_left hld,ite_eq_left hld,weight]
        field_simp [s.nu_ne_zero (Nat.dvd_of_mem_divisors hd)]
      · rw [ite_eq_right hld,ite_eq_right hld]
    _ = _ := DivisorUpperTransform.upper_inverse_sum _ _ _ s.prodPrimes_ne_zero hl

theorem weight_one (s : BoundingSieve) (Z : ℕ) (hZ : 1 ≤ Z) : weight s Z 1=1 := by
  have hG := denominator_pos s Z hZ
  rw [weight,DivisorUpperTransform.upper_inverse_one _ _ s.prodPrimes_ne_zero,s.nu_mult.1,div_one]
  have he : (∑ d ∈ s.prodPrimes.divisors, (μ d : ℝ)*target s Z d)=
      ∑ d ∈ levelSet s Z, s.selbergTerms d/denominator s Z := by
    rw [levelSet,sum_filter]
    apply sum_congr rfl
    intro d hd
    by_cases hcut : d ≤ Z
    · have hm : d ∈ levelSet s Z := mem_filter.mpr ⟨hd,hcut⟩
      rw [target,ite_eq_left hm,ite_eq_left hcut]
      have hmu := moebius_sq_real s d (Nat.dvd_of_mem_divisors hd)
      calc
        _ = (μ d : ℝ)^2*s.selbergTerms d/denominator s Z := by ring
        _ = _ := by rw [hmu,one_mul]
    · have hm : d ∉ levelSet s Z := fun hh ↦ hcut (mem_filter.mp hh).2
      rw [target,ite_eq_right hm,ite_eq_right hcut,mul_zero]
  rw [he]
  simp only [div_eq_mul_inv,← sum_mul]
  change denominator s Z/denominator s Z=1
  exact div_self hG.ne'

theorem main_sum_exact (s : BoundingSieve) (Z : ℕ) (hZ : 1 ≤ Z) :
    s.mainSum (BoundingSieve.lambdaSquared (weight s Z))=1/denominator s Z := by
  have hG := denominator_pos s Z hZ
  rw [BoundingSieve.mainSum_lambdaSquared_eq_sum_mul_sum_sq]
  have hi : (∑ l ∈ s.prodPrimes.divisors, (s.selbergTerms l)⁻¹ *
      (∑ d ∈ s.prodPrimes.divisors, if l ∣ d then s.nu d * weight s Z d else 0)^2)=
      ∑ l ∈ s.prodPrimes.divisors, (s.selbergTerms l)⁻¹*(target s Z l)^2 := by
    apply sum_congr rfl
    intro l hl
    rw [inner_transform s Z l (Nat.dvd_of_mem_divisors hl)]
  rw [hi]
  have he : (∑ l ∈ s.prodPrimes.divisors, (s.selbergTerms l)⁻¹*(target s Z l)^2)=
      ∑ l ∈ levelSet s Z, s.selbergTerms l/(denominator s Z)^2 := by
    rw [levelSet,sum_filter]
    apply sum_congr rfl
    intro l hl
    by_cases hcut : l ≤ Z
    · have hm : l ∈ levelSet s Z := mem_filter.mpr ⟨hl,hcut⟩
      rw [target,ite_eq_left hm,ite_eq_left hcut,div_pow,mul_pow,
        moebius_sq_real s l (Nat.dvd_of_mem_divisors hl),one_mul]
      field_simp [(s.selbergTerms_pos (Nat.dvd_of_mem_divisors hl)).ne',hG.ne']
    · have hm : l ∉ levelSet s Z := fun hh ↦ hcut (mem_filter.mp hh).2
      rw [target,ite_eq_right hm,ite_eq_right hcut,zero_pow (by norm_num : 2 ≠ 0),mul_zero]
  rw [he]
  simp only [div_eq_mul_inv,← sum_mul]
  change denominator s Z/(denominator s Z)^2=1/denominator s Z
  field_simp [hG.ne']

theorem moebius_abs_real (s : BoundingSieve) (d : ℕ) (hd : d ∣ s.prodPrimes) :
    |(μ d : ℝ)|=1 := by
  exact_mod_cast abs_moebius_eq_one_of_squarefree (s.squarefree_of_dvd_prodPrimes hd)

theorem target_abs_sum (s : BoundingSieve) (Z : ℕ) (hZ : 1 ≤ Z) :
    (∑ d ∈ s.prodPrimes.divisors, |target s Z d|)=1 := by
  have hG := denominator_pos s Z hZ
  have he : (∑ d ∈ s.prodPrimes.divisors, |target s Z d|)=
      ∑ d ∈ levelSet s Z, s.selbergTerms d/denominator s Z := by
    rw [levelSet,sum_filter]
    apply sum_congr rfl
    intro d hd
    by_cases hcut : d ≤ Z
    · have hm : d ∈ levelSet s Z := mem_filter.mpr ⟨hd,hcut⟩
      rw [target,ite_eq_left hm,ite_eq_left hcut,abs_div,abs_mul,
        moebius_abs_real s d (Nat.dvd_of_mem_divisors hd),
        abs_of_pos (s.selbergTerms_pos (Nat.dvd_of_mem_divisors hd)),abs_of_pos hG,one_mul]
    · have hm : d ∉ levelSet s Z := fun hh ↦ hcut (mem_filter.mp hh).2
      rw [target,ite_eq_right hm,ite_eq_right hcut,abs_zero]
  rw [he]
  simp only [div_eq_mul_inv,← sum_mul]
  change denominator s Z/denominator s Z=1
  exact div_self hG.ne'

theorem weight_support (s : BoundingSieve) (Z d : ℕ) (hd : d ∣ s.prodPrimes)
    (hZd : Z < d) : weight s Z d=0 := by
  rw [weight,DivisorUpperTransform.upper_inverse_explicit _ _ _ s.prodPrimes_ne_zero hd]
  have he : (∑ l ∈ s.prodPrimes.divisors, if d ∣ l then (μ (l/d) : ℝ)*target s Z l else 0)=0 := by
    apply sum_eq_zero
    intro l hl
    by_cases hdl : d ∣ l
    · have hlpos : 0 < l := Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero s.prodPrimes_ne_zero
        (Nat.dvd_of_mem_divisors hl))
      have hdlle : d ≤ l := Nat.le_of_dvd hlpos hdl
      have hnot : l ∉ levelSet s Z := fun hh ↦ (not_le_of_gt (hZd.trans_le hdlle)) (mem_filter.mp hh).2
      rw [ite_eq_left hdl,target,ite_eq_right hnot,mul_zero]
    · rw [ite_eq_right hdl]
  rw [he,zero_div]

theorem upper_inverse_abs_le_one (s : BoundingSieve) (Z d : ℕ) (hZ : 1 ≤ Z)
    (hd : d ∣ s.prodPrimes) :
    |DivisorUpperTransform.upperInverse s.prodPrimes (target s Z) d| ≤ 1 := by
  rw [DivisorUpperTransform.upper_inverse_explicit _ _ _ s.prodPrimes_ne_zero hd]
  calc
    _ ≤ ∑ l ∈ s.prodPrimes.divisors,
        |if d ∣ l then (μ (l/d) : ℝ)*target s Z l else 0| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ l ∈ s.prodPrimes.divisors, |target s Z l| := by
      apply sum_le_sum
      intro l hl
      by_cases hdl : d ∣ l
      · rw [ite_eq_left hdl,abs_mul]
        have hmu : |(μ (l/d) : ℝ)| ≤ 1 := by exact_mod_cast (abs_moebius_le_one (n := l/d))
        exact (mul_le_mul_of_nonneg_right hmu (abs_nonneg _)).trans_eq (one_mul _)
      · rw [ite_eq_right hdl,abs_zero]
        exact abs_nonneg _
    _ = 1 := target_abs_sum s Z hZ

theorem weight_abs_bound (s : BoundingSieve) (Z d : ℕ) (hZ : 1 ≤ Z)
    (hd : d ∣ s.prodPrimes) : |weight s Z d| ≤ 1/s.nu d := by
  rw [weight,abs_div,abs_of_pos (s.nu_pos_of_dvd_prodPrimes hd)]
  exact div_le_div_of_nonneg_right (upper_inverse_abs_le_one s Z d hZ hd)
    (s.nu_pos_of_dvd_prodPrimes hd).le
end PaperP1.OptimalSelbergWeights

