module

public import PaperP1.Analysis.RelativeRamareRemainder
public import PaperP1.Analysis.NarrowPrimeBands

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.NarrowRamareRectangle
open Finset PaperP1
open scoped Classical

def cofactorSet (X H j : ℕ) : Finset ℕ :=
  (Icc 1 (2*X)).filter (fun m ↦ (X : ℝ) ≤ (m : ℝ)*NarrowPrimeBands.anchor H j ∧
    (m : ℝ)*NarrowPrimeBands.anchor H j < 2*(X : ℝ))

def coefficient (P Q : Finset ℕ) (f : ℕ → ℂ) (n : ℕ) : ℂ :=
  f n*(PrimePresence.present Q n : ℂ)/((PrimeDivisorWeights.count P n+1 : ℕ) : ℂ)

def rectangle (X H : ℕ) (P Q : Finset ℕ) (f : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ j ∈ NarrowPrimeBands.indices H P,
    DirichletPolynomialMeanValue.value (NarrowPrimeBands.band H P j) f t*
      DirichletPolynomialMeanValue.value (cofactorSet X H j) (coefficient P Q f) t

theorem cofactorSet_eq_interval (X H j : ℕ) (hX : 0 < X) :
    cofactorSet X H j=Ico ⌈(X : ℝ)/NarrowPrimeBands.anchor H j⌉₊
      ⌈2*(X : ℝ)/NarrowPrimeBands.anchor H j⌉₊ := by
  let u := NarrowPrimeBands.anchor H j
  have hu : 0 < u := NarrowPrimeBands.anchor_pos H j
  have hu1 : 1 ≤ u := NarrowPrimeBands.anchor_one_le H j
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  ext m
  simp only [cofactorSet,mem_filter,mem_Icc,mem_Ico,Nat.ceil_le,Nat.lt_ceil]
  change (1 ≤ m ∧ m ≤ 2*X) ∧ (X : ℝ) ≤ (m : ℝ)*u ∧ (m : ℝ)*u < 2*(X : ℝ) ↔
    (X : ℝ)/u ≤ (m : ℝ) ∧ (m : ℝ) < 2*(X : ℝ)/u
  constructor
  · rintro ⟨_,hl,hr⟩
    exact ⟨(div_le_iff₀ hu).mpr hl,(lt_div_iff₀ hu).mpr hr⟩
  · rintro ⟨hl,hr⟩
    have hl' := (div_le_iff₀ hu).mp hl
    have hr' := (lt_div_iff₀ hu).mp hr
    have hm : 1 ≤ m := by
      by_contra hh
      have hm0 : m=0 := by omega
      simp only [hm0,Nat.cast_zero,zero_mul] at hl'
      linarith
    have hmR : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hmU : (m : ℝ) ≤ 2*(X : ℝ) := by nlinarith
    exact ⟨⟨hm,by exact_mod_cast hmU⟩,hl',hr'⟩

theorem cofactor_endpoints (X H j : ℕ) (hX : 0 < X) :
    1 ≤ ⌈(X : ℝ)/NarrowPrimeBands.anchor H j⌉₊ ∧
    ⌈(X : ℝ)/NarrowPrimeBands.anchor H j⌉₊ ≤ ⌈2*(X : ℝ)/NarrowPrimeBands.anchor H j⌉₊ ∧
    ⌈2*(X : ℝ)/NarrowPrimeBands.anchor H j⌉₊ ≤ 2*⌈(X : ℝ)/NarrowPrimeBands.anchor H j⌉₊ := by
  have hu := NarrowPrimeBands.anchor_pos H j
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  refine ⟨Nat.one_le_ceil_iff.mpr (div_pos hXR hu),Nat.ceil_le_ceil (by gcongr; linarith),?_⟩
  apply Nat.ceil_le.mpr
  have hh := Nat.le_ceil ((X : ℝ)/NarrowPrimeBands.anchor H j)
  push_cast
  calc
    _ = 2*((X : ℝ)/NarrowPrimeBands.anchor H j) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hh (by norm_num)

theorem twist_coefficient (P Q : Finset ℕ) (f : ℕ → ℂ) (m : ℕ) (t : ℝ) :
    DirichletRamareApproximation.twist (coefficient P Q f) m t=
      (PrimePresence.present Q m : ℂ)*DirichletRamareApproximation.twist f m t/
        ((PrimeDivisorWeights.count P m+1 : ℕ) : ℂ) := by
  unfold DirichletRamareApproximation.twist coefficient
  ring

theorem band_product_expansion (X H j : ℕ) (P Q : Finset ℕ) (f : ℕ → ℂ) (t : ℝ) :
    DirichletPolynomialMeanValue.value (NarrowPrimeBands.band H P j) f t*
      DirichletPolynomialMeanValue.value (cofactorSet X H j) (coefficient P Q f) t=
    ∑ p ∈ NarrowPrimeBands.band H P j, ∑ m ∈ Icc 1 (2*X),
      if (X : ℝ) ≤ (m : ℝ)*NarrowPrimeBands.anchor H j ∧
        (m : ℝ)*NarrowPrimeBands.anchor H j < 2*(X : ℝ) then
        DirichletRamareApproximation.twist f p t*((PrimePresence.present Q m : ℂ)*
          DirichletRamareApproximation.twist f m t)/((PrimeDivisorWeights.count P m+1 : ℕ) : ℂ) else 0 := by
  change (∑ p ∈ NarrowPrimeBands.band H P j, DirichletRamareApproximation.twist f p t)*
    (∑ m ∈ cofactorSet X H j, DirichletRamareApproximation.twist (coefficient P Q f) m t)=_
  rw [sum_mul]
  apply sum_congr rfl
  intro p hp
  rw [mul_sum]
  simp_rw [twist_coefficient]
  unfold cofactorSet
  rw [sum_filter]
  apply sum_congr rfl
  intro m hm
  split_ifs <;> ring

theorem rectangle_expansion (X H : ℕ) (P Q : Finset ℕ) (f : ℕ → ℂ) (t : ℝ) :
    rectangle X H P Q f t=
    ∑ p ∈ P, ∑ m ∈ Icc 1 (2*X),
      if (X : ℝ) ≤ (m : ℝ)*NarrowPrimeBands.anchor H (NarrowPrimeBands.index H p) ∧
        (m : ℝ)*NarrowPrimeBands.anchor H (NarrowPrimeBands.index H p) < 2*(X : ℝ) then
        DirichletRamareApproximation.twist f p t*((PrimePresence.present Q m : ℂ)*
          DirichletRamareApproximation.twist f m t)/((PrimeDivisorWeights.count P m+1 : ℕ) : ℂ) else 0 := by
  unfold rectangle
  simp_rw [band_product_expansion]
  rw [NarrowPrimeBands.sum_partition H P]
  apply sum_congr rfl
  intro j hj
  apply sum_congr rfl
  intro p hp
  rw [(mem_filter.mp hp).2]
end PaperP1.NarrowRamareRectangle
