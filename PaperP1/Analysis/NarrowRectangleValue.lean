module

public import PaperP1.Analysis.RelativePrimeRamare
public import PaperP1.Analysis.NarrowPrimeBands
public import PaperP1.Analysis.NarrowRamareRectangle
public import PaperP1.Analysis.NarrowRectangleWeight

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.NarrowRectangleValue
open Finset PaperP1 PrimeDivisorWeights
open scoped Classical

def coefficient (X H : ℕ) (P Q : Finset ℕ) (f : ℕ → ℂ) (n : ℕ) : ℂ :=
  (NarrowRectangleWeight.weight X H P n : ℂ)*(PrimePresence.present Q n : ℂ)*f n

theorem test_source_mem (X H p m : ℕ) (hX : 0 < X) (hH : 2 ≤ H) (hp : 1 ≤ p)
    (ht : NarrowRectangleWeight.test X H p m) : p*m ∈ Ico X (4*X) := by
  have hh := NarrowRectangleWeight.test_product_bounds X H p m hX hH hp ht
  have hg := NarrowPrimeBands.growth_le_two H hH
  have hXR : (0 : ℝ) ≤ X := Nat.cast_nonneg X
  have hu : ((p*m : ℕ) : ℝ) < 4*(X : ℝ) := by nlinarith only [hh.2,hg,hXR]
  exact mem_Ico.mpr ⟨by exact_mod_cast hh.1,by exact_mod_cast hu⟩

theorem weighted_sum_identity (X H : ℕ) (hX : 0 < X) (hH : 2 ≤ H)
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (a b : ℕ → ℂ)
    (hb : ∀ p ∈ P, ∀ m : ℕ, b (p*m)=a p*b m) :
    (∑ n ∈ Ico X (4*X), (NarrowRectangleWeight.weight X H P n : ℂ)*b n)=
      ∑ p ∈ P, ∑ m ∈ Icc 1 (2*X), if NarrowRectangleWeight.test X H p m then
        a p*b m/((count P m+1 : ℕ) : ℂ) else 0 := by
  let S := Ico X (4*X)
  have hS : ∀ n ∈ S, 0 < n ∧ n ≤ 4*X := by
    intro n hn
    have hh := mem_Ico.mp hn
    omega
  calc
    _ = ∑ n ∈ S, ∑ p ∈ factors P n,
        if NarrowRectangleWeight.test X H p (n/p) then b n/((count P (n/p)+1 : ℕ) : ℂ) else 0 := by
      apply sum_congr rfl
      intro n hn
      rw [NarrowRectangleWeight.weight,Complex.ofReal_sum,sum_mul]
      apply sum_congr rfl
      intro p hp
      split_ifs <;> push_cast <;> ring
    _ = ∑ p ∈ P, ∑ n ∈ S.filter (p ∣ ·),
        if NarrowRectangleWeight.test X H p (n/p) then b n/((count P (n/p)+1 : ℕ) : ℂ) else 0 := by
      simp only [factors,sum_filter]
      rw [sum_comm]
    _ = ∑ p ∈ P, ∑ m ∈ Icc 1 (4*X/p), if NarrowRectangleWeight.test X H p m then
        a p*b m/((count P m+1 : ℕ) : ℂ) else 0 := by
      apply sum_congr rfl
      intro p hp
      rw [sum_multiples S (4*X) p (hP p hp).pos hS]
      apply sum_congr rfl
      intro m hm
      rw [Nat.mul_div_cancel_left m (hP p hp).pos,hb p hp m]
      by_cases ht : NarrowRectangleWeight.test X H p m
      · have hi : p*m ∈ S := test_source_mem X H p m hX hH (hP p hp).one_le ht
        simp only [ht,hi,ite_true]
      · simp only [ht,ite_false,ite_self]
    _ = _ := by
      apply sum_congr rfl
      intro p hp
      have hdiv : 4*X/p ≤ 2*X := Nat.div_le_of_le_mul (by nlinarith [(hP p hp).two_le])
      have hsub : Icc 1 (4*X/p) ⊆ Icc 1 (2*X) := by
        intro m hm
        exact mem_Icc.mpr ⟨(mem_Icc.mp hm).1,(mem_Icc.mp hm).2.trans hdiv⟩
      apply sum_subset hsub
      intro m hm hnot
      have ht : ¬NarrowRectangleWeight.test X H p m := by
        intro ht
        have hu := (mem_Ico.mp (test_source_mem X H p m hX hH (hP p hp).one_le ht)).2
        have hmd : m ≤ 4*X/p := (Nat.le_div_iff_mul_le (hP p hp).pos).mpr (by nlinarith only [hu])
        exact hnot (mem_Icc.mpr ⟨(mem_Icc.mp hm).1,hmd⟩)
      exact ite_eq_right ht

theorem rectangle_value_identity (X H : ℕ) (hX : 0 < X) (hH : 2 ≤ H)
    (P Q : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime)
    (hPQ : Disjoint P Q) (f : ℕ → ℂ) (hf : ∀ a b, f (a*b)=f a*f b) (t : ℝ) :
    NarrowRamareRectangle.rectangle X H P Q f t=
      DirichletPolynomialMeanValue.value (Ico X (4*X)) (coefficient X H P Q f) t := by
  have hh := weighted_sum_identity X H hX hH P hP (fun n ↦ DirichletRamareApproximation.twist f n t)
    (RelativePrimeRamare.presenceCoefficient Q (fun n ↦ DirichletRamareApproximation.twist f n t))
    (RelativePrimeRamare.presence_relative P Q hP hQ hPQ (fun n ↦ DirichletRamareApproximation.twist f n t)
      (DirichletRamareApproximation.twist_mul f hf t))
  rw [NarrowRamareRectangle.rectangle_expansion]
  change _=DirichletPolynomialMeanValue.value (Ico X (4*X))
    (fun n ↦ (NarrowRectangleWeight.weight X H P n : ℂ)*(PrimePresence.present Q n : ℂ)*f n) t
  rw [RelativePrimeRamare.value_weighted_sum]
  calc
    _ = ∑ p ∈ P, ∑ m ∈ Icc 1 (2*X), if NarrowRectangleWeight.test X H p m then
        DirichletRamareApproximation.twist f p t*((PrimePresence.present Q m : ℂ)*
          DirichletRamareApproximation.twist f m t)/((count P m+1 : ℕ) : ℂ) else 0 := by
      apply sum_congr rfl
      intro p hp
      apply sum_congr rfl
      intro m hm
      by_cases ht : NarrowRectangleWeight.test X H p m
      · have ht' : (X : ℝ) ≤ (m : ℝ)*NarrowPrimeBands.anchor H (NarrowPrimeBands.index H p) ∧
            (m : ℝ)*NarrowPrimeBands.anchor H (NarrowPrimeBands.index H p) < 2*(X : ℝ) := ht
        rw [ite_eq_left ht,ite_eq_left ht']
      · have ht' : ¬((X : ℝ) ≤ (m : ℝ)*NarrowPrimeBands.anchor H (NarrowPrimeBands.index H p) ∧
            (m : ℝ)*NarrowPrimeBands.anchor H (NarrowPrimeBands.index H p) < 2*(X : ℝ)) := ht
        rw [ite_eq_right ht,ite_eq_right ht']
    _ = _ := by simpa only [RelativePrimeRamare.presenceCoefficient,mul_assoc] using hh.symm
end PaperP1.NarrowRectangleValue
