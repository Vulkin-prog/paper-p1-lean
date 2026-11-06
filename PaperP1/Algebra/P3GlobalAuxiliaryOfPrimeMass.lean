module

public import PaperP1.Algebra.P3GlobalAuxiliaryFromCanonicalDivisors
public import PaperP1.Analysis.P3SmoothGlobalDivisorEstimate

/-! # One explicit elementary prime-sum inequality constructs an original smooth-surface auxiliary equation -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3GlobalAuxiliaryOfPrimeMass

open MvPolynomial Finset P3StandardMonomialParameters
open scoped Classical

theorem exists_auxiliary (d e A H : ℕ) (hd : 0 < d) (he : d ≤ e) (hA : 0 < A) (hH : 1 ≤ H)
    (P : MvPolynomial (Fin 4) ℤ) (hP0 : P ≠ 0) (hhom : P.IsHomogeneous d)
    (hnot : ¬X (3 : Fin 4) ∣ map (Int.castRingHom ℚ) P) (hcoef : ∀ m, |P.coeff m| ≤ (A : ℤ))
    (U : Finset (Fin 4 → ℤ)) (hnormal : ∀ v ∈ U, v 3 = 1)
    (hheight : ∀ v ∈ U, ∀ k, |v k| ≤ (H : ℤ)) (hroots : ∀ v ∈ U, eval v P = 0)
    (hgrad : ∀ v ∈ U, ∃ k, eval v (pderiv k P) ≠ 0)
    (D K : ℝ) (hD : 0 < D) (hK : 0 < K)
    (S : Finset ℕ) (hprimes : ∀ p ∈ S, p.Prime) (hlarge : ∀ p ∈ S, K ≤ (p : ℝ))
    (hclass : ∀ p ∈ S, (Fintype.card (P3CanonicalSmoothResidues.Class p P) : ℝ) ≤ D * (p : ℝ) ^ 2)
    (hnumeric : Real.log ((size d e).factorial : ℝ) + (weight d e : ℝ) * Real.log (H : ℝ) <
      P3SmoothGlobalDivisorEstimate.lowerBound d (size d e) A H D K S) :
    ∃ G : MvPolynomial (Fin 4) ℤ, G.IsHomogeneous e ∧
      ¬map (Int.castRingHom ℚ) P ∣ map (Int.castRingHom ℚ) G ∧ ∀ v ∈ U, eval v G = 0 := by
  apply P3GlobalAuxiliaryFromCanonicalDivisors.exists_auxiliary d e H he P hP0 hhom hnot
    U hnormal hheight hroots
  intro f _hf
  let v : Fin (size d e) → Fin 4 → ℤ := fun j ↦ (f j).val
  let L := fun p ↦ P3BudgetedCanonicalDivisor.cutoffs D (size d e) p P
  have hb := P3SmoothGlobalDivisorEstimate.log_divisor_lower_bound D hD S hprimes d A H hd hA hH
    P hhom hcoef v (fun j ↦ hnormal _ (f j).property)
    (fun j k ↦ hheight _ (f j).property k) (fun j ↦ hroots _ (f j).property)
    (fun j ↦ hgrad _ (f j).property) K hK hlarge hclass
  rw [Fintype.card_fin] at hb
  have hh := hnumeric.trans_le hb
  rw [P3CanonicalDivisorLowerBound.log_divisor S hprimes P v] at hh
  refine ⟨S, hprimes, L, ?_⟩
  exact PrimePowerLogSeparation.separation S hprimes
    (fun p ↦ P3CanonicalSurfaceDivisor.exponent p P v (L p)) (size d e) (weight d e) H hH hh

theorem coarse_exists_auxiliary (d e A H : ℕ) (hd : 0 < d) (he : d ≤ e) (hA : 0 < A) (hH : 1 ≤ H)
    (P : MvPolynomial (Fin 4) ℤ) (hP0 : P ≠ 0) (hhom : P.IsHomogeneous d)
    (hnot : ¬X (3 : Fin 4) ∣ map (Int.castRingHom ℚ) P) (hcoef : ∀ m, |P.coeff m| ≤ (A : ℤ))
    (U : Finset (Fin 4 → ℤ)) (hnormal : ∀ v ∈ U, v 3 = 1)
    (hheight : ∀ v ∈ U, ∀ k, |v k| ≤ (H : ℤ)) (hroots : ∀ v ∈ U, eval v P = 0)
    (hgrad : ∀ v ∈ U, ∃ k, eval v (pderiv k P) ≠ 0)
    (K : ℝ) (hK : 0 < K) (S : Finset ℕ) (hprimes : ∀ p ∈ S, p.Prime)
    (hlarge : ∀ p ∈ S, K ≤ (p : ℝ))
    (hnumeric : Real.log ((size d e).factorial : ℝ) + (weight d e : ℝ) * Real.log (H : ℝ) <
      P3SmoothGlobalDivisorEstimate.lowerBound d (size d e) A H d K S) :
    ∃ G : MvPolynomial (Fin 4) ℤ, G.IsHomogeneous e ∧
      ¬map (Int.castRingHom ℚ) P ∣ map (Int.castRingHom ℚ) G ∧ ∀ v ∈ U, eval v G = 0 := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  apply exists_auxiliary d e A H hd he hA hH P hP0 hhom hnot hcoef U hnormal hheight hroots hgrad
    (d : ℝ) K hdR hK S hprimes hlarge ?_ hnumeric
  intro p hp
  exact_mod_cast P3CoarseCanonicalClassCount.cardinality_bound p d (hprimes p hp) P hhom

end PaperP1.P3GlobalAuxiliaryOfPrimeMass
