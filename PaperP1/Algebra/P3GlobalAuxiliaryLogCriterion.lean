module

public import PaperP1.Algebra.P3GlobalAuxiliaryFromCanonicalDivisors
public import PaperP1.Analysis.P3CanonicalDivisorLowerBound

/-! # An explicit weighted canonical-population inequality constructs the global auxiliary equation -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3GlobalAuxiliaryLogCriterion

open MvPolynomial Finset P3StandardMonomialParameters

theorem exists_auxiliary (d e H : ℕ) (he : d ≤ e) (hH : 1 ≤ H)
    (P : MvPolynomial (Fin 4) ℤ) (hP0 : P ≠ 0) (hhom : P.IsHomogeneous d)
    (hnot : ¬X (3 : Fin 4) ∣ map (Int.castRingHom ℚ) P)
    (U : Finset (Fin 4 → ℤ)) (hnormal : ∀ v ∈ U, v 3 = 1)
    (hheight : ∀ v ∈ U, ∀ k, |v k| ≤ (H : ℤ)) (hroots : ∀ v ∈ U, eval v P = 0)
    (hseparation : ∀ f : Fin (size d e) → U, Function.Injective f →
      ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime) ∧
        Real.log ((size d e).factorial : ℝ) + (weight d e : ℝ) * Real.log (H : ℝ) <
          ∑ p ∈ S, P3CanonicalDivisorLowerBound.lowerBound p P (fun j ↦ (f j).val) * Real.log (p : ℝ)) :
    ∃ G : MvPolynomial (Fin 4) ℤ, G.IsHomogeneous e ∧
      ¬map (Int.castRingHom ℚ) P ∣ map (Int.castRingHom ℚ) G ∧ ∀ v ∈ U, eval v G = 0 := by
  apply P3GlobalAuxiliaryFromCanonicalDivisors.exists_auxiliary d e H he P hP0 hhom hnot
    U hnormal hheight hroots
  intro f hf
  obtain ⟨S, hprimes, hlog⟩ := hseparation f hf
  let v := fun j ↦ (f j).val
  let L := fun p ↦ P3CanonicalDivisorLowerBound.commonCutoff p P v
  have hb := P3CanonicalDivisorLowerBound.log_divisor_lower_bound S hprimes P v
  rw [P3CanonicalDivisorLowerBound.log_divisor S hprimes P v] at hb
  refine ⟨S, hprimes, L, ?_⟩
  exact PrimePowerLogSeparation.separation S hprimes
    (fun p ↦ P3CanonicalSurfaceDivisor.exponent p P v (L p)) (size d e) (weight d e) H hH
    (hlog.trans_le hb)

end PaperP1.P3GlobalAuxiliaryLogCriterion
