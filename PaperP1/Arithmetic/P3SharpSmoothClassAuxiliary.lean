module

public import PaperP1.Analysis.P3OptimizedSurfaceDivisor
public import PaperP1.Analysis.FactorialHeightDivisorSeparation
public import PaperP1.Algebra.P3StandardHeightAuxiliary

/-! # The sharp product-modulus scale constructs one uniform bounded-degree auxiliary equation in each smooth class -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3SharpSmoothClassAuxiliary

open MvPolynomial Finset P3StandardMonomialParameters P3SurfaceDivisorLimits

theorem uniform_degree (d : ℕ) (hd : 0 < d) (ε : ℝ) (hε : 0 < ε) :
    ∃ (e : ℕ) (B : ℝ), d ≤ e ∧ 0 < B ∧
      ∀ (S : Finset ℕ), (∀ p ∈ S, p.Prime) → ∀ H : ℕ, 1 ≤ H →
        B * (H : ℝ) ^ (1 / Real.sqrt (d : ℝ) + ε) ≤ ((∏ p ∈ S, p : ℕ) : ℝ) →
      ∀ (P : MvPolynomial (Fin 4) ℤ), P ≠ 0 → P.IsHomogeneous d →
        ¬ X (3 : Fin 4) ∣ map (Int.castRingHom ℚ) P →
      ∀ (a : ℕ → Fin 4 → ℤ), (∀ p ∈ S, a p 3 = 1) →
        (∀ p ∈ S, (p : ℤ) ∣ eval (a p) P) →
        (∀ p ∈ S, ∃ k, ¬(p : ℤ) ∣ eval (a p) (pderiv k P)) →
      ∀ U : Finset (Fin 4 → ℤ), (∀ v ∈ U, v 3 = 1) →
        (∀ v ∈ U, ∀ k, |v k| ≤ (H : ℤ)) →
        (∀ p ∈ S, ∀ v ∈ U, ∀ k, (p : ℤ) ∣ v k - a p k) →
        (∀ v ∈ U, eval v P = 0) →
      ∃ G : MvPolynomial (Fin 4) ℤ, G.IsHomogeneous e ∧
        ¬ map (Int.castRingHom ℚ) P ∣ map (Int.castRingHom ℚ) G ∧ ∀ v ∈ U, eval v G = 0 := by
  obtain ⟨e, he, hE, hW⟩ := P3OptimizedSurfaceDivisor.exists_parameters d hd ε hε
  let B : ℝ := ((size d e).factorial + 1 : ℕ)
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨e, B, he, hB, ?_⟩
  intro S hprimes H hH hQ P hP0 hhom hnot a ha hP hgrad U hnormal hheight hcongruent hroots
  have hseparation := FactorialHeightDivisorSeparation.separation (size d e) (weight d e)
    (divisor d e) H (∏ p ∈ S, p) hE hH (1 / Real.sqrt (d : ℝ) + ε) hW.le hQ
  apply P3StandardHeightAuxiliary.exists_auxiliary S hprimes (cutoff d e) d e H he P hP0 hhom hnot
    a ha hP hgrad U hnormal hheight hcongruent hroots
  exact hseparation

end PaperP1.P3SharpSmoothClassAuxiliary
