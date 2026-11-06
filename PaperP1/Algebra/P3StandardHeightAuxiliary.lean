module

public import PaperP1.Algebra.P3StandardMonomialParameters
public import PaperP1.Algebra.PrimeClassHeightAuxiliary

/-! # A coefficient-independent scalar inequality constructs an auxiliary equation on the original smooth classes -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3StandardHeightAuxiliary

open MvPolynomial Finset P3StandardMonomialCount P3StandardMonomialParameters
open scoped Classical

theorem exists_auxiliary (S : Finset ℕ) (hprimes : ∀ p ∈ S, p.Prime) (L d e H : ℕ) (he : d ≤ e)
    (P : MvPolynomial (Fin 4) ℤ) (hP0 : P ≠ 0) (hhom : P.IsHomogeneous d)
    (hnot : ¬ X (3 : Fin 4) ∣ map (Int.castRingHom ℚ) P)
    (a : ℕ → Fin 4 → ℤ) (ha : ∀ p ∈ S, a p 3 = 1)
    (hP : ∀ p ∈ S, (p : ℤ) ∣ eval (a p) P)
    (hgrad : ∀ p ∈ S, ∃ k, ¬(p : ℤ) ∣ eval (a p) (pderiv k P))
    (U : Finset (Fin 4 → ℤ)) (hnormal : ∀ v ∈ U, v 3 = 1)
    (hheight : ∀ v ∈ U, ∀ k, |v k| ≤ (H : ℤ))
    (hcongruent : ∀ p ∈ S, ∀ v ∈ U, ∀ k, (p : ℤ) ∣ v k - a p k)
    (hroots : ∀ v ∈ U, eval v P = 0)
    (hseparation : (size d e).factorial * H ^ weight d e <
      (∏ p ∈ S, p) ^ (L * size d e - (L + 2).choose 3)) :
    ∃ G : MvPolynomial (Fin 4) ℤ, G.IsHomogeneous e ∧
      ¬ map (Int.castRingHom ℚ) P ∣ map (Int.castRingHom ℚ) G ∧ ∀ v ∈ U, eval v G = 0 := by
  let q := map (Int.castRingHom ℚ) P
  let μ := P3HeightLeadingMonomial.order.degree q
  have hq0 : q ≠ 0 := by
    intro hz
    exact hP0 (map_injective (Int.castRingHom ℚ) (Int.cast_injective (α := ℚ))
      (hz.trans (map_zero _).symm))
  have hqhom : q.IsHomogeneous d := hhom.map _
  have hμdeg : μ.degree = d := P3HeightLeadingMonomial.leading_degree d q hqhom hq0
  have hμ3 : μ 3 = 0 := P3HeightLeadingMonomial.leading_normalizer_zero d q hqhom hq0 hnot
  have hme : μ.degree ≤ e := by rw [hμdeg]; exact he
  have hcard : Fintype.card (StandardIndex μ e) = size d e := by rw [size_eq μ e hme, hμdeg]
  have hweight : (∑ r : StandardIndex μ e, NormalizedP3MonomialHeight.freeDegree r.val.val) = weight d e := by
    rw [weight_eq μ e hme hμ3, hμdeg]
  apply PrimeClassHeightAuxiliary.exists_auxiliary (ι := StandardIndex μ e) S hprimes L d e H P hP0 hhom
    a ha hP hgrad P3HeightLeadingMonomial.order (fun r ↦ r.val.val)
    (exponent_injective μ e) (exponent_degree μ e) (exponent_standard μ e)
    U hnormal hheight hcongruent hroots
  simpa only [hcard, hweight] using hseparation

end PaperP1.P3StandardHeightAuxiliary
