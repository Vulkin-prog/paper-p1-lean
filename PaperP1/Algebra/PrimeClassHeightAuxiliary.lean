module

public import PaperP1.Algebra.PrimeClassStandardMonomialAuxiliary
public import PaperP1.Algebra.NormalizedP3MonomialHeight

/-! # A literal row-height/product-divisor inequality constructs the actual independent surface auxiliary equation -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimeClassHeightAuxiliary

open MvPolynomial Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_auxiliary (S : Finset ℕ) (hprimes : ∀ p ∈ S, p.Prime) (L d e H : ℕ)
    (P : MvPolynomial (Fin 4) ℤ) (hP0 : P ≠ 0) (hhom : P.IsHomogeneous d)
    (a : ℕ → Fin 4 → ℤ) (ha : ∀ p ∈ S, a p 3 = 1)
    (hP : ∀ p ∈ S, (p : ℤ) ∣ eval (a p) P)
    (hgrad : ∀ p ∈ S, ∃ k, ¬(p : ℤ) ∣ eval (a p) (pderiv k P))
    (o : MonomialOrder (Fin 4)) (m : ι → Fin 4 →₀ ℕ) (hm : Function.Injective m)
    (hdegree : ∀ i, (m i).degree = e)
    (hstandard : ∀ i, ¬ o.degree (map (Int.castRingHom ℚ) P) ≤ m i)
    (U : Finset (Fin 4 → ℤ)) (hnormal : ∀ v ∈ U, v 3 = 1)
    (hheight : ∀ v ∈ U, ∀ k, |v k| ≤ (H : ℤ))
    (hcongruent : ∀ p ∈ S, ∀ v ∈ U, ∀ k, (p : ℤ) ∣ v k - a p k)
    (hroots : ∀ v ∈ U, eval v P = 0)
    (hseparation : (Fintype.card ι).factorial * H ^ (∑ i, NormalizedP3MonomialHeight.freeDegree (m i)) <
      (∏ p ∈ S, p) ^ (L * Fintype.card ι - (L + 2).choose 3)) :
    ∃ G : MvPolynomial (Fin 4) ℤ, G.IsHomogeneous e ∧
      ¬ map (Int.castRingHom ℚ) P ∣ map (Int.castRingHom ℚ) G ∧ ∀ v ∈ U, eval v G = 0 := by
  apply PrimeClassStandardMonomialAuxiliary.exists_auxiliary S hprimes L d e P hP0 hhom
    a ha hP hgrad o m hm hdegree hstandard U hnormal hcongruent hroots
  intro f _hf
  have hb := NormalizedP3MonomialHeight.determinant_bound m (fun j ↦ (f j).val) H
    (fun j ↦ hnormal _ (f j).property) (fun j k ↦ hheight _ (f j).property k)
  exact hb.trans_lt hseparation

end PaperP1.PrimeClassHeightAuxiliary
