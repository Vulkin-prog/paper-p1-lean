module

public import PaperP1.Algebra.StandardMonomialAuxiliary
public import PaperP1.Algebra.MultiPrimeSurfaceDeterminant

/-! # Actual smooth prime classes and an integer size separation construct an independent auxiliary equation -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrimeClassStandardMonomialAuxiliary

open MvPolynomial Finset Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem exists_auxiliary (S : Finset ℕ) (hprimes : ∀ p ∈ S, p.Prime) (L d e : ℕ)
    (P : MvPolynomial (Fin 4) ℤ) (hP0 : P ≠ 0) (hhom : P.IsHomogeneous d)
    (a : ℕ → Fin 4 → ℤ) (ha : ∀ p ∈ S, a p 3 = 1)
    (hP : ∀ p ∈ S, (p : ℤ) ∣ eval (a p) P)
    (hgrad : ∀ p ∈ S, ∃ k, ¬(p : ℤ) ∣ eval (a p) (pderiv k P))
    (o : MonomialOrder (Fin 4)) (m : ι → Fin 4 →₀ ℕ) (hm : Function.Injective m)
    (hdegree : ∀ i, (m i).degree = e)
    (hstandard : ∀ i, ¬ o.degree (map (Int.castRingHom ℚ) P) ≤ m i)
    (U : Finset (Fin 4 → ℤ)) (hnormal : ∀ v ∈ U, v 3 = 1)
    (hcongruent : ∀ p ∈ S, ∀ v ∈ U, ∀ k, (p : ℤ) ∣ v k - a p k)
    (hroots : ∀ v ∈ U, eval v P = 0)
    (hsmall : ∀ f : ι → U, Function.Injective f →
      (Matrix.det (fun i j ↦ (m i).prod (fun k r ↦ (f j).val k ^ r))).natAbs <
        (∏ p ∈ S, p) ^ (L * Fintype.card ι - (L + 2).choose 3)) :
    ∃ G : MvPolynomial (Fin 4) ℤ, G.IsHomogeneous e ∧
      ¬ map (Int.castRingHom ℚ) P ∣ map (Int.castRingHom ℚ) G ∧ ∀ v ∈ U, eval v G = 0 := by
  classical
  have hq0 : map (Int.castRingHom ℚ) P ≠ 0 := by
    intro hz
    exact hP0 (map_injective (Int.castRingHom ℚ) (Int.cast_injective (α := ℚ))
      (hz.trans (map_zero _).symm))
  apply StandardMonomialAuxiliary.exists_of_minors_zero o (map (Int.castRingHom ℚ) P) hq0
    e m hm hdegree hstandard U
  intro f hf
  let A : Matrix ι ι ℤ := fun i j ↦ (m i).prod (fun k r ↦ (f j).val k ^ r)
  have hdiv : ((∏ p ∈ S, p : ℕ) : ℤ) ^ (L * Fintype.card ι - (L + 2).choose 3) ∣ A.det := by
    have hd := MultiPrimeSurfaceDeterminant.integer_dvd S hprimes L d P hhom a ha hP hgrad
      (fun j ↦ (f j).val) (fun j ↦ hnormal _ (f j).property)
      (fun p hp j k ↦ hcongruent p hp _ (f j).property k)
      (fun j ↦ hroots _ (f j).property) (fun i ↦ monomial (m i) 1)
    simpa only [eval_monomial, one_mul] using hd
  have hzero : A.det = 0 := MultiPrimeSurfaceDeterminant.det_zero_of_small S L A hdiv (hsmall f hf)
  change A.transpose.det = 0
  rw [Matrix.det_transpose]
  exact hzero

end PaperP1.PrimeClassStandardMonomialAuxiliary
