module

public import PaperP1.Arithmetic.P3CanonicalSurfaceDivisor
public import PaperP1.Algebra.P3StandardMonomialParameters
public import PaperP1.Algebra.StandardMonomialAuxiliary

/-! # Canonical mixed-prime divisors and a literal scalar comparison construct an actual global auxiliary polynomial -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.P3GlobalAuxiliaryFromCanonicalDivisors

open MvPolynomial Finset P3StandardMonomialCount P3StandardMonomialParameters
open scoped Classical

theorem exists_auxiliary (d e H : ℕ) (he : d ≤ e) (P : MvPolynomial (Fin 4) ℤ)
    (hP0 : P ≠ 0) (hhom : P.IsHomogeneous d) (hnot : ¬X (3 : Fin 4) ∣ map (Int.castRingHom ℚ) P)
    (U : Finset (Fin 4 → ℤ)) (hnormal : ∀ v ∈ U, v 3 = 1)
    (hheight : ∀ v ∈ U, ∀ k, |v k| ≤ (H : ℤ)) (hroots : ∀ v ∈ U, eval v P = 0)
    (hseparation : ∀ f : Fin (size d e) → U, Function.Injective f →
      ∃ S : Finset ℕ, (∀ p ∈ S, p.Prime) ∧
      ∃ L : ∀ p, P3CanonicalSmoothResidues.Class p P → ℕ,
        (size d e).factorial * H ^ weight d e <
          P3CanonicalSurfaceDivisor.divisor S P (fun j ↦ (f j).val) L) :
    ∃ G : MvPolynomial (Fin 4) ℤ, G.IsHomogeneous e ∧
      ¬map (Int.castRingHom ℚ) P ∣ map (Int.castRingHom ℚ) G ∧ ∀ v ∈ U, eval v G = 0 := by
  let q := map (Int.castRingHom ℚ) P
  let μ := P3HeightLeadingMonomial.order.degree q
  have hq0 : q ≠ 0 := by
    intro hz
    exact hP0 (map_injective (Int.castRingHom ℚ) (Int.cast_injective (α := ℚ))
      (hz.trans (map_zero _).symm))
  have hμdeg : μ.degree = d := P3HeightLeadingMonomial.leading_degree d q (hhom.map _) hq0
  have hμ3 : μ 3 = 0 := P3HeightLeadingMonomial.leading_normalizer_zero d q (hhom.map _) hq0 hnot
  have hme : μ.degree ≤ e := by rw [hμdeg]; exact he
  have hcard : Fintype.card (StandardIndex μ e) = size d e := by rw [size_eq μ e hme, hμdeg]
  let η : StandardIndex μ e ≃ Fin (size d e) := Fintype.equivFinOfCardEq hcard
  let m : Fin (size d e) → Fin 4 →₀ ℕ := fun i ↦ (η.symm i).val.val
  have hm : Function.Injective m := (exponent_injective μ e).comp η.symm.injective
  have hdegree : ∀ i, (m i).degree = e := fun i ↦ exponent_degree μ e (η.symm i)
  have hstandard : ∀ i, ¬P3HeightLeadingMonomial.order.degree q ≤ m i :=
    fun i ↦ exponent_standard μ e (η.symm i)
  have hweight : (∑ i, NormalizedP3MonomialHeight.freeDegree (m i)) = weight d e := by
    change (∑ i, NormalizedP3MonomialHeight.freeDegree (η.symm i).val.val) = _
    rw [Equiv.sum_comp η.symm (fun r ↦ NormalizedP3MonomialHeight.freeDegree r.val.val),
      weight_eq μ e hme hμ3, hμdeg]
  apply StandardMonomialAuxiliary.exists_of_minors_zero P3HeightLeadingMonomial.order q hq0
    e m hm hdegree hstandard U
  intro f hf
  obtain ⟨S, hprimes, L, hsep⟩ := hseparation f hf
  have hb := NormalizedP3MonomialHeight.determinant_bound m (fun j ↦ (f j).val) H
    (fun j ↦ hnormal _ (f j).property) (fun j k ↦ hheight _ (f j).property k)
  rw [Fintype.card_fin, hweight] at hb
  have hsmall : (Matrix.det (fun i j ↦ eval (f j).val (monomial (m i) (1 : ℤ)))).natAbs <
      P3CanonicalSurfaceDivisor.divisor S P (fun j ↦ (f j).val) L := by
    simpa only [eval_monomial, one_mul] using hb.trans_lt hsep
  have hz := P3CanonicalSurfaceDivisor.det_zero_of_small S hprimes d P hhom
    (fun j ↦ (f j).val) (fun j ↦ hnormal _ (f j).property)
    (fun j ↦ hroots _ (f j).property) L (fun i ↦ monomial (m i) (1 : ℤ)) hsmall
  let A : Matrix (Fin (size d e)) (Fin (size d e)) ℤ :=
    fun i j ↦ (m i).prod (fun k r ↦ (f j).val k ^ r)
  have hzA : A.det = 0 := by simpa only [eval_monomial, one_mul] using hz
  change A.transpose.det = 0
  rw [Matrix.det_transpose]
  exact hzA

end PaperP1.P3GlobalAuxiliaryFromCanonicalDivisors
