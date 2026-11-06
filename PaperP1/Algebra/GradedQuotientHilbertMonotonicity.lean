module

public import PaperP1.Algebra.HomogeneousQuotientGrading
public import PaperP1.Algebra.GradedHilbertPolynomial
public import PaperP1.Algebra.PolynomialEventualCoefficientOrder
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition

/-! # Actual nested quotient pieces give genuine top Hilbert-coefficient inequalities -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GradedQuotientHilbertMonotonicity

variable {F A : Type*} [Field F] [CommRing A] [Algebra F A]
  (H : ℕ → Submodule F A) (I J : Ideal A)

def quotientMap (n : ℕ) : H n →ₗ[F] HomogeneousQuotientGrading.piece H I n where
  toFun a := ⟨Ideal.Quotient.mk I (a : A), Submodule.mem_map.mpr ⟨a, a.property, rfl⟩⟩
  map_add' a b := Subtype.ext (map_add (Ideal.Quotient.mk I) (a : A) (b : A))
  map_smul' r a := Subtype.ext ((Ideal.Quotient.mkₐ F I).toLinearMap.map_smul r (a : A))

theorem quotientMap_surjective (n : ℕ) : Function.Surjective (quotientMap H I n) := by
  rintro ⟨a, ha⟩
  obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.mp ha
  exact ⟨⟨b, hb⟩, rfl⟩

def factor (hle : I ≤ J) (n : ℕ) :
    HomogeneousQuotientGrading.piece H I n →ₗ[F] HomogeneousQuotientGrading.piece H J n where
  toFun a := ⟨Ideal.Quotient.factorₐ F hle a, by
    obtain ⟨b, hb, hba⟩ := Submodule.mem_map.mp a.property
    exact Submodule.mem_map.mpr ⟨b, hb, by
      change Ideal.Quotient.mk J b = Ideal.Quotient.factorₐ F hle a
      rw [← hba]
      rfl⟩⟩
  map_add' a b := Subtype.ext (map_add (Ideal.Quotient.factorₐ F hle) (a : A ⧸ I) (b : A ⧸ I))
  map_smul' r a := Subtype.ext ((Ideal.Quotient.factorₐ F hle).toLinearMap.map_smul r (a : A ⧸ I))

theorem factor_surjective (hle : I ≤ J) (n : ℕ) : Function.Surjective (factor H I J hle n) := by
  rintro ⟨a, ha⟩
  obtain ⟨b, hb, rfl⟩ := Submodule.mem_map.mp ha
  exact ⟨⟨Ideal.Quotient.mk I b, Submodule.mem_map.mpr ⟨b, hb, rfl⟩⟩, rfl⟩

theorem finrank_le (hle : I ≤ J) (n : ℕ) [Module.Finite F (H n)] :
    Module.finrank F (HomogeneousQuotientGrading.piece H J n) ≤
      Module.finrank F (HomogeneousQuotientGrading.piece H I n) := by
  let : Module.Finite F (HomogeneousQuotientGrading.piece H I n) :=
    Module.Finite.of_surjective (quotientMap H I n) (quotientMap_surjective H I n)
  exact LinearMap.finrank_le_finrank_of_surjective (f := factor H I J hle n) (factor_surjective H I J hle n)

theorem coefficient_le [∀ n, Module.Finite F (H n)] (hle : I ≤ J)
    (p q : Polynomial ℚ) (r : ℕ) (hpdeg : p.natDegree ≤ r) (hqdeg : q.natDegree ≤ r)
    (hp : GradedHilbertPolynomial.IsHilbertPolynomial (HomogeneousQuotientGrading.piece H I) p)
    (hq : GradedHilbertPolynomial.IsHilbertPolynomial (HomogeneousQuotientGrading.piece H J) q) :
    q.coeff r ≤ p.coeff r := by
  obtain ⟨N, hN⟩ := hp
  obtain ⟨M, hM⟩ := hq
  apply PolynomialEventualCoefficientOrder.coefficient_le q p r hqdeg hpdeg (max N M)
  intro n hn
  rw [hM n ((le_max_right _ _).trans hn), hN n ((le_max_left _ _).trans hn)]
  exact_mod_cast finrank_le H I J hle n

end PaperP1.GradedQuotientHilbertMonotonicity
