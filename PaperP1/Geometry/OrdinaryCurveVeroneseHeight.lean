module

public import PaperP1.Algebra.GradedVeroneseChartPrimeHeight
public import PaperP1.Geometry.OrdinarySurfaceCurveData

/-! # The actual ordinary curve height is independent of every positive auxiliary Veronese degree -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OrdinaryCurveVeroneseHeight

open MvPolynomial HomogeneousSplitRadicalRelations WeightedOrdinaryAffineIdeal OrdinaryCurveSourceMap

attribute [local instance] MvPolynomial.gradedAlgebra

variable {F ι : Type*} [Field F] (c : ι → F) (I J : ι → Finset ℤ)
  (Q : Ideal (WeightedPolynomial F ι))
  (hrel : ∀ i, WeightedOrdinarySubstitution.ordinaryRelation (c i) (I i) (J i) i ∈ Q)

def surfacePrime : Ideal (OrdinaryRing (ordinaryIdeal c I J)) :=
  RingHom.ker (OrdinaryCurveSourceHeight.factor c I J Q hrel)

def gradedFactor : ordinaryPiece (ordinaryIdeal c I J) →+*ᵍ ordinaryPiece Q where
  __ := (OrdinaryCurveSourceHeight.factor c I J Q hrel).toRingHom
  map_mem hx := by
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hx
    exact Submodule.mem_map.mpr ⟨p, hp, rfl⟩

theorem surfacePrime_prime [Q.IsPrime] : (surfacePrime c I J Q hrel).IsPrime := RingHom.ker_isPrime _

theorem surfacePrime_homogeneous (hmin : ∀ i, 2 ≤ (I i).card + (J i).card)
    (hQ : Q.IsHomogeneous (homogeneousSubmodule (Fin 3 ⊕ ι) F)) :
    letI := OrdinaryRadicalSurface.grading c I J hmin
    (surfacePrime c I J Q hrel).IsHomogeneous (ordinaryPiece (ordinaryIdeal c I J)) := by
  let := OrdinaryRadicalSurface.grading c I J hmin
  let : GradedAlgebra (ordinaryPiece Q) :=
    HomogeneousQuotientGrading.grading (homogeneousSubmodule (Fin 3 ⊕ ι) F) Q hQ
  exact (HomogeneousIdeal.comap (gradedFactor c I J Q hrel) (⊥ : HomogeneousIdeal (ordinaryPiece Q))).isHomogeneous

theorem surfacePrime_chart_not_mem (hZ : X (Sum.inl (2 : Fin 3)) ∉ Q) :
    Ideal.Quotient.mk (ordinaryIdeal c I J) (X (Sum.inl (2 : Fin 3))) ∉ surfacePrime c I J Q hrel := by
  intro hh
  change Ideal.Quotient.mk Q (X (Sum.inl (2 : Fin 3))) = 0 at hh
  exact hZ (Ideal.Quotient.eq_zero_iff_mem.mp hh)

theorem surfaceIdeal_eq (D : ℕ) : OrdinaryCurveSourceHeight.surfaceIdeal c D I J Q hrel =
    (surfacePrime c I J Q hrel).comap (OrdinaryVeronese (ordinaryIdeal c I J) D).val.toRingHom := by
  ext x
  rfl

theorem height_eq (hmin : ∀ i, 2 ≤ (I i).card + (J i).card)
    (hQ : Q.IsHomogeneous (homogeneousSubmodule (Fin 3 ⊕ ι) F)) [Q.IsPrime]
    (hZ : X (Sum.inl (2 : Fin 3)) ∉ Q) (D : ℕ) (hD : 0 < D) :
    (surfacePrime c I J Q hrel).height = (OrdinaryCurveSourceHeight.surfaceIdeal c D I J Q hrel).height := by
  let := OrdinaryRadicalSurface.grading c I J hmin
  let : (surfacePrime c I J Q hrel).IsPrime := surfacePrime_prime c I J Q hrel
  have hz : Ideal.Quotient.mk (ordinaryIdeal c I J) (X (Sum.inl (2 : Fin 3))) ∈
      ordinaryPiece (ordinaryIdeal c I J) 1 := Submodule.mem_map.mpr ⟨_, isHomogeneous_X F _, rfl⟩
  rw [surfaceIdeal_eq c I J Q hrel D]
  exact GradedVeroneseChartPrimeHeight.height_eq (ordinaryPiece (ordinaryIdeal c I J)) D hD hz
    (surfacePrime c I J Q hrel) (surfacePrime_homogeneous c I J Q hrel hmin hQ)
    (surfacePrime_chart_not_mem c I J Q hrel hZ)

theorem height_independent (hmin : ∀ i, 2 ≤ (I i).card + (J i).card)
    (hQ : Q.IsHomogeneous (homogeneousSubmodule (Fin 3 ⊕ ι) F)) [Q.IsPrime]
    (hZ : X (Sum.inl (2 : Fin 3)) ∉ Q) (D E : ℕ) (hD : 0 < D) (hE : 0 < E) :
    (OrdinaryCurveSourceHeight.surfaceIdeal c D I J Q hrel).height =
      (OrdinaryCurveSourceHeight.surfaceIdeal c E I J Q hrel).height :=
  (height_eq c I J Q hrel hmin hQ hZ D hD).symm.trans (height_eq c I J Q hrel hmin hQ hZ E hE)

end PaperP1.OrdinaryCurveVeroneseHeight
