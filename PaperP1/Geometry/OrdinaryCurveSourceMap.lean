module

public import PaperP1.Algebra.WeightedOrdinarySubstitution
public import PaperP1.Algebra.GradedVeroneseMap
public import PaperP1.Algebra.SourceVeroneseGrading
public import PaperP1.Algebra.HomogeneousQuotientGrading
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps

/-! # The actual source curve induced by an ordinary homogeneous radical-curve ideal -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.OrdinaryCurveSourceMap

open MvPolynomial PaperP1.HomogeneousSplitRadicalRelations

attribute [local instance] MvPolynomial.gradedAlgebra

variable {F ι : Type*} [Field F]

local instance weightedRing : CommRing (WeightedPolynomial F ι) := inferInstance

abbrev OrdinaryRing (Q : Ideal (WeightedPolynomial F ι)) := WeightedPolynomial F ι ⧸ Q

local instance ordinaryRing (Q : Ideal (WeightedPolynomial F ι)) : CommRing (OrdinaryRing Q) := inferInstance

def ordinaryPiece (Q : Ideal (WeightedPolynomial F ι)) (n : ℕ) : Submodule F (OrdinaryRing Q) :=
  HomogeneousQuotientGrading.piece (homogeneousSubmodule (Fin 3 ⊕ ι) F) Q n

theorem ordinaryPiece_finite [Finite ι] (Q : Ideal (WeightedPolynomial F ι)) (n : ℕ) :
    Module.Finite F (ordinaryPiece Q n) := by
  let : Module.Finite F (homogeneousSubmodule (Fin 3 ⊕ ι) F n) :=
    Module.Finite.of_fg (homogeneousSubmodule_fg (Fin 3 ⊕ ι) F n)
  exact HomogeneousQuotientGrading.piece_finite (homogeneousSubmodule (Fin 3 ⊕ ι) F) Q n

local instance ordinaryMonoid (Q : Ideal (WeightedPolynomial F ι)) : SetLike.GradedMonoid (ordinaryPiece Q) :=
  HomogeneousQuotientGrading.gradedMonoid (homogeneousSubmodule (Fin 3 ⊕ ι) F) Q

abbrev OrdinaryVeronese (Q : Ideal (WeightedPolynomial F ι)) (D : ℕ) :=
  GradedVeroneseAlgebra.veronese (ordinaryPiece Q) D

variable (c : ι → F) (D : ℕ) (I J : ι → Finset ℤ) (hD : 0 < D)
  (hmin : ∀ i, 2 ≤ (I i).card + (J i).card) (hdeg : ∀ i, (I i).card + (J i).card ≤ 2 * D)
  (Q : Ideal (WeightedPolynomial F ι))
  (hrel : ∀ i, WeightedOrdinarySubstitution.ordinaryRelation (c i) (I i) (J i) i ∈ Q)

include hD hmin hdeg hrel in
theorem relationIdeal_le_kernel : relationIdeal c D I J ≤
    RingHom.ker ((Ideal.Quotient.mkₐ F Q).comp (WeightedOrdinarySubstitution.map D)).toRingHom := by
  apply Ideal.span_le.mpr
  rintro _ ⟨i, rfl⟩
  change Ideal.Quotient.mk Q (WeightedOrdinarySubstitution.map D (relation (c i) D (I i) (J i) i)) = 0
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [WeightedOrdinarySubstitution.map_relation (c i) D (I i) (J i) i hD (hmin i) (hdeg i)]
  exact Q.mul_mem_left _ (hrel i)

def coordinateMap : HomogeneousSplitRadicalGrading.CoordinateRing c D I J →ₐ[F] OrdinaryRing Q :=
  Ideal.Quotient.liftₐ (relationIdeal c D I J)
    ((Ideal.Quotient.mkₐ F Q).comp (WeightedOrdinarySubstitution.map D))
    (fun _ hp ↦ RingHom.mem_ker.mp (relationIdeal_le_kernel c D I J hD hmin hdeg Q hrel hp))

theorem coordinateMap_mk (p : WeightedPolynomial F ι) :
    coordinateMap c D I J hD hmin hdeg Q hrel (Ideal.Quotient.mk _ p) =
      Ideal.Quotient.mk Q (WeightedOrdinarySubstitution.map D p) := rfl

theorem coordinateMap_mem (n : ℕ) (x : HomogeneousSplitRadicalGrading.CoordinateRing c D I J)
    (hx : x ∈ HomogeneousSplitRadicalGrading.piece c D I J n) :
    coordinateMap c D I J hD hmin hdeg Q hrel x ∈ ordinaryPiece Q n := by
  obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hx
  exact Submodule.mem_map.mpr ⟨WeightedOrdinarySubstitution.map D p,
    WeightedOrdinarySubstitution.map_homogeneous D hD n p hp, rfl⟩

variable (hQ : Q.IsHomogeneous (homogeneousSubmodule (Fin 3 ⊕ ι) F))

def gradedCoordinateMap : HomogeneousSplitRadicalGrading.piece c D I J →+*ᵍ ordinaryPiece Q where
  __ := (coordinateMap c D I J hD hmin hdeg Q hrel).toRingHom
  map_mem := by intro n x hx; exact coordinateMap_mem c D I J hD hmin hdeg Q hrel n x hx

def veroneseMap : HomogeneousSplitRadicalVeronese.veronese c D I J →ₐ[F] OrdinaryVeronese Q D := by
  let := HomogeneousSplitRadicalGrading.grading c D I J hdeg
  let : GradedAlgebra (ordinaryPiece Q) :=
    HomogeneousQuotientGrading.grading (homogeneousSubmodule (Fin 3 ⊕ ι) F) Q hQ
  exact GradedVeroneseMap.map (HomogeneousSplitRadicalGrading.piece c D I J) (ordinaryPiece Q)
    (gradedCoordinateMap c D I J hD hmin hdeg Q hrel)
    (coordinateMap c D I J hD hmin hdeg Q hrel).commutes D

theorem veroneseMap_val (x : HomogeneousSplitRadicalVeronese.veronese c D I J) :
    (veroneseMap c D I J hD hmin hdeg Q hrel hQ x : OrdinaryRing Q) =
      coordinateMap c D I J hD hmin hdeg Q hrel x.val := rfl

def sourceIdeal : Ideal (HomogeneousSplitRadicalVeronese.veronese c D I J) :=
  RingHom.ker (veroneseMap c D I J hD hmin hdeg Q hrel hQ).toRingHom

include hQ in
theorem sourceIdeal_homogeneous :
    letI := SourceVeroneseGrading.sourceGrading c D I J hdeg hD
    (sourceIdeal c D I J hD hmin hdeg Q hrel hQ).IsHomogeneous (SourceVeroneseGrading.sourcePiece c D I J) := by
  let := HomogeneousSplitRadicalGrading.grading c D I J hdeg
  let : GradedAlgebra (ordinaryPiece Q) :=
    HomogeneousQuotientGrading.grading (homogeneousSubmodule (Fin 3 ⊕ ι) F) Q hQ
  let := GradedVeroneseGrading.grading (HomogeneousSplitRadicalGrading.piece c D I J) D hD
  let := GradedVeroneseGrading.grading (ordinaryPiece Q) D hD
  have h := ((⊥ : HomogeneousIdeal (GradedVeroneseGrading.piece (ordinaryPiece Q) D)).comap
    (GradedVeroneseMap.gradedMap (HomogeneousSplitRadicalGrading.piece c D I J) (ordinaryPiece Q)
      (gradedCoordinateMap c D I J hD hmin hdeg Q hrel)
      (coordinateMap c D I J hD hmin hdeg Q hrel).commutes D)).isHomogeneous
  let := SourceVeroneseGrading.sourceGrading c D I J hdeg hD
  change (sourceIdeal c D I J hD hmin hdeg Q hrel hQ).IsHomogeneous
    (SourceVeroneseGrading.sourcePiece c D I J) at h
  exact h

theorem sourceIdeal_prime [Q.IsPrime] : (sourceIdeal c D I J hD hmin hdeg Q hrel hQ).IsPrime :=
  RingHom.ker_isPrime _

abbrev SourceRing := HomogeneousSplitRadicalVeronese.veronese c D I J ⧸
  sourceIdeal c D I J hD hmin hdeg Q hrel hQ

local instance sourceRing : CommRing (SourceRing c D I J hD hmin hdeg Q hrel hQ) := inferInstance

def curveMap : SourceRing c D I J hD hmin hdeg Q hrel hQ →ₐ[F] OrdinaryRing Q :=
  (OrdinaryVeronese Q D).val.comp (Ideal.kerLiftAlg (veroneseMap c D I J hD hmin hdeg Q hrel hQ))

theorem curveMap_injective : Function.Injective (curveMap c D I J hD hmin hdeg Q hrel hQ) :=
  by
    intro x y hxy
    apply Ideal.kerLiftAlg_injective (veroneseMap c D I J hD hmin hdeg Q hrel hQ)
    exact Subtype.ext hxy

theorem curveMap_mk (x : HomogeneousSplitRadicalVeronese.veronese c D I J) :
    curveMap c D I J hD hmin hdeg Q hrel hQ (Ideal.Quotient.mk _ x) =
      coordinateMap c D I J hD hmin hdeg Q hrel x.val := rfl

def sourcePiece (n : ℕ) : Submodule F (SourceRing c D I J hD hmin hdeg Q hrel hQ) :=
  HomogeneousQuotientGrading.piece (SourceVeroneseGrading.sourcePiece c D I J)
    (sourceIdeal c D I J hD hmin hdeg Q hrel hQ) n

theorem curveMap_mem (n : ℕ) (x : SourceRing c D I J hD hmin hdeg Q hrel hQ)
    (hx : x ∈ sourcePiece c D I J hD hmin hdeg Q hrel hQ n) :
    curveMap c D I J hD hmin hdeg Q hrel hQ x ∈ ordinaryPiece Q (n * D) := by
  obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
  exact coordinateMap_mem c D I J hD hmin hdeg Q hrel (n * D) y.val hy

end PaperP1.OrdinaryCurveSourceMap
