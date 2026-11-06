module

public import PaperP1.Algebra.SourceSurfaceScalarExtensionDomain
public import PaperP1.Geometry.LinearHypersurfaceImage
public import Mathlib.RingTheory.Ideal.Maximal

/-! # The actual principal hypersurface image of the source remains irreducible over every field extension -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SourceSurfaceGeometricImage

open scoped TensorProduct
open MvPolynomial LinearHypersurfaceImage

theorem irreducible_after_extension {F E A : Type*} [Field F] [Field E] [Algebra F E]
    [CommRing A] [Algebra F A] [IsDomain (E ⊗[F] A)] {m : ℕ}
    (g : Fin m → A) (y : A) (q : MvPolynomial (Fin (m + 1)) F)
    (hq : ideal (F := F) g y = Ideal.span {q}) (hq0 : q ≠ 0) :
    Irreducible (map (algebraMap F E) q) := by
  let B := CoordinateRing (F := F) g y
  let : IsDomain (E ⊗[F] B) := ScalarExtensionInjectiveAlgebraMap.isDomain
    (toSource (F := F) g y) (toSource_injective g y)
  let e := PolynomialQuotientScalarExtension.equiv (E := E) (ideal (F := F) g y)
  have hdomain : IsDomain (MvPolynomial (Fin (m + 1)) E ⧸
      (ideal (F := F) g y).map (map (algebraMap F E))) :=
    e.symm.injective.isDomain e.symm.toRingHom
  have hmap : (ideal (F := F) g y).map (map (algebraMap F E)) =
      Ideal.span {map (algebraMap F E) q} := by
    rw [hq, Ideal.map_span, Set.image_singleton]
  rw [hmap] at hdomain
  have hprime : (Ideal.span {map (algebraMap F E) q}).IsPrime :=
    (Ideal.Quotient.isDomain_iff_prime _).mp hdomain
  have hnonzero : map (algebraMap F E) q ≠ 0 :=
    (map_ne_zero_iff (map (algebraMap F E)) (map_injective _ (algebraMap F E).injective)).mpr hq0
  exact ((Ideal.span_singleton_prime hnonzero).mp hprime).irreducible

theorem source_irreducible_after_extension {F E : Type*} [Field F] [CharZero F] [Field E] [Algebra F E]
    (k D : ℕ) (c : Fin k → F) (I J : Fin k → Finset ℤ)
    (hc : ∀ i, c i ≠ 0) (hne : ∀ i, (I i).Nonempty ∨ (J i).Nonempty)
    (hI : Pairwise fun i j ↦ Disjoint (I i) (I j))
    (hJ : Pairwise fun i j ↦ Disjoint (J i) (J j)) {m : ℕ}
    (g : Fin m → HomogeneousSplitRadicalVeronese.veronese c D I J)
    (y : HomogeneousSplitRadicalVeronese.veronese c D I J)
    (q : MvPolynomial (Fin (m + 1)) F)
    (hq : ideal (F := F) g y = Ideal.span {q}) (hq0 : q ≠ 0) :
    Irreducible (map (algebraMap F E) q) := by
  let := SourceSurfaceScalarExtensionDomain.veronese_isDomain (E := E) k D c I J hc hne hI hJ
  exact irreducible_after_extension g y q hq hq0

end PaperP1.SourceSurfaceGeometricImage
