module

public import PaperP1.Algebra.HomogeneousSplitRadicalIndexEquiv
public import PaperP1.Algebra.HomogeneousSplitRadicalScalarRelations
public import PaperP1.Algebra.PolynomialQuotientScalarExtension
public import PaperP1.Algebra.ScalarExtensionInjectiveAlgebraMap
public import PaperP1.Algebra.HomogeneousSplitRadicalVeronese

/-! # The actual weighted source and its chosen Veronese algebra remain domains over every field extension -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SourceSurfaceScalarExtensionDomain

open scoped TensorProduct
open HomogeneousSplitRadicalRelations HomogeneousSplitRadicalGrading

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

def equiv (k D : ℕ) (c : Fin k → F) (I J : Fin k → Finset ℤ) :
    E ⊗[F] CoordinateRing c D I J ≃ₐ[E]
      CoordinateRing (fun i ↦ algebraMap F E (c i)) D I J := by
  have hh := PolynomialQuotientScalarExtension.equiv (E := E) (relationIdeal c D I J)
  have hmap := HomogeneousSplitRadicalScalarRelations.ideal_map (algebraMap F E) c D I J
  rw [hmap] at hh
  exact hh

theorem weighted_isDomain [CharZero F] (k D : ℕ) (c : Fin k → F) (I J : Fin k → Finset ℤ)
    (hc : ∀ i, c i ≠ 0) (hne : ∀ i, (I i).Nonempty ∨ (J i).Nonempty)
    (hI : Pairwise fun i j ↦ Disjoint (I i) (I j))
    (hJ : Pairwise fun i j ↦ Disjoint (J i) (J j)) :
    IsDomain (E ⊗[F] CoordinateRing c D I J) := by
  let : CharZero E := Algebra.charZero_of_charZero F E
  let := HomogeneousSplitRadicalIndexEquiv.domain_fin k D (fun i ↦ algebraMap F E (c i)) I J
    (fun i ↦ (map_ne_zero_iff (algebraMap F E) (algebraMap F E).injective).mpr (hc i)) hne hI hJ
  exact (equiv (E := E) k D c I J).injective.isDomain (equiv (E := E) k D c I J).toRingHom

theorem veronese_isDomain [CharZero F] (k D : ℕ) (c : Fin k → F) (I J : Fin k → Finset ℤ)
    (hc : ∀ i, c i ≠ 0) (hne : ∀ i, (I i).Nonempty ∨ (J i).Nonempty)
    (hI : Pairwise fun i j ↦ Disjoint (I i) (I j))
    (hJ : Pairwise fun i j ↦ Disjoint (J i) (J j)) :
    IsDomain (E ⊗[F] HomogeneousSplitRadicalVeronese.veronese c D I J) := by
  let := weighted_isDomain (E := E) k D c I J hc hne hI hJ
  exact ScalarExtensionInjectiveAlgebraMap.isDomain
    (HomogeneousSplitRadicalVeronese.veronese c D I J).val Subtype.val_injective

end PaperP1.SourceSurfaceScalarExtensionDomain
