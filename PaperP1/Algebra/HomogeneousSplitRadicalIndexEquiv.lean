module

public import PaperP1.Algebra.HomogeneousSplitRadicalPresentation
public import PaperP1.Algebra.HomogeneousSplitRadicalGrading
public import Mathlib.Order.Fin.Basic

/-! # Actual weighted radical coordinate quotients are compatible with reindexing their radicals -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HomogeneousSplitRadicalIndexEquiv

open MvPolynomial HomogeneousSplitRadicalRelations HomogeneousSplitRadicalGrading
  HomogeneousSplitRadicalData

variable {F ι κ : Type*} [Field F]

def polynomialEquiv (F : Type*) [Field F] (e : ι ≃ κ) :
    WeightedPolynomial F ι ≃ₐ[F] WeightedPolynomial F κ :=
  renameEquiv F (Equiv.sumCongr (Equiv.refl (Fin 3)) e)

theorem base_map (e : ι ≃ κ) (P : MvPolynomial (Fin 3) F) :
    polynomialEquiv F e (rename Sum.inl P) = rename Sum.inl P := by
  change rename (Equiv.sumCongr (Equiv.refl (Fin 3)) e) (rename Sum.inl P) = _
  rw [rename_rename]
  rfl

theorem relation_map (e : ι ≃ κ) (c : ι → F) (D : ℕ) (I J : ι → Finset ℤ) (i : ι) :
    polynomialEquiv F e (relation (c i) D (I i) (J i) i) =
      relation (c (e.symm (e i))) D (I (e.symm (e i))) (J (e.symm (e i))) (e i) := by
  simp only [e.symm_apply_apply]
  change rename (Equiv.sumCongr (Equiv.refl (Fin 3)) e)
      (X (Sum.inr i) ^ 2 - rename Sum.inl
        (HomogeneousSplitRadicalPolynomials.nativeRadicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i))) =
    X (Sum.inr (e i)) ^ 2 - rename Sum.inl
      (HomogeneousSplitRadicalPolynomials.nativeRadicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i))
  rw [map_sub, map_pow, rename_X, rename_rename]
  rfl

theorem ideal_map (e : ι ≃ κ) (c : ι → F) (D : ℕ) (I J : ι → Finset ℤ) :
    (relationIdeal c D I J).map (polynomialEquiv F e).toRingHom =
      relationIdeal (fun j ↦ c (e.symm j)) D (fun j ↦ I (e.symm j)) (fun j ↦ J (e.symm j)) := by
  rw [relationIdeal, Ideal.map_span, ← Set.range_comp']
  apply congrArg Ideal.span
  ext P
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨e i, (relation_map e c D I J i).symm⟩
  · rintro ⟨j, rfl⟩
    refine ⟨e.symm j, ?_⟩
    change polynomialEquiv F e (relation (c (e.symm j)) D (I (e.symm j)) (J (e.symm j)) (e.symm j)) = _
    rw [relation_map]
    simp only [e.apply_symm_apply]

def coordinateEquiv (e : ι ≃ κ) (c : ι → F) (D : ℕ) (I J : ι → Finset ℤ) :
    CoordinateRing c D I J ≃ₐ[F]
      CoordinateRing (fun j ↦ c (e.symm j)) D (fun j ↦ I (e.symm j)) (fun j ↦ J (e.symm j)) :=
  Ideal.quotientEquivAlg _ _ (polynomialEquiv F e) (ideal_map e c D I J).symm

theorem domain_fin [CharZero F] (k D : ℕ) (c : Fin k → F)
    (I J : Fin k → Finset ℤ) (hc : ∀ i, c i ≠ 0)
    (hne : ∀ i, (I i).Nonempty ∨ (J i).Nonempty)
    (hI : Pairwise fun i j ↦ Disjoint (I i) (I j))
    (hJ : Pairwise fun i j ↦ Disjoint (J i) (J j)) : IsDomain (CoordinateRing c D I J) := by
  let s := List.ofFn (fun i : Fin k ↦ radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i))
  have hlen : s.length = k := List.length_ofFn
  let e : Fin s.length ≃ Fin k := (Fin.castOrderIso hlen).toEquiv
  let c' := fun i ↦ c (e i)
  let I' := fun i ↦ I (e i)
  let J' := fun i ↦ J (e i)
  have hs : ∀ i, s.get i = radicand (c' i) (2 * D - ((I' i).card + (J' i).card)) (I' i) (J' i) := by
    intro i
    exact List.get_ofFn _ i
  let := HomogeneousSplitRadicalPresentation.source_presentation_isDomain s c' D I' J' hs
    (fun i ↦ hc (e i)) (fun i ↦ hne (e i))
    (fun i j hij ↦ hI (e.injective.ne hij)) (fun i j hij ↦ hJ (e.injective.ne hij))
  have he : CoordinateRing c' D I' J' ≃ₐ[F] CoordinateRing c D I J := by
    have hh := coordinateEquiv e c' D I' J'
    have hc' : (fun j ↦ c' (e.symm j)) = c := by funext j; exact congrArg c (e.apply_symm_apply j)
    have hI' : (fun j ↦ I' (e.symm j)) = I := by funext j; exact congrArg I (e.apply_symm_apply j)
    have hJ' : (fun j ↦ J' (e.symm j)) = J := by funext j; exact congrArg J (e.apply_symm_apply j)
    rw [hc', hI', hJ'] at hh
    exact hh
  exact he.symm.injective.isDomain he.symm.toRingHom

end PaperP1.HomogeneousSplitRadicalIndexEquiv
