module

public import PaperP1.Algebra.HomogeneousSplitRadicalRelations
public import PaperP1.Algebra.HomogeneousSplitRadicalAlgebra
public import PaperP1.Algebra.QuadraticTowerPresentation

/-! # The literal weighted polynomial quotient is the integral homogenized radical algebra -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HomogeneousSplitRadicalPresentation

open Finset Polynomial PaperP1.HomogeneousSplitRadicalData
  PaperP1.HomogeneousSplitRadicalRelations PaperP1.HomogeneousSplitRadicalPolynomials
  PaperP1.TrivariatePolynomialEquiv

local instance baseRing (F : Type*) [Field F] : CommRing (PolynomialRing F) := inferInstance
local instance nativeRing (F : Type*) [Field F] : CommRing (MvPolynomial (Fin 3) F) := inferInstance
local instance weightedRing (F ι : Type*) [Field F] : CommRing (WeightedPolynomial F ι) := inferInstance
local instance targetRing (F : Type*) [Field F] (k : ℕ) :
    CommRing (MvPolynomial (Fin k) (PolynomialRing F)) := inferInstance

def polynomialEquiv (F : Type*) [Field F] (k : ℕ) :
    WeightedPolynomial F (Fin k) ≃+* MvPolynomial (Fin k) (PolynomialRing F) :=
  ((MvPolynomial.renameEquiv F (Equiv.sumComm (Fin 3) (Fin k))).toRingEquiv.trans
    (MvPolynomial.sumAlgEquiv F (Fin k) (Fin 3)).toRingEquiv).trans
      (MvPolynomial.mapEquiv (Fin k) (threeEquiv F).toRingEquiv)

theorem polynomialEquiv_C (F : Type*) [Field F] (k : ℕ) (c : F) :
    polynomialEquiv F k (MvPolynomial.C c) = MvPolynomial.C (C (C (C c))) := by
  change MvPolynomial.map (threeEquiv F).toRingHom
    (MvPolynomial.sumAlgEquiv F (Fin k) (Fin 3)
      (MvPolynomial.rename (Equiv.sumComm (Fin 3) (Fin k)) (MvPolynomial.C c))) = _
  rw [MvPolynomial.rename_C, MvPolynomial.sumAlgEquiv_C_inl, MvPolynomial.map_C]
  change MvPolynomial.C (threeEquiv F (MvPolynomial.C c)) = _
  rw [threeEquiv_C]

theorem polynomialEquiv_base_X (F : Type*) [Field F] (k : ℕ) (j : Fin 3) :
    polynomialEquiv F k (MvPolynomial.X (Sum.inl j)) =
      MvPolynomial.C (threeEquiv F (MvPolynomial.X j)) := by
  change MvPolynomial.map (threeEquiv F).toRingHom
    (MvPolynomial.sumAlgEquiv F (Fin k) (Fin 3)
      (MvPolynomial.rename (Equiv.sumComm (Fin 3) (Fin k)) (MvPolynomial.X (Sum.inl j)))) = _
  rw [MvPolynomial.rename_X]
  change MvPolynomial.map (threeEquiv F).toRingHom
    (MvPolynomial.sumAlgEquiv F (Fin k) (Fin 3) (MvPolynomial.X (Sum.inr j))) = _
  rw [MvPolynomial.sumAlgEquiv_X_inr, MvPolynomial.map_C]
  rfl

theorem polynomialEquiv_radical_X (F : Type*) [Field F] (k : ℕ) (i : Fin k) :
    polynomialEquiv F k (MvPolynomial.X (Sum.inr i)) = MvPolynomial.X i := by
  change MvPolynomial.map (threeEquiv F).toRingHom
    (MvPolynomial.sumAlgEquiv F (Fin k) (Fin 3)
      (MvPolynomial.rename (Equiv.sumComm (Fin 3) (Fin k)) (MvPolynomial.X (Sum.inr i)))) = _
  rw [MvPolynomial.rename_X]
  change MvPolynomial.map (threeEquiv F).toRingHom
    (MvPolynomial.sumAlgEquiv F (Fin k) (Fin 3) (MvPolynomial.X (Sum.inl i))) = _
  rw [MvPolynomial.sumAlgEquiv_X_inl, MvPolynomial.map_X]

theorem polynomialEquiv_rename (F : Type*) [Field F] (k : ℕ) (p : MvPolynomial (Fin 3) F) :
    polynomialEquiv F k (MvPolynomial.rename Sum.inl p) = MvPolynomial.C (threeEquiv F p) := by
  have he : (polynomialEquiv F k).toRingHom.comp (MvPolynomial.rename Sum.inl).toRingHom =
      MvPolynomial.C.comp (threeEquiv F).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change polynomialEquiv F k (MvPolynomial.rename Sum.inl (MvPolynomial.C a)) =
        MvPolynomial.C (threeEquiv F (MvPolynomial.C a))
      rw [MvPolynomial.rename_C, polynomialEquiv_C, threeEquiv_C]
    · intro j
      change polynomialEquiv F k (MvPolynomial.rename Sum.inl (MvPolynomial.X j)) =
        MvPolynomial.C (threeEquiv F (MvPolynomial.X j))
      rw [MvPolynomial.rename_X, polynomialEquiv_base_X]
  exact DFunLike.congr_fun he p

theorem polynomialEquiv_relation {F : Type*} [Field F]
    (s : List (PolynomialRing F)) (c : Fin s.length → F) (D : ℕ)
    (I J : Fin s.length → Finset ℤ)
    (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i))
    (i : Fin s.length) :
    polynomialEquiv F s.length (relation (c i) D (I i) (J i) i) =
      QuadraticTowerPresentation.relation (PolynomialRing F) s i := by
  simp only [relation, map_sub, map_pow, polynomialEquiv_radical_X, polynomialEquiv_rename,
    nativeRadicand_map, QuadraticTowerPresentation.relation, hs]

theorem relationIdeal_map {F : Type*} [Field F]
    (s : List (PolynomialRing F)) (c : Fin s.length → F) (D : ℕ)
    (I J : Fin s.length → Finset ℤ)
    (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i)) :
    (relationIdeal c D I J).map (polynomialEquiv F s.length).toRingHom =
      QuadraticTowerPresentation.relationIdeal (PolynomialRing F) s := by
  rw [relationIdeal, Ideal.map_span, ← Set.range_comp']
  unfold QuadraticTowerPresentation.relationIdeal
  congr 1
  exact congrArg Set.range (funext (polynomialEquiv_relation s c D I J hs))

def presentationEquiv {F : Type*} [Field F]
    (s : List (PolynomialRing F)) (c : Fin s.length → F) (D : ℕ)
    (I J : Fin s.length → Finset ℤ)
    (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i)) :
    WeightedPolynomial F (Fin s.length) ⧸ relationIdeal c D I J ≃+*
      FiniteQuadraticTower.Tower (PolynomialRing F) s := by
  let e₁ : WeightedPolynomial F (Fin s.length) ⧸ relationIdeal c D I J ≃+*
      QuadraticTowerPresentation.Presentation (PolynomialRing F) s :=
    Ideal.quotientEquiv _ _ (polynomialEquiv F s.length) (relationIdeal_map s c D I J hs).symm
  let e₂ : QuadraticTowerPresentation.Presentation (PolynomialRing F) s ≃+*
      FiniteQuadraticTower.Tower (PolynomialRing F) s :=
    (QuadraticTowerPresentation.presentationEquiv (PolynomialRing F) s).toRingEquiv
  exact e₁.trans e₂

theorem presentation_isDomain {F : Type*} [Field F]
    (s : List (PolynomialRing F)) (c : Fin s.length → F) (D : ℕ)
    (I J : Fin s.length → Finset ℤ)
    (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i))
    (h : IsDomain (FiniteQuadraticTower.Tower (PolynomialRing F) s)) :
    IsDomain (WeightedPolynomial F (Fin s.length) ⧸ relationIdeal c D I J) := by
  let := h
  exact (presentationEquiv s c D I J hs).injective.isDomain (presentationEquiv s c D I J hs).toRingHom

theorem source_presentation_isDomain {F : Type*} [Field F] [CharZero F]
    (s : List (PolynomialRing F)) (c : Fin s.length → F) (D : ℕ)
    (I J : Fin s.length → Finset ℤ)
    (hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J i).card)) (I i) (J i))
    (hc : ∀ i, c i ≠ 0) (hne : ∀ i, (I i).Nonempty ∨ (J i).Nonempty)
    (hI : Pairwise fun i j ↦ Disjoint (I i) (I j)) (hJ : Pairwise fun i j ↦ Disjoint (J i) (J j)) :
    IsDomain (WeightedPolynomial F (Fin s.length) ⧸ relationIdeal c D I J) := by
  apply presentation_isDomain s c D I J hs
  let e := fun i ↦ 2 * D - ((I i).card + (J i).card)
  have hlist : s = HomogeneousSplitRadicalAlgebra.radicands (List.finRange s.length) c e I J := by
    calc
      s = List.ofFn s.get := (List.ofFn_get s).symm
      _ = List.ofFn (fun i ↦ radicand (c i) (e i) (I i) (J i)) := congrArg List.ofFn (funext hs)
      _ = _ := List.ofFn_eq_map
  have hd := HomogeneousSplitRadicalAlgebra.coordinate_isDomain
    (List.finRange s.length) (List.nodup_finRange _) c hc e I J hne hI hJ
  change IsDomain (FiniteQuadraticTower.Tower (PolynomialRing F)
    (HomogeneousSplitRadicalAlgebra.radicands (List.finRange s.length) c e I J)) at hd
  rw [← hlist] at hd
  exact hd

end PaperP1.HomogeneousSplitRadicalPresentation
