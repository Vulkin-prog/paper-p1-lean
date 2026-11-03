module

public import PaperP1.Algebra.RadicalProjectionPolynomialBaseChange
public import PaperP1.Algebra.SplitRadicalProjectionPolynomial

/-! # The same literal split-radical image equation remains irreducible over every characteristic-zero field extension -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SplitRadicalProjectionBaseChange

open Finset Polynomial PaperP1.FormalWordPolynomials PaperP1.ScaledSplitWordSquares
  PaperP1.SplitRadicalCoordinateAlgebra PaperP1.SplitRadicalProjectionPolynomial

def baseMap {F G : Type*} [Field F] [Field G] (φ : F →+* G) : F[X][X] →+* G[X][X] :=
  Polynomial.mapRingHom (Polynomial.mapRingHom φ)

theorem linear_map {F G : Type*} [Field F] [Field G] (φ : F →+* G) (I : Finset ℤ) :
    (linearOver F I).map φ = linearOver G I := by
  simp only [linearOver, Polynomial.map_prod, Polynomial.map_add, Polynomial.map_X, Polynomial.map_C]
  simp only [map_intCast]

theorem word_map {F G : Type*} [Field F] [Field G] (φ : F →+* G) (I J : Finset ℤ) :
    baseMap φ (wordOver F I J) = wordOver G I J := by
  change (wordOver F I J).map (Polynomial.mapRingHom φ) = _
  rw [wordOver, Polynomial.map_mul, Polynomial.map_C]
  change C ((linearOver F I).map φ) * ((linearOver F J).map C).map (Polynomial.mapRingHom φ) = _
  rw [linear_map, Polynomial.map_map]
  have he : (Polynomial.mapRingHom φ).comp (C (R := F)) = (C (R := G)).comp φ := by
    ext c
    simp
  rw [he, ← Polynomial.map_map, linear_map]
  rfl

theorem scaled_map {F G : Type*} [Field F] [Field G] (φ : F →+* G) (c : F) (I J : Finset ℤ) :
    baseMap φ (scaledPolynomial c I J) = scaledPolynomial (φ c) I J := by
  change (C (C c) * wordOver F I J).map (Polynomial.mapRingHom φ) = _
  rw [Polynomial.map_mul, Polynomial.map_C]
  change C ((C c).map φ) * baseMap φ (wordOver F I J) = _
  rw [Polynomial.map_C, word_map]
  rfl

theorem radicands_map {F G ι : Type*} [Field F] [Field G] (φ : F →+* G)
    (l : List ι) (c : ι → F) (I J : ι → Finset ℤ) :
    (radicands l c I J).map (baseMap φ) = radicands l (fun i ↦ φ (c i)) I J := by
  simp only [radicands, List.map_map, Function.comp_def, scaled_map]

theorem sourceEquation_map {F G ι : Type*} [Field F] [Field G] [CharZero G] (φ : F →+* G)
    (l : List ι) (hl : l.Nodup) (c : ι → F) (hc : ∀ i, c i ≠ 0) (I J : ι → Finset ℤ)
    (hne : ∀ i, (I i).Nonempty ∨ (J i).Nonempty)
    (hI : Pairwise fun i j ↦ Disjoint (I i) (I j)) (hJ : Pairwise fun i j ↦ Disjoint (J i) (J j)) :
    (sourceEquation l c I J).map (baseMap φ) = sourceEquation l (fun i ↦ φ (c i)) I J := by
  have hc' : ∀ i, φ (c i) ≠ 0 := fun i ↦ (map_ne_zero_iff φ φ.injective).mpr (hc i)
  have hs : PaperP1.IndependentQuadraticTower.Independent
      (((radicands l c I J).map (baseMap φ)).map (algebraMap G[X][X] (FunctionField G))) := by
    rw [radicands_map]
    exact generic_independent l hl (fun i ↦ φ (c i)) hc' I J hne hI hJ
  have hh := RadicalProjectionPolynomialBaseChange.map_equation F[X][X] G[X][X] (FunctionField G)
    (baseMap φ) (radicands l c I J) hs
  simpa only [sourceEquation, radicands_map] using hh

theorem source_irreducible_after_extension {F G ι : Type*} [Field F] [Field G] [CharZero G] (φ : F →+* G)
    (l : List ι) (hl : l.Nodup) (c : ι → F) (hc : ∀ i, c i ≠ 0) (I J : ι → Finset ℤ)
    (hne : ∀ i, (I i).Nonempty ∨ (J i).Nonempty)
    (hI : Pairwise fun i j ↦ Disjoint (I i) (I j)) (hJ : Pairwise fun i j ↦ Disjoint (J i) (J j)) :
    Irreducible ((sourceEquation l c I J).map (baseMap φ)) := by
  rw [sourceEquation_map φ l hl c hc I J hne hI hJ]
  exact source_equation_irreducible l hl (fun i ↦ φ (c i))
    (fun i ↦ (map_ne_zero_iff φ φ.injective).mpr (hc i)) I J hne hI hJ

end PaperP1.SplitRadicalProjectionBaseChange
