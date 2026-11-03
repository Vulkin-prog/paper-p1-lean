module

public import PaperP1.Arithmetic.SplitRadicalLineObstruction
public import PaperP1.Algebra.SplitRadicalCoordinateAlgebra

/-! # The actual split-radical coordinate algebra has no function-field point over an excluded line -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SplitRadicalLineMap

open Finset Polynomial PaperP1.FiniteQuadraticTower PaperP1.FormalWordPolynomials
  PaperP1.ScaledSplitWordSquares PaperP1.SplitRadicalCoordinateAlgebra
  PaperP1.SquareLineMatching PaperP1.SelectedProportionalPairs

def lineMap (α β : ℚ) : ℚ[X][X] →+* ℚ[X] := evalRingHom (C α * X + C β)

theorem lineMap_scaled (α β c : ℚ) (I J : Finset ℤ) :
    lineMap α β (scaledPolynomial c I J) = lineRestriction c I J α β := by
  change (scaledPolynomial c I J).eval (C α * X + C β) = _
  simp only [scaledPolynomial, wordOver, eval_mul, eval_C, eval_map]
  change C c * (linearOver ℚ I * (linearOver ℚ J).comp (C α * X + C β)) =
    C c * linearOver ℚ I * (linearOver ℚ J).comp (C α * X + C β)
  rw [mul_assoc]

theorem hom_square {ι : Type*} (l : List ι) (c : ι → ℚ) (I J : ι → Finset ℤ) (α β : ℚ)
    (ψ : CoordinateAlgebra l c I J →+* FractionRing ℚ[X])
    (hbase : ∀ P : ℚ[X][X], ψ (algebraMap ℚ[X][X] (CoordinateAlgebra l c I J) P) =
      algebraMap ℚ[X] (FractionRing ℚ[X]) (lineMap α β P)) (i : ι) (hi : i ∈ l) :
    IsSquare (algebraMap ℚ[X] (FractionRing ℚ[X]) (lineRestriction (c i) (I i) (J i) α β)) := by
  have hmem : scaledPolynomial (c i) (I i) (J i) ∈ radicands l c I J := List.mem_map.mpr ⟨i, hi, rfl⟩
  obtain ⟨j, hj⟩ := (List.exists_mem_iff_get (l := radicands l c I J)
    (p := fun P ↦ P = scaledPolynomial (c i) (I i) (J i))).mp
      ⟨scaledPolynomial (c i) (I i) (J i), hmem, rfl⟩
  have hh := congrArg ψ (root_square ℚ[X][X] (radicands l c I J) j)
  rw [map_pow, hj, hbase, lineMap_scaled] at hh
  exact ⟨ψ (root ℚ[X][X] (radicands l c I J) j), by simpa only [pow_two] using hh.symm⟩

theorem no_line_map {ι : Type*} [DecidableEq ι]
    (l : List ι) (hcard : 2 ≤ l.toFinset.card) (S T : Finset ℤ)
    (c : ι → ℚ) (I J : ι → Finset ℤ) (x y : ℤ) (α β : ℚ)
    (hI : ∀ i, I i ⊆ S) (hJ : ∀ i, J i ⊆ T)
    (hdisj : Pairwise fun i j ↦ Disjoint (I i) (I j)) (hne : ∀ i, (I i).Nonempty)
    (hposS : ∀ i ∈ S, 0 < x + i) (hposT : ∀ j ∈ T, 0 < y + j)
    (hind : EvenIndependentValues.Independent (values x S))
    (hdirect : Disjoint (FiniteEvenSquareClasses.space (values x S)) (FiniteEvenSquareClasses.space (values y T)))
    (hline : (y : ℚ) = α * (x : ℚ) + β) (hc : ∀ i, c i ≠ 0) :
    ¬∃ ψ : CoordinateAlgebra l c I J →+* FractionRing ℚ[X],
      ∀ P : ℚ[X][X], ψ (algebraMap ℚ[X][X] (CoordinateAlgebra l c I J) P) =
        algebraMap ℚ[X] (FractionRing ℚ[X]) (lineMap α β P) := by
  rintro ⟨ψ, hbase⟩
  apply SplitRadicalLineObstruction.family_obstruction l.toFinset hcard S T I J x y α β c
    (fun i _ ↦ hI i) (fun i _ ↦ hJ i) (fun _ _ _ _ hij ↦ hdisj hij) (fun i _ ↦ hne i)
    hposS hposT hind hdirect hline (fun i _ ↦ hc i)
  intro i hi
  exact hom_square l c I J α β ψ hbase i (List.mem_toFinset.mp hi)

end PaperP1.SplitRadicalLineMap
