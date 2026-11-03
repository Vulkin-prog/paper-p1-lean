module

public import PaperP1.Algebra.AffineCurveGraphPresentation

/-! # Actual generators of a plane-curve function field and its rational parametrization -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AffineCurveFieldGeneration

open Polynomial IntermediateField PaperP1.AffineCurveFunctionField

variable {F : Type*} [Field F]

theorem specialize_mem (C₀ : F[X][X]) [Fact (Irreducible C₀)]
    (L : IntermediateField F (FunctionField C₀))
    (hx : firstCoordinate C₀ ∈ L) (hy : secondCoordinate C₀ ∈ L) (P : F[X][X]) :
    specialize C₀ P ∈ L := by
  let x : L := ⟨firstCoordinate C₀, hx⟩
  let y : L := ⟨secondCoordinate C₀, hy⟩
  have heq : L.val.comp (Polynomial.aevalAeval x y) = specialize C₀ := by
    ext <;> simp [x, y, firstCoordinate, secondCoordinate]
  rw [← heq]
  exact (Polynomial.aevalAeval x y P).property

theorem eq_top_of_coordinates_mem (C₀ : F[X][X]) [Fact (Irreducible C₀)]
    (L : IntermediateField F (FunctionField C₀))
    (hx : firstCoordinate C₀ ∈ L) (hy : secondCoordinate C₀ ∈ L) : L = ⊤ := by
  let : CommRing (CoordinateRing C₀) := inferInstance
  apply eq_top_iff.mpr
  intro z _
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (CoordinateRing C₀) z
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective a
  obtain ⟨Q, rfl⟩ := Ideal.Quotient.mk_surjective b
  change specialize C₀ P / specialize C₀ Q ∈ L
  exact L.div_mem (specialize_mem C₀ L hx hy P) (specialize_mem C₀ L hx hy Q)

theorem coordinates_generate (C₀ : F[X][X]) [Fact (Irreducible C₀)] :
    adjoin F {firstCoordinate C₀, secondCoordinate C₀} = ⊤ := by
  apply eq_top_of_coordinates_mem
  · exact subset_adjoin F _ (Set.mem_insert _ _)
  · exact subset_adjoin F _ (Set.mem_insert_of_mem _ (Set.mem_singleton _))

theorem first_generates_of_graph (C₀ : F[X][X]) [Fact (Irreducible C₀)] (hdegree : 0 < C₀.natDegree)
    (p q : F[X]) (hq : q ≠ 0)
    (hgraph : aeval (firstCoordinate C₀) p = secondCoordinate C₀ * aeval (firstCoordinate C₀) q) :
    adjoin F {firstCoordinate C₀} = ⊤ := by
  have hx := first_transcendental C₀ hdegree
  have hqeval : aeval (firstCoordinate C₀) q ≠ 0 := by
    intro hz
    apply hq
    apply transcendental_iff_injective.mp hx
    simpa only [map_zero] using hz
  have hy : secondCoordinate C₀ = aeval (firstCoordinate C₀) p / aeval (firstCoordinate C₀) q :=
    (eq_div_iff hqeval).mpr hgraph.symm
  apply eq_top_of_coordinates_mem
  · exact mem_adjoin_simple_self F _
  · rw [hy]
    exact adjoin_simple_le_iff.mp (RationalGraphFieldTower.graph_subfield_le (firstCoordinate C₀) hx p q)

def rationalEquiv (C₀ : F[X][X]) [Fact (Irreducible C₀)] (hdegree : 0 < C₀.natDegree)
    (p q : F[X]) (hq : q ≠ 0)
    (hgraph : aeval (firstCoordinate C₀) p = secondCoordinate C₀ * aeval (firstCoordinate C₀) q) :
    RatFunc F ≃ₐ[F] FunctionField C₀ :=
  (RatFunc.algEquivOfTranscendental (firstCoordinate C₀) (first_transcendental C₀ hdegree)).trans
    ((IntermediateField.equivOfEq (first_generates_of_graph C₀ hdegree p q hq hgraph)).trans
      IntermediateField.topEquiv)

theorem rationalEquiv_X (C₀ : F[X][X]) [Fact (Irreducible C₀)] (hdegree : 0 < C₀.natDegree)
    (p q : F[X]) (hq : q ≠ 0)
    (hgraph : aeval (firstCoordinate C₀) p = secondCoordinate C₀ * aeval (firstCoordinate C₀) q) :
    rationalEquiv C₀ hdegree p q hq hgraph (RatFunc.X : RatFunc F) = firstCoordinate C₀ := by
  change ((RatFunc.algEquivOfTranscendental (firstCoordinate C₀) (first_transcendental C₀ hdegree)) RatFunc.X :
    FunctionField C₀) = firstCoordinate C₀
  exact RatFunc.algEquivOfTranscendental_X _ _

end PaperP1.AffineCurveFieldGeneration
