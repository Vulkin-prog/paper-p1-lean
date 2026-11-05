module

public import PaperP1.Analysis.SecondRegularCurveComponentGraphs
public import PaperP1.Analysis.JointExceptionalComponentGridCount
public import Mathlib.Topology.Homeomorph.Lemmas

/-! # Exact coordinate transport of genuine open regular regions and their components -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RegularRegionCoordinateSwap

open MvPolynomial Set PlaneCoordinateSwap JointExceptionalComponentGridCount

def swapHomeomorph : (Fin 2 → ℝ) ≃ₜ (Fin 2 → ℝ) where
  toFun := point
  invFun := point
  left_inv := point_twice
  right_inv := point_twice
  continuous_toFun := TransposedGraphImageNeighborhood.continuous_point
  continuous_invFun := TransposedGraphImageNeighborhood.continuous_point

def swapped (E : Finset (Fin 2 → ℝ)) : Finset (Fin 2 → ℝ) := E.image point

theorem point_injective : Function.Injective (point : (Fin 2 → ℝ) → Fin 2 → ℝ) := by
  intro z w he
  simpa only [point_twice] using congrArg point he

theorem swapped_card (E : Finset (Fin 2 → ℝ)) : (swapped E).card = E.card :=
  Finset.card_image_of_injective _ point_injective

theorem mem_swapped_point (E : Finset (Fin 2 → ℝ)) (z : Fin 2 → ℝ) :
    point z ∈ swapped E ↔ z ∈ E := by
  classical
  constructor
  · intro hz
    obtain ⟨w, hw, he⟩ := Finset.mem_image.mp hz
    exact point_injective he ▸ hw
  · exact fun hz ↦ Finset.mem_image.mpr ⟨z, hz, rfl⟩

theorem unitBox_point (z : Fin 2 → ℝ) : point z ∈ unitBox ↔ z ∈ unitBox := by
  constructor
  · intro hz i
    simpa only [point, index_twice] using hz (index i)
  · exact fun hz i ↦ hz (index i)

theorem mem_region (P : MvPolynomial (Fin 2) ℝ) (E : Finset (Fin 2 → ℝ)) (z : Fin 2 → ℝ) :
    point z ∈ RegularCurveComponentGraphs.region (polynomial P) (openRegion (swapped E)) ↔
      z ∈ SecondRegularCurveComponentGraphs.region P (openRegion E) := by
  have hp : eval (point z) (pderiv 1 (polynomial P)) = eval z (pderiv 0 P) := by
    simpa only [index_zero] using evaluation_partial P z 0
  constructor
  · intro hz
    refine ⟨⟨?_, ?_⟩, (unitBox_point z).mp hz.2.1, ?_⟩
    · simpa only [evaluation_polynomial_at_point] using hz.1.1
    · simpa only [hp] using hz.1.2
    · exact fun he ↦ hz.2.2 ((mem_swapped_point E z).mpr he)
  · intro hz
    refine ⟨⟨?_, ?_⟩, (unitBox_point z).mpr hz.2.1, ?_⟩
    · simpa only [evaluation_polynomial_at_point] using hz.1.1
    · simpa only [hp] using hz.1.2
    · exact fun he ↦ hz.2.2 ((mem_swapped_point E z).mp he)

theorem image_region (P : MvPolynomial (Fin 2) ℝ) (E : Finset (Fin 2 → ℝ)) :
    point '' SecondRegularCurveComponentGraphs.region P (openRegion E) =
      RegularCurveComponentGraphs.region (polynomial P) (openRegion (swapped E)) := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact (mem_region P E w).mpr hw
  · intro hz
    refine ⟨point z, ?_, point_twice z⟩
    apply (mem_region P E (point z)).mp
    simpa only [point_twice] using hz

theorem image_component (P : MvPolynomial (Fin 2) ℝ) (E : Finset (Fin 2 → ℝ))
    (a : Fin 2 → ℝ) (ha : a ∈ SecondRegularCurveComponentGraphs.region P (openRegion E)) :
    point '' connectedComponentIn (SecondRegularCurveComponentGraphs.region P (openRegion E)) a =
      connectedComponentIn (RegularCurveComponentGraphs.region (polynomial P) (openRegion (swapped E))) (point a) := by
  have hh := swapHomeomorph.image_connectedComponentIn ha
  change point '' connectedComponentIn (SecondRegularCurveComponentGraphs.region P (openRegion E)) a =
    connectedComponentIn (point '' SecondRegularCurveComponentGraphs.region P (openRegion E)) (point a) at hh
  rwa [image_region] at hh

theorem polynomial_irreducible (P : MvPolynomial (Fin 2) ℝ) (hP : Irreducible P) :
    Irreducible (polynomial P) :=
  (MulEquiv.irreducible_iff (MvPolynomial.renameEquiv ℝ index).toRingEquiv.toMulEquiv).mpr hP

end PaperP1.RegularRegionCoordinateSwap
