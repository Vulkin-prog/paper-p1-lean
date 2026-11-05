module

public import PaperP1.Analysis.FirstRegularComponentFamilyBound
public import PaperP1.Analysis.RegularRegionCoordinateSwap

/-! # The quadratic component-family budget in the original second orientation -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SecondRegularComponentFamilyBound

open MvPolynomial Set PlaneCoordinateSwap JointExceptionalComponentGridCount
open RegularRegionCoordinateSwap SecondRegularCurveComponentGraphs

theorem card_bound_of_comparison {ι : Type*} (I : Finset ι) (P : MvPolynomial (Fin 2) ℝ)
    (hP : Irreducible P) (E : Finset (Fin 2 → ℝ)) (a : ι → Fin 2 → ℝ)
    (ha : ∀ i ∈ I, a i ∈ region P (openRegion E))
    (hcomp : ∀ i ∈ I, ∀ z ∈ connectedComponentIn (region P (openRegion E)) (a i),
      |eval z (pderiv 1 P)| ≤ |eval z (pderiv 0 P)|)
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      Disjoint (connectedComponentIn (region P (openRegion E)) (a i))
        (connectedComponentIn (region P (openRegion E)) (a j))) :
    I.card ≤ E.card + P.totalDegree * (2 * P.totalDegree + 4) := by
  have hc := FirstRegularComponentFamilyBound.card_bound_of_comparison I (polynomial P)
    (polynomial_irreducible P hP) (swapped E) (fun i ↦ point (a i))
    (fun i hi ↦ (mem_region P E (a i)).mpr (ha i hi)) (by
      intro i hi z hz
      rw [← image_component P E (a i) (ha i hi)] at hz
      obtain ⟨v, hv, rfl⟩ := hz
      have hp0 : eval (point v) (pderiv 0 (polynomial P)) = eval v (pderiv 1 P) := by
        simpa only [index_one] using evaluation_partial P v 1
      have hp1 : eval (point v) (pderiv 1 (polynomial P)) = eval v (pderiv 0 P) := by
        simpa only [index_zero] using evaluation_partial P v 0
      rw [hp0, hp1]
      exact hcomp i hi v hv) (by
      intro i hi j hj hne
      rw [← image_component P E (a i) (ha i hi), ← image_component P E (a j) (ha j hj)]
      exact Set.disjoint_image_of_injective point_injective (hdisj i hi j hj hne))
  simpa only [swapped_card, PlaneCoordinateSwap.degree] using hc

theorem card_bound {ι : Type*} (I : Finset ι) (P : MvPolynomial (Fin 2) ℝ)
    (hP : Irreducible P) (E : Finset (Fin 2 → ℝ)) (a : ι → Fin 2 → ℝ)
    (ha : ∀ i ∈ I, a i ∈ region P (openRegion E)) (r : ℕ)
    (havoid : ∀ z ∈ region P (openRegion E), z ∉ GraphControlExceptions.points P r)
    (hinit : ∀ i ∈ I, |eval (a i) (pderiv 1 P)| ≤ |eval (a i) (pderiv 0 P)|)
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      Disjoint (connectedComponentIn (region P (openRegion E)) (a i))
        (connectedComponentIn (region P (openRegion E)) (a j))) :
    I.card ≤ E.card + P.totalDegree * (2 * P.totalDegree + 4) := by
  apply card_bound_of_comparison I P hP E a ha ?_ hdisj
  intro i hi z hz
  exact GradientComparisonControl.abs_ge_propagates P r _ isPreconnected_connectedComponentIn
    id continuousOn_id (fun v hv ↦
      ⟨(connectedComponentIn_subset (region P (openRegion E)) (a i) hv).1.1,
        havoid v (connectedComponentIn_subset _ _ hv)⟩)
    (a i) (mem_connectedComponentIn (ha i hi)) (hinit i hi) z hz

end PaperP1.SecondRegularComponentFamilyBound
