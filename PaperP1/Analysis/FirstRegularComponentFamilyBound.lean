module

public import PaperP1.Analysis.RegularEndpointBranch
public import PaperP1.Analysis.SinkComponentFamilyBound

/-! # Internal finite-family count for controlled first-orientation curve components -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FirstRegularComponentFamilyBound

open MvPolynomial Set RegularCurveComponentGraphs JointExceptionalComponentGridCount
open CurveComponentBarrier

theorem regular_endpoint_card {ι : Type*} (I : Finset ι) (P : MvPolynomial (Fin 2) ℝ)
    (E : Finset (Fin 2 → ℝ)) (a w : ι → Fin 2 → ℝ)
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      Disjoint (connectedComponentIn (region P (openRegion E)) (a i))
        (connectedComponentIn (region P (openRegion E)) (a j)))
    (hw : ∀ i ∈ I, w i ∈ closure (connectedComponentIn (region P (openRegion E)) (a i)))
    (hmin : ∀ i ∈ I, ∀ z ∈ connectedComponentIn (region P (openRegion E)) (a i), w i 0 ≤ z 0)
    (hregular : ∀ i ∈ I, eval (w i) P = 0 ∧ w i ∈ E ∧ w i ∈ unitBox ∧
      eval (w i) (pderiv 1 P) ≠ 0) : I.card ≤ E.card := by
  classical
  apply Finset.card_le_card_of_injOn w (fun i hi ↦ (hregular i hi).2.1)
  intro i hi j hj he
  by_contra hne
  obtain ⟨B, hBne, _hBconn, _hBsub, hbranch⟩ := RegularEndpointBranch.exists_branch P E (w i)
    (hregular i hi).1 (hregular i hi).2.1 (hregular i hi).2.2.1 (hregular i hi).2.2.2
  have hBi := hbranch (a i) (hw i hi) (hmin i hi)
  have hBj := hbranch (a j) (by rw [he]; exact hw j hj)
    (by rw [he]; exact hmin j hj)
  obtain ⟨z, hz⟩ := hBne
  exact Set.disjoint_left.mp (hdisj i hi j hj hne) (hBi hz) (hBj hz)

theorem card_bound_of_comparison {ι : Type*} (I : Finset ι) (P : MvPolynomial (Fin 2) ℝ)
    (hP : Irreducible P) (E : Finset (Fin 2 → ℝ)) (a : ι → Fin 2 → ℝ)
    (ha : ∀ i ∈ I, a i ∈ region P (openRegion E))
    (hcomp : ∀ i ∈ I, ∀ z ∈ connectedComponentIn (region P (openRegion E)) (a i),
      |eval z (pderiv 0 P)| ≤ |eval z (pderiv 1 P)|)
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      Disjoint (connectedComponentIn (region P (openRegion E)) (a i))
        (connectedComponentIn (region P (openRegion E)) (a j))) :
    I.card ≤ E.card + P.totalDegree * (2 * P.totalDegree + 4) := by
  classical
  let C : ι → Set (Fin 2 → ℝ) := fun i ↦ connectedComponentIn (region P (openRegion E)) (a i)
  have hex (i : ι) (hi : i ∈ I) := ControlledRegularComponentEnds.exists_end_of_comparison P E (a i)
    (ha i hi) (hcomp i hi)
  let w : ι → Fin 2 → ℝ := fun i ↦ if hi : i ∈ I then Classical.choose (hex i hi) else fun _ ↦ 0
  have hw (i : ι) (hi : i ∈ I) :
      w i ∈ closure (C i) ∧ eval (w i) P = 0 ∧ (∀ j, |w i j| ≤ 1) ∧
      (∀ z ∈ closure (C i), w i 0 ≤ z 0) ∧
      (eval (w i) (barrier P) = 0 ∨ (w i ∈ E ∧ w i ∈ unitBox ∧ eval (w i) (pderiv 1 P) ≠ 0)) := by
    dsimp only [w]
    rw [dite_eq_left hi]
    exact Classical.choose_spec (hex i hi)
  let K := I.filter (fun i ↦ eval (w i) (barrier P) = 0)
  let J := I.filter (fun i ↦ ¬eval (w i) (barrier P) = 0)
  have hK : K.card ≤ P.totalDegree * (2 * P.totalDegree + 4) := by
    apply SinkComponentFamilyBound.card_bound K P hP C
      (fun i hi j hj hne ↦ hdisj i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1 hne)
      (fun _ _ ↦ isPreconnected_connectedComponentIn)
      (fun i _ z hz ↦ (connectedComponentIn_subset _ (a i) hz).1.1) a w
      (fun i hi ↦ mem_connectedComponentIn (ha i (Finset.mem_filter.mp hi).1))
      (fun i hi ↦ positive P (a i) (ha i (Finset.mem_filter.mp hi).1).2.1
        ⟨1, (ha i (Finset.mem_filter.mp hi).1).1.2⟩)
      (fun i hi ↦ (hw i (Finset.mem_filter.mp hi).1).1)
      (fun i hi ↦ (hw i (Finset.mem_filter.mp hi).1).2.1)
      (fun _ hi ↦ (Finset.mem_filter.mp hi).2)
  have hJ : J.card ≤ E.card := by
    apply regular_endpoint_card J P E a w
      (fun i hi j hj hne ↦ hdisj i (Finset.mem_filter.mp hi).1 j (Finset.mem_filter.mp hj).1 hne)
      (fun i hi ↦ (hw i (Finset.mem_filter.mp hi).1).1)
      (fun i hi z hz ↦ (hw i (Finset.mem_filter.mp hi).1).2.2.2.1 z (subset_closure hz))
    intro i hi
    obtain ⟨hiI, hiH⟩ := Finset.mem_filter.mp hi
    exact ⟨(hw i hiI).2.1, (hw i hiI).2.2.2.2.resolve_left hiH⟩
  have hsum : K.card + J.card = I.card := Finset.card_filter_add_card_filter_not _
  omega

theorem card_bound {ι : Type*} (I : Finset ι) (P : MvPolynomial (Fin 2) ℝ)
    (hP : Irreducible P) (E : Finset (Fin 2 → ℝ)) (a : ι → Fin 2 → ℝ)
    (ha : ∀ i ∈ I, a i ∈ region P (openRegion E)) (r : ℕ)
    (havoid : ∀ z ∈ region P (openRegion E), z ∉ GraphControlExceptions.points P r)
    (hinit : ∀ i ∈ I, |eval (a i) (pderiv 0 P)| ≤ |eval (a i) (pderiv 1 P)|)
    (hdisj : ∀ i ∈ I, ∀ j ∈ I, i ≠ j →
      Disjoint (connectedComponentIn (region P (openRegion E)) (a i))
        (connectedComponentIn (region P (openRegion E)) (a j))) :
    I.card ≤ E.card + P.totalDegree * (2 * P.totalDegree + 4) := by
  apply card_bound_of_comparison I P hP E a ha ?_ hdisj
  intro i hi z hz
  exact GradientComparisonControl.abs_le_propagates P r _ isPreconnected_connectedComponentIn
    id continuousOn_id (fun v hv ↦
      ⟨(connectedComponentIn_subset (region P (openRegion E)) (a i) hv).1.1,
        havoid v (connectedComponentIn_subset _ _ hv)⟩)
    (a i) (mem_connectedComponentIn (ha i hi)) (hinit i hi) z hz

end PaperP1.FirstRegularComponentFamilyBound
