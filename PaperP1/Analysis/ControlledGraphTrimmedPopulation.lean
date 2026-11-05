module

public import PaperP1.Analysis.ControlledGraphParameterPopulation
public import PaperP1.Analysis.NormalizedGridSpacing

/-! # Actual bounded graph intervals with trimmed grid populations

The selected endpoints come from the original point set. All intermediate
curve values stay in the unit box, and at most two original points are lost.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ControlledGraphTrimmedPopulation

open MvPolynomial Set Finset UnitSlopeNormalizedCharts ControlledGraphParameterPopulation


theorem exists_trimmed_population (P : MvPolynomial (Fin 2) ℝ) (r : ℕ) (hr : 1 ≤ r)
    (q : Piece P r) (N : ℕ) (hN : 0 < N) (S : Finset (Fin 2 → ℝ)) (hne : S.Nonempty)
    (hS : ∀ w ∈ S, ∃ t ∈ Ioo q.left q.right, (fun i ↦ q.path i t) = w)
    (hbox : ∀ w ∈ S, ∀ i, |w i| ≤ 1)
    (hgrid : ∀ w ∈ S, ∃ z : Fin 2 → ℤ, ∀ i, w i = (z i : ℝ) / N) :
    ∃ a b : ℝ, a ∈ Ioo q.left q.right ∧ b ∈ Ioo q.left q.right ∧ a ≤ b ∧
      ∃ R : Finset ℝ, S.card ≤ R.card + 2 ∧
        (∀ t ∈ Icc a b, ∀ i, |q.path i t| ≤ 1) ∧
        ∀ t ∈ R, a + 1 / (N : ℝ) ≤ t ∧ t ≤ b - 1 / (N : ℝ) ∧
          t ∈ Ioo q.left q.right ∧ (fun i ↦ q.path i t) ∈ S := by
  obtain ⟨T, hcard, hT⟩ := finite_parameter_population P r q N S hS hbox hgrid
  have hTne : T.Nonempty := card_pos.mp (by rw [hcard]; exact card_pos.mpr hne)
  obtain ⟨a, ha, b, hb, R, hsub, hcardR, hbounds, hmargin⟩ :=
    NormalizedGridSpacing.trimmed_population N hN T hTne (fun t ht ↦ (hT t ht).2.2.2)
  refine ⟨a, b, (hT a ha).1, (hT b hb).1, (hbounds a ha).2, R, ?_, ?_, ?_⟩
  · rw [← hcard]
    exact hcardR
  · intro t ht
    exact box_between P r hr q a b (hT a ha).1 (hT b hb).1 (hT a ha).2.1 (hT b hb).2.1 t ht
  · intro t ht
    exact ⟨(hmargin t ht).1, (hmargin t ht).2, (hT t (hsub ht)).1, (hT t (hsub ht)).2.2.1⟩

end PaperP1.ControlledGraphTrimmedPopulation
