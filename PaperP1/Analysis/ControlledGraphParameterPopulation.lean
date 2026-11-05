module

public import PaperP1.Analysis.UnitSlopePieceRestriction
public import PaperP1.Analysis.IteratedDerivativeMonotonicity
public import PaperP1.Analysis.AffineUnitGraphParametrization
public import Mathlib.Data.Finset.Image

/-! # Exact parameters and bounded intermediate values on controlled graph pieces -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ControlledGraphParameterPopulation

open MvPolynomial Set Finset UnitSlopeNormalizedCharts PlaneCoordinateSwap
open scoped ContDiff

theorem coordinate_monotonicity (P : MvPolynomial (Fin 2) ℝ) (r : ℕ) (hr : 1 ≤ r)
    (q : Piece P r) (i : Fin 2) :
    MonotoneOn (q.path i) (Ioo q.left q.right) ∨ AntitoneOn (q.path i) (Ioo q.left q.right) := by
  rcases AffineUnitGraphParametrization.eq_or_transpose i q.independent with hi | hi
  · rw [hi]
    exact Or.inl (fun x hx y hy hxy ↦ by rw [q.normalized_coordinate x hx, q.normalized_coordinate y hy]; exact hxy)
  · rw [hi]
    simpa only [iteratedDeriv_zero] using IteratedDerivativeMonotonicity.monotone_or_antitone
      (q.path (index q.independent)) q.left q.right (q.smooth _) 0
      (fun x hx y hy ↦ q.derivative_signs 1 hr x hx y hy)

theorem box_between (P : MvPolynomial (Fin 2) ℝ) (r : ℕ) (hr : 1 ≤ r) (q : Piece P r)
    (a b : ℝ) (ha : a ∈ Ioo q.left q.right) (hb : b ∈ Ioo q.left q.right)
    (hboxa : ∀ i, |q.path i a| ≤ 1) (hboxb : ∀ i, |q.path i b| ≤ 1)
    (t : ℝ) (ht : t ∈ Icc a b) : ∀ i, |q.path i t| ≤ 1 := by
  have hmem : t ∈ Ioo q.left q.right := ⟨ha.1.trans_le ht.1, ht.2.trans_lt hb.2⟩
  intro i
  have hA := abs_le.mp (hboxa i)
  have hB := abs_le.mp (hboxb i)
  rcases coordinate_monotonicity P r hr q i with hm | hm
  · exact abs_le.mpr ⟨hA.1.trans (hm ha hmem ht.1), (hm hmem hb ht.2).trans hB.2⟩
  · exact abs_le.mpr ⟨hB.1.trans (hm hmem hb ht.2), (hm ha hmem ht.1).trans hA.2⟩

theorem parameter_of_point (P : MvPolynomial (Fin 2) ℝ) (r : ℕ) (q : Piece P r)
    (w : Fin 2 → ℝ) (hw : ∃ t ∈ Ioo q.left q.right, (fun i ↦ q.path i t) = w) :
    w q.independent ∈ Ioo q.left q.right ∧ (fun i ↦ q.path i (w q.independent)) = w := by
  obtain ⟨t, ht, he⟩ := hw
  have hc : w q.independent = t := by
    rw [← he]
    exact q.normalized_coordinate t ht
  rw [hc]
  exact ⟨ht, he⟩

theorem pointMap_injective (P : MvPolynomial (Fin 2) ℝ) (r : ℕ) (q : Piece P r) :
    InjOn (fun t ↦ fun i ↦ q.path i t) (Ioo q.left q.right) := by
  intro t ht u hu he
  have hh := congrFun he q.independent
  change q.path q.independent t = q.path q.independent u at hh
  rw [q.normalized_coordinate t ht, q.normalized_coordinate u hu] at hh
  exact hh

theorem finite_parameter_population (P : MvPolynomial (Fin 2) ℝ) (r : ℕ) (q : Piece P r)
    (N : ℕ) (S : Finset (Fin 2 → ℝ))
    (hS : ∀ w ∈ S, ∃ t ∈ Ioo q.left q.right, (fun i ↦ q.path i t) = w)
    (hbox : ∀ w ∈ S, ∀ i, |w i| ≤ 1)
    (hgrid : ∀ w ∈ S, ∃ z : Fin 2 → ℤ, ∀ i, w i = (z i : ℝ) / N) :
    ∃ T : Finset ℝ, T.card = S.card ∧
      ∀ t ∈ T, t ∈ Ioo q.left q.right ∧ (∀ i, |q.path i t| ≤ 1) ∧
        (fun i ↦ q.path i t) ∈ S ∧
        ∃ m : ℤ, t = (m : ℝ) / N := by
  classical
  let T := S.image (fun w ↦ w q.independent)
  have hinj : InjOn (fun w : Fin 2 → ℝ ↦ w q.independent) (S : Set (Fin 2 → ℝ)) := by
    intro w hw v hv he
    have hw' := (parameter_of_point P r q w (hS w hw)).2
    have hv' := (parameter_of_point P r q v (hS v hv)).2
    change w q.independent = v q.independent at he
    rw [he] at hw'
    exact hw'.symm.trans hv'
  refine ⟨T, card_image_of_injOn hinj, ?_⟩
  intro t ht
  obtain ⟨w, hw, rfl⟩ := mem_image.mp ht
  have hp := parameter_of_point P r q w (hS w hw)
  refine ⟨hp.1, ?_, ?_, ?_⟩
  · intro i
    have he := congrFun hp.2 i
    rw [he]
    exact hbox w hw i
  · rw [hp.2]
    exact hw
  · obtain ⟨z, hz⟩ := hgrid w hw
    exact ⟨z q.independent, hz q.independent⟩

end PaperP1.ControlledGraphParameterPopulation
