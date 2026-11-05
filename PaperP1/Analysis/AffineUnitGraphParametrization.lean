module

public import PaperP1.Analysis.AffineInteriorUnitDerivatives
public import PaperP1.Analysis.UnitSlopeHigherDerivativeBounds

/-! # Actual unit graph jets and coverage of an admissible interior segment

The order-zero condition is the explicit bounded-box condition. All positive
order bounds follow from the actual curve chart and the short affine scale.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.AffineUnitGraphParametrization

open MvPolynomial Set PlaneCoordinateSwap UnitSlopeNormalizedCharts LocalAffineDerivativeFormula
open scoped ContDiff

def path {P : MvPolynomial (Fin 2) ℝ} {r : ℕ} (q : Piece P (r + 1)) (u c : ℝ) :
    Fin 2 → ℝ → ℝ := fun i t ↦ q.path i (parameter u c t)

def UnitJets (r : ℕ) (ψ : Fin 2 → ℝ → ℝ) : Prop :=
  ∀ i, ∀ j ≤ r, ∀ t ∈ Ioo (0 : ℝ) 1, |iteratedDeriv j (ψ i) t| ≤ 1

theorem eq_or_transpose (i j : Fin 2) : i = j ∨ i = index j := by
  fin_cases i <;> fin_cases j <;> decide

theorem unit_jets (P : MvPolynomial (Fin 2) ℝ) (r : ℕ) (q : Piece P (r + 1))
    (δ : ℝ) (hδ : 0 < δ) (u c : ℝ) (hc : 0 ≤ c) (hcone : c ≤ 1)
    (hscale : c ≤ δ / (2 * ((r + 1 : ℕ) : ℝ)))
    (hmargin : ∀ t ∈ Ioo (0 : ℝ) 1, q.left + δ ≤ parameter u c t ∧ parameter u c t ≤ q.right - δ)
    (hvalues : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ i, |q.path i (parameter u c t)| ≤ 1) :
    UnitJets r (path q u c) := by
  have hmap : MapsTo (parameter u c) (Ioo (0 : ℝ) 1) (Ioo q.left q.right) := by
    intro t ht
    have hm := hmargin t ht
    exact ⟨by linarith [hm.1], by linarith [hm.2]⟩
  intro i j hj t ht
  by_cases hzero : j = 0
  · subst j
    simpa only [iteratedDeriv_zero, path] using hvalues t ht i
  · have hjpos : 1 ≤ j := by omega
    rcases eq_or_transpose i q.independent with hi | hi
    · rw [hi]
      have heq : EqOn (fun v ↦ q.path q.independent (parameter u c v)) (parameter u c) (Ioo (0 : ℝ) 1) :=
        fun v hv ↦ q.normalized_coordinate _ (hmap hv)
      have hjet := heq.iteratedDeriv_of_isOpen isOpen_Ioo j
      change |iteratedDeriv j (fun v ↦ q.path q.independent (parameter u c v)) t| ≤ 1
      rw [hjet ht, positive_parameter_derivative u c j hjpos t]
      split_ifs
      · rw [abs_of_nonneg hc]
        exact hcone
      · simp only [abs_zero, zero_le_one]
    · rw [hi]
      change |iteratedDeriv j (fun v ↦ q.path (index q.independent) (parameter u c v)) t| ≤ 1
      exact AffineInteriorUnitDerivatives.positive_unit_derivative _ q.left q.right δ hδ r
        (q.smooth (index q.independent)) q.slope
        (fun n hn ↦ UnitSlopeHigherDerivativeBounds.derivative_monotonicity P (r + 1) q n (by omega))
        u c hc hcone hscale j hjpos hj t (hmargin t ht).1 (hmargin t ht).2

theorem unit_curve_parametrization (P : MvPolynomial (Fin 2) ℝ) (r : ℕ) (q : Piece P (r + 1))
    (δ : ℝ) (hδ : 0 < δ) (u c : ℝ) (hc : 0 < c) (hcone : c ≤ 1)
    (hscale : c ≤ δ / (2 * ((r + 1 : ℕ) : ℝ)))
    (hmargin : ∀ t ∈ Ioo (0 : ℝ) 1, q.left + δ ≤ parameter u c t ∧ parameter u c t ≤ q.right - δ)
    (hvalues : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ i, |q.path i (parameter u c t)| ≤ 1) :
    (∀ i, ContDiffOn ℝ ∞ (path q u c i) (Ioo (0 : ℝ) 1)) ∧
      UnitJets r (path q u c) ∧
      (∀ t ∈ Ioo (0 : ℝ) 1, eval (fun i ↦ path q u c i t) P = 0) ∧
      ∀ x ∈ Ioo u (u + c), ∃ t ∈ Ioo (0 : ℝ) 1,
        (fun i ↦ path q u c i t) = (fun i ↦ q.path i x) := by
  have hmap : MapsTo (parameter u c) (Ioo (0 : ℝ) 1) (Ioo q.left q.right) := by
    intro t ht
    have hm := hmargin t ht
    exact ⟨by linarith [hm.1], by linarith [hm.2]⟩
  refine ⟨?_, unit_jets P r q δ hδ u c hc.le hcone hscale hmargin hvalues, ?_, ?_⟩
  · intro i
    exact (q.smooth i).comp (contDiff_parameter u c ∞).contDiffOn hmap
  · intro t ht
    exact q.equation (parameter u c t) (hmap ht)
  · intro x hx
    obtain ⟨t, ht, heq⟩ := image_parameter u c hc x hx
    refine ⟨t, ht, ?_⟩
    change (fun i ↦ q.path i (parameter u c t)) = (fun i ↦ q.path i x)
    rw [heq]

end PaperP1.AffineUnitGraphParametrization
