module

public import PaperP1.Analysis.UnitSlopeNormalizedCharts
public import PaperP1.Analysis.IteratedDerivativeInteriorBound

/-! # Actual quantitative higher derivative bounds on constructed curve graphs

Control through r+1 supplies bounds through r. The chart is selected before
all derivative orders, interior margins and tested parameters.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UnitSlopeHigherDerivativeBounds

open MvPolynomial Set PlaneCoordinateSwap UnitSlopeNormalizedCharts
open scoped ContDiff

theorem derivative_monotonicity (P : MvPolynomial (Fin 2) ℝ) (r : ℕ) (q : Piece P r)
    (n : ℕ) (hn : n + 1 ≤ r) :
    MonotoneOn (iteratedDeriv n (q.path (index q.independent))) (Ioo q.left q.right) ∨
      AntitoneOn (iteratedDeriv n (q.path (index q.independent))) (Ioo q.left q.right) :=
  IteratedDerivativeMonotonicity.monotone_or_antitone _ q.left q.right
    (q.smooth (index q.independent)) n (q.derivative_signs (n + 1) hn)

theorem interior_bound (P : MvPolynomial (Fin 2) ℝ) (r : ℕ) (q : Piece P (r + 1))
    (δ : ℝ) (hδ : 0 < δ) (j : ℕ) (hj : 1 ≤ j) (hjr : j ≤ r) (x : ℝ)
    (hleft : q.left + δ ≤ x) (hright : x ≤ q.right - δ) :
    |iteratedDeriv j (q.path (index q.independent)) x| ≤
      (2 * ((r + 1 : ℕ) : ℝ) / δ) ^ (j - 1) :=
  IteratedDerivativeInteriorBound.interior_bound _ q.left q.right δ hδ r
    (q.smooth (index q.independent)) q.slope
    (fun n hn ↦ derivative_monotonicity P (r + 1) q n (by omega)) j hj hjr x hleft hright

theorem exists_piece_with_higher_bounds (P : MvPolynomial (Fin 2) ℝ) (hP : Irreducible P)
    (hD : 0 < P.totalDegree) (r : ℕ) (z : Fin 2 → ℝ) (hzero : eval z P = 0)
    (hnot : z ∉ GraphControlExceptions.points P (r + 1)) :
    ∃ q : Piece P (r + 1), z q.independent ∈ Ioo q.left q.right ∧
      (fun i ↦ q.path i (z q.independent)) = z ∧
      ∀ δ : ℝ, 0 < δ → ∀ j : ℕ, 1 ≤ j → j ≤ r → ∀ x : ℝ,
        q.left + δ ≤ x → x ≤ q.right - δ →
          |iteratedDeriv j (q.path (index q.independent)) x| ≤
            (2 * ((r + 1 : ℕ) : ℝ) / δ) ^ (j - 1) := by
  obtain ⟨q, hmem, hpoint⟩ := UnitSlopeNormalizedCharts.exists_at_nonexceptional P hP hD (r + 1) z hzero hnot
  exact ⟨q, hmem, hpoint, interior_bound P r q⟩

theorem exists_control_set_and_higher_bounds (P : MvPolynomial (Fin 2) ℝ) (hP : Irreducible P)
    (hD : 0 < P.totalDegree) (r : ℕ) :
    ∃ E : Finset (Fin 2 → ℝ),
      (∀ z, z ∈ E ↔ z ∈ GraphControlExceptions.points P (r + 1)) ∧
      E.card ≤ 30 * P.totalDegree ^ 2 * (r + 2) ^ 2 ∧
      ∀ z : Fin 2 → ℝ, eval z P = 0 → z ∉ E →
        ∃ q : Piece P (r + 1), z q.independent ∈ Ioo q.left q.right ∧
          (fun i ↦ q.path i (z q.independent)) = z ∧
          ∀ δ : ℝ, 0 < δ → ∀ j : ℕ, 1 ≤ j → j ≤ r → ∀ x : ℝ,
            q.left + δ ≤ x → x ≤ q.right - δ →
              |iteratedDeriv j (q.path (index q.independent)) x| ≤
                (2 * ((r + 1 : ℕ) : ℝ) / δ) ^ (j - 1) := by
  classical
  obtain ⟨E, hE, hcard⟩ := GraphControlExceptions.exists_finset P hP hD (r + 1)
  refine ⟨E, hE, ?_, ?_⟩
  · simpa only [show r + 1 + 1 = r + 2 by omega] using hcard
  · intro z hzero hnot
    exact exists_piece_with_higher_bounds P hP hD r z hzero (fun hz ↦ hnot ((hE z).mpr hz))

end PaperP1.UnitSlopeHigherDerivativeBounds
