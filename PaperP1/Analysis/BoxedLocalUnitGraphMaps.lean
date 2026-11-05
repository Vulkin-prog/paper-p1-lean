module

public import PaperP1.Analysis.ShortCenteredAffineSegment
public import PaperP1.Analysis.AffineUnitGraphParametrization
public import Mathlib.Order.Filter.Finite

/-! # Constructed local unit-jet maps through every bounded nonexceptional point

The segment, margin and scale are conclusions. Only the actual starting point
is required to lie strictly inside the unit box.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.BoxedLocalUnitGraphMaps

open MvPolynomial Set Filter PlaneCoordinateSwap UnitSlopeNormalizedCharts AffineUnitGraphParametrization
open scoped Topology ContDiff

theorem exists_bounded_interval (P : MvPolynomial (Fin 2) ℝ) (r : ℕ) (q : Piece P (r + 1))
    (x₀ : ℝ) (hx : x₀ ∈ Ioo q.left q.right) (hbox : ∀ i, |q.path i x₀| < 1) :
    ∃ a b : ℝ, x₀ ∈ Ioo a b ∧ Ioo a b ⊆ Ioo q.left q.right ∧
      ∀ t ∈ Ioo a b, ∀ i, |q.path i t| < 1 := by
  have hc : ∀ i, ContinuousAt (q.path i) x₀ :=
    fun i ↦ (q.smooth i).continuousOn.continuousAt (isOpen_Ioo.mem_nhds hx)
  have hb : ∀ᶠ t in 𝓝 x₀, ∀ i : Fin 2, |q.path i t| < 1 :=
    Filter.eventually_all.mpr (fun i ↦ (hc i).abs.eventually_lt continuousAt_const (hbox i))
  have hn : {t : ℝ | t ∈ Ioo q.left q.right ∧ ∀ i, |q.path i t| < 1} ∈ 𝓝 x₀ :=
    Filter.inter_mem (isOpen_Ioo.mem_nhds hx) hb
  obtain ⟨a, b, hmem, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hn
  exact ⟨a, b, hmem, (fun t ht ↦ (hsub ht).1), (fun t ht ↦ (hsub ht).2)⟩

theorem exists_through_parameter (P : MvPolynomial (Fin 2) ℝ) (r : ℕ) (q : Piece P (r + 1))
    (x₀ : ℝ) (hx : x₀ ∈ Ioo q.left q.right) (hbox : ∀ i, |q.path i x₀| < 1) :
    ∃ ψ : Fin 2 → ℝ → ℝ,
      (∀ i, ContDiffOn ℝ ∞ (ψ i) (Ioo (0 : ℝ) 1)) ∧ UnitJets r ψ ∧
      (∀ t ∈ Ioo (0 : ℝ) 1, eval (fun i ↦ ψ i t) P = 0) ∧
      (fun i ↦ ψ i (1 / 2)) = (fun i ↦ q.path i x₀) ∧
      ∃ a b : ℝ, x₀ ∈ Ioo a b ∧ ∀ x ∈ Ioo a b, ∃ t ∈ Ioo (0 : ℝ) 1,
        (fun i ↦ ψ i t) = (fun i ↦ q.path i x) := by
  obtain ⟨a, b, hmem, _hsub, hbounded⟩ := exists_bounded_interval P r q x₀ hx hbox
  obtain ⟨δ, u, c, hδ, hc, hcone, hscale, hmid, hcenter, hinfo⟩ :=
    ShortCenteredAffineSegment.exists_segment q.left q.right a b x₀ hx hmem r
  have hmargin : ∀ t ∈ Ioo (0 : ℝ) 1,
      q.left + δ ≤ LocalAffineDerivativeFormula.parameter u c t ∧
        LocalAffineDerivativeFormula.parameter u c t ≤ q.right - δ :=
    fun t ht ↦ (hinfo t ht).1
  have hvalues : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ i,
      |q.path i (LocalAffineDerivativeFormula.parameter u c t)| ≤ 1 :=
    fun t ht i ↦ (hbounded _ (hinfo t ht).2 i).le
  obtain ⟨hsmooth, hjets, hequation, hcover⟩ :=
    unit_curve_parametrization P r q δ hδ u c hc hcone hscale hmargin hvalues
  refine ⟨path q u c, hsmooth, hjets, hequation, ?_, u, u + c, hcenter, hcover⟩
  change (fun i ↦ q.path i (LocalAffineDerivativeFormula.parameter u c (1 / 2))) =
    (fun i ↦ q.path i x₀)
  rw [hmid]

theorem exists_at_curve_point (P : MvPolynomial (Fin 2) ℝ) (hP : Irreducible P)
    (hD : 0 < P.totalDegree) (r : ℕ) (z : Fin 2 → ℝ) (hzero : eval z P = 0)
    (hbox : ∀ i, |z i| < 1) (hnot : z ∉ GraphControlExceptions.points P (r + 1)) :
    ∃ ψ : Fin 2 → ℝ → ℝ,
      (∀ i, ContDiffOn ℝ ∞ (ψ i) (Ioo (0 : ℝ) 1)) ∧ UnitJets r ψ ∧
      (∀ t ∈ Ioo (0 : ℝ) 1, eval (fun i ↦ ψ i t) P = 0) ∧ (fun i ↦ ψ i (1 / 2)) = z := by
  obtain ⟨q, hmem, hpoint⟩ := UnitSlopeNormalizedCharts.exists_at_nonexceptional P hP hD (r + 1) z hzero hnot
  have hqbox : ∀ i, |q.path i (z q.independent)| < 1 := by
    intro i
    change |(fun j ↦ q.path j (z q.independent)) i| < 1
    rw [hpoint]
    exact hbox i
  obtain ⟨ψ, hsmooth, hjets, hequation, hmid, _hcover⟩ :=
    exists_through_parameter P r q (z q.independent) hmem hqbox
  exact ⟨ψ, hsmooth, hjets, hequation, hmid.trans hpoint⟩

theorem exists_control_set_and_maps (P : MvPolynomial (Fin 2) ℝ) (hP : Irreducible P)
    (hD : 0 < P.totalDegree) (r : ℕ) :
    ∃ E : Finset (Fin 2 → ℝ),
      (∀ z, z ∈ E ↔ z ∈ GraphControlExceptions.points P (r + 1)) ∧
      E.card ≤ 30 * P.totalDegree ^ 2 * (r + 2) ^ 2 ∧
      ∀ z : Fin 2 → ℝ, eval z P = 0 → (∀ i, |z i| < 1) → z ∉ E →
        ∃ ψ : Fin 2 → ℝ → ℝ,
          (∀ i, ContDiffOn ℝ ∞ (ψ i) (Ioo (0 : ℝ) 1)) ∧ UnitJets r ψ ∧
          (∀ t ∈ Ioo (0 : ℝ) 1, eval (fun i ↦ ψ i t) P = 0) ∧ (fun i ↦ ψ i (1 / 2)) = z := by
  classical
  obtain ⟨E, hE, hcard⟩ := GraphControlExceptions.exists_finset P hP hD (r + 1)
  refine ⟨E, hE, ?_, ?_⟩
  · simpa only [show r + 1 + 1 = r + 2 by omega] using hcard
  · intro z hzero hbox hnot
    exact exists_at_curve_point P hP hD r z hzero hbox (fun hz ↦ hnot ((hE z).mpr hz))

end PaperP1.BoxedLocalUnitGraphMaps
