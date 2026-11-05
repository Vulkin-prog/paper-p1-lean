module

public import PaperP1.Analysis.JointGraphChebyshevExceptions
public import PaperP1.Analysis.UnitSlopePieceRestriction
public import PaperP1.Analysis.UnitGraphMonomialPieceCount
public import PaperP1.Analysis.BoxedLocalUnitGraphMaps

/-! # Constructed local maps with simultaneous unit jets and polynomial zero counts

The common finite exceptional set, actual curve map and affine segment are
constructed before every tested bounded-degree polynomial and point population.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.JointLocalUnitCountingMaps

open MvPolynomial Set UnitSlopeNormalizedCharts AffineUnitGraphParametrization TotalDegreeMonomials
open scoped ContDiff

theorem exists_at_nonexceptional (P : MvPolynomial (Fin 2) ℝ) (hP : Irreducible P)
    (r k : ℕ) (hk : k < P.totalDegree) (z : Fin 2 → ℝ) (hzero : eval z P = 0)
    (hbox : ∀ i, |z i| < 1) (hnot : z ∉ JointGraphChebyshevExceptions.points P r k) :
    ∃ ψ : Fin 2 → ℝ → ℝ,
      (∀ i, ContDiffOn ℝ ∞ (ψ i) (Ioo (0 : ℝ) 1)) ∧ UnitJets r ψ ∧
      (∃ i : Fin 2, ∃ u c : ℝ, 0 < c ∧ ∀ t ∈ Ioo (0 : ℝ) 1, ψ i t = u + c * t) ∧
      InjOn (fun t ↦ fun i ↦ ψ i t) (Ioo (0 : ℝ) 1) ∧
      (∀ t ∈ Ioo (0 : ℝ) 1, eval (fun i ↦ ψ i t) P = 0) ∧
      (∀ t ∈ Ioo (0 : ℝ) 1, (fun i ↦ ψ i t) ∉ JointGraphChebyshevExceptions.points P r k) ∧
      (fun i ↦ ψ i (1 / 2)) = z ∧
      ∀ Q : MvPolynomial (Fin 2) ℝ, Q ≠ 0 → Q.totalDegree ≤ k →
        ∀ S : Finset (Fin 2 → ℝ),
          (∀ w ∈ S, (∃ t ∈ Ioo (0 : ℝ) 1, (fun i ↦ ψ i t) = w) ∧ eval w Q = 0) →
            S.card < Fintype.card (Index k) := by
  classical
  obtain ⟨E, hE, _hcard⟩ := JointGraphChebyshevExceptions.exists_finset P hP r k hk
  have hcontrol := (JointGraphChebyshevExceptions.avoids_both P r k z hnot).1
  obtain ⟨q, hmem, hpoint⟩ := UnitSlopeNormalizedCharts.exists_at_nonexceptional P hP (by omega) (r + 1) z hzero hcontrol
  let x₀ := z q.independent
  have hpoint₀ : (fun i ↦ q.path i x₀) = z := hpoint
  have hnotE : (fun i ↦ q.path i x₀) ∉ E := by
    rw [hpoint₀]
    exact fun hz ↦ hnot ((hE z).mp hz)
  obtain ⟨q', hmem', hpath, _hindex, havoid⟩ :=
    UnitSlopePieceRestriction.exists_avoiding P (r + 1) q x₀ hmem E hnotE
  have hpoint' : (fun i ↦ q'.path i x₀) = z := by rw [hpath]; exact hpoint₀
  have hnon : ∀ t ∈ Ioo q'.left q'.right,
      (fun i ↦ q'.path i t) ∉ MonomialWronskianExceptions.exceptionalPoints P k := by
    intro t ht hw
    apply havoid t ht
    exact (hE _).mpr (Or.inr (Or.inr hw))
  have hqbox : ∀ i, |q'.path i x₀| < 1 := by
    intro i
    change |(fun j ↦ q'.path j x₀) i| < 1
    rw [hpoint']
    exact hbox i
  obtain ⟨a, b, hboundedMem, _hboundedSub, hbounded⟩ :=
    BoxedLocalUnitGraphMaps.exists_bounded_interval P r q' x₀ hmem' hqbox
  obtain ⟨δ, u, c, hδ, hc, hcone, hscale, hmid, _hcenter, hinfo⟩ :=
    ShortCenteredAffineSegment.exists_segment q'.left q'.right a b x₀ hmem' hboundedMem r
  have hmargin : ∀ t ∈ Ioo (0 : ℝ) 1,
      q'.left + δ ≤ LocalAffineDerivativeFormula.parameter u c t ∧
        LocalAffineDerivativeFormula.parameter u c t ≤ q'.right - δ := fun t ht ↦ (hinfo t ht).1
  have hvalues : ∀ t ∈ Ioo (0 : ℝ) 1, ∀ i,
      |q'.path i (LocalAffineDerivativeFormula.parameter u c t)| ≤ 1 :=
    fun t ht i ↦ (hbounded _ (hinfo t ht).2 i).le
  have hmap : MapsTo (LocalAffineDerivativeFormula.parameter u c) (Ioo (0 : ℝ) 1) (Ioo q'.left q'.right) := by
    intro t ht
    have hm := hmargin t ht
    exact ⟨by linarith [hm.1], by linarith [hm.2]⟩
  obtain ⟨hsmooth, hjets, hequation, _hcover⟩ :=
    unit_curve_parametrization P r q' δ hδ u c hc hcone hscale hmargin hvalues
  refine ⟨path q' u c, hsmooth, hjets, ?_, ?_, hequation, ?_, ?_, ?_⟩
  · exact ⟨q'.independent, u, c, hc, (fun t ht ↦ q'.normalized_coordinate _ (hmap ht))⟩
  · intro t ht v hv heq
    have hcoord := congrFun heq q'.independent
    change q'.path q'.independent (LocalAffineDerivativeFormula.parameter u c t) =
      q'.path q'.independent (LocalAffineDerivativeFormula.parameter u c v) at hcoord
    rw [q'.normalized_coordinate _ (hmap ht), q'.normalized_coordinate _ (hmap hv)] at hcoord
    change u + c * t = u + c * v at hcoord
    exact mul_left_cancel₀ hc.ne' (add_left_cancel hcoord)
  · intro t ht hz
    exact havoid _ (hmap ht) ((hE _).mpr hz)
  · change (fun i ↦ q'.path i (LocalAffineDerivativeFormula.parameter u c (1 / 2))) = z
    rw [hmid]
    exact hpoint'
  · intro Q hQ hdegree S hS
    exact UnitGraphMonomialPieceCount.point_count P r k q' u c hc hmap hnon Q hQ hdegree S hS

theorem exists_control_set_and_counting_maps (P : MvPolynomial (Fin 2) ℝ) (hP : Irreducible P)
    (r k : ℕ) (hk : k < P.totalDegree) :
    ∃ E : Finset (Fin 2 → ℝ),
      (∀ z, z ∈ E ↔ z ∈ JointGraphChebyshevExceptions.points P r k) ∧
      E.card ≤ P.totalDegree ^ 2 * (30 * (r + 2) ^ 2 + 3 * (k + 1) ^ 6) ∧
      ∀ z : Fin 2 → ℝ, eval z P = 0 → (∀ i, |z i| < 1) → z ∉ E →
        ∃ ψ : Fin 2 → ℝ → ℝ,
          (∀ i, ContDiffOn ℝ ∞ (ψ i) (Ioo (0 : ℝ) 1)) ∧ UnitJets r ψ ∧
          (∃ i : Fin 2, ∃ u c : ℝ, 0 < c ∧ ∀ t ∈ Ioo (0 : ℝ) 1, ψ i t = u + c * t) ∧
          InjOn (fun t ↦ fun i ↦ ψ i t) (Ioo (0 : ℝ) 1) ∧
          (∀ t ∈ Ioo (0 : ℝ) 1, eval (fun i ↦ ψ i t) P = 0) ∧
          (∀ t ∈ Ioo (0 : ℝ) 1, (fun i ↦ ψ i t) ∉ JointGraphChebyshevExceptions.points P r k) ∧
          (fun i ↦ ψ i (1 / 2)) = z ∧
          ∀ Q : MvPolynomial (Fin 2) ℝ, Q ≠ 0 → Q.totalDegree ≤ k →
            ∀ S : Finset (Fin 2 → ℝ),
              (∀ w ∈ S, (∃ t ∈ Ioo (0 : ℝ) 1, (fun i ↦ ψ i t) = w) ∧ eval w Q = 0) →
                S.card < Fintype.card (Index k) := by
  classical
  obtain ⟨E, hE, hcard⟩ := JointGraphChebyshevExceptions.exists_finset P hP r k hk
  refine ⟨E, hE, hcard, ?_⟩
  intro z hzero hbox hnot
  exact exists_at_nonexceptional P hP r k hk z hzero hbox (fun hz ↦ hnot ((hE z).mpr hz))

end PaperP1.JointLocalUnitCountingMaps
