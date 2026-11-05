module

public import PaperP1.Analysis.AffineBucketWindow
public import PaperP1.Analysis.DyadicParameterBucketCover
public import PaperP1.Analysis.UnitGraphMonomialPieceCount

/-! # Constructed genuine affine unit-jet maps covering each actual dyadic bucket -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ActualDyadicBucketMaps

open MvPolynomial Set Finset UnitSlopeNormalizedCharts LocalAffineDerivativeFormula
  AffineUnitGraphParametrization MonomialWronskianExceptions DyadicGridMargins DyadicParameterBucketCover
open scoped ContDiff


theorem exists_map (P : MvPolynomial (Fin 2) ℝ) (r k : ℕ) (q : Piece P (r + 1))
    (hwidth : q.right - q.left ≤ 2) (hbox : ∀ t ∈ Ioo q.left q.right, ∀ i, |q.path i t| ≤ 1)
    (hWr : ∀ t ∈ Ioo q.left q.right, (fun i ↦ q.path i t) ∉ exceptionalPoints P k)
    (N M : ℕ) (hN : 0 < N) (hM : 16 * (r + 1) ≤ M)
    (d : Index N M) (T : Finset ℝ) (hne : (cluster N M q.left q.right d T).Nonempty) :
    ∃ u c : ℝ, 0 < c ∧
      (∀ i, ContDiffOn ℝ ∞ (path q u c i) (Ioo (0 : ℝ) 1)) ∧ UnitJets r (path q u c) ∧
      (∀ v ∈ Ioo (0 : ℝ) 1, eval (fun i ↦ path q u c i v) P = 0) ∧
      (∀ t ∈ cluster N M q.left q.right d T, ∃ v ∈ Ioo (0 : ℝ) 1,
        (fun i ↦ path q u c i v) = (fun i ↦ q.path i t)) ∧
      ∀ Q : MvPolynomial (Fin 2) ℝ, Q ≠ 0 → Q.totalDegree ≤ k →
        ∀ S : Finset (Fin 2 → ℝ),
          (∀ w ∈ S, (∃ v ∈ Ioo (0 : ℝ) 1, (fun i ↦ path q u c i v) = w) ∧ eval w Q = 0) →
            S.card < Fintype.card (TotalDegreeMonomials.Index k) := by
  have hMpos : 0 < M := by omega
  obtain ⟨t₀, ht₀⟩ := hne
  obtain ⟨hδ, hδone, hleft, hright⟩ := cluster_margin N M hN q.left q.right hwidth d T t₀ ht₀
  obtain ⟨u, c, hc, hcone, hscale, _hmid, hmargin, hcover⟩ :=
    AffineBucketWindow.exists_window r M hM q.left q.right t₀ (radius N d.2.1.val) hδ hδone hleft hright
  have hmap : MapsTo (parameter u c) (Ioo (0 : ℝ) 1) (Ioo q.left q.right) := by
    intro v hv
    have hh := hmargin v hv
    exact ⟨by linarith only [hh.1, hδ], by linarith only [hh.2, hδ]⟩
  have hvalues : ∀ v ∈ Ioo (0 : ℝ) 1, ∀ i, |q.path i (parameter u c v)| ≤ 1 :=
    fun v hv i ↦ hbox _ (hmap hv) i
  obtain ⟨hsmooth, hjets, hcurve, _himage⟩ := unit_curve_parametrization P r q (radius N d.2.1.val / 2)
    (by positivity) u c hc hcone hscale hmargin hvalues
  refine ⟨u, c, hc, hsmooth, hjets, hcurve, ?_, ?_⟩
  · intro t ht
    obtain ⟨v, hv, he⟩ := hcover t (cluster_distance N M hN hMpos q.left q.right d T t t₀ ht ht₀)
    refine ⟨v, hv, ?_⟩
    change (fun i ↦ q.path i (parameter u c v)) = (fun i ↦ q.path i t)
    rw [he]
  · intro Q hQ hdegree S hS
    exact UnitGraphMonomialPieceCount.point_count P r k q u c hc hmap hWr Q hQ hdegree S hS

end PaperP1.ActualDyadicBucketMaps
