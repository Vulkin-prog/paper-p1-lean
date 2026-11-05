module

public import PaperP1.Analysis.ActualDyadicBucketMaps
public import PaperP1.Analysis.SimplifiedUnitMapGridCount
public import PaperP1.Analysis.ControlledGraphParameterPopulation
public import PaperP1.Combinatorics.FiniteCoverCount

/-! # Actual grid counts for the constructed dyadic buckets and their finite cover -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DyadicBucketGridCount

open MvPolynomial Set Finset UnitSlopeNormalizedCharts AffineUnitGraphParametrization
  MonomialWronskianExceptions DyadicGridMargins DyadicParameterBucketCover
open scoped ContDiff


theorem cluster_count (P : MvPolynomial (Fin 2) ℝ) (r k : ℕ) (hk : 1 ≤ k)
    (q : Piece P (r + 1)) (horder : Fintype.card (TotalDegreeMonomials.Index k) - 1 ≤ r)
    (hwidth : q.right - q.left ≤ 2) (hbox : ∀ t ∈ Ioo q.left q.right, ∀ i, |q.path i t| ≤ 1)
    (hWr : ∀ t ∈ Ioo q.left q.right, (fun i ↦ q.path i t) ∉ exceptionalPoints P k)
    (N M : ℕ) (hN : 0 < N) (hM : 16 * (r + 1) ≤ M) (hlog : Real.log (N : ℝ) ≤ k)
    (d : Index N M) (T : Finset ℝ)
    (hgrid : ∀ t ∈ T, ∃ z : Fin 2 → ℤ, ∀ i, q.path i t = (z i : ℝ) / N) :
    ((cluster N M q.left q.right d T).card : ℝ) ≤ 32 * Real.exp 4 * ((k + 1 : ℕ) : ℝ) ^ 8 := by
  classical
  by_cases hne : (cluster N M q.left q.right d T).Nonempty
  · obtain ⟨u, c, _hc, hsmooth, hjets, _hcurve, hcover, hpoly⟩ :=
      ActualDyadicBucketMaps.exists_map P r k q hwidth hbox hWr N M hN hM d T hne
    let C := cluster N M q.left q.right d T
    let S := C.image (fun t ↦ fun i ↦ q.path i t)
    have hmem (t : ℝ) (ht : t ∈ C) : t ∈ Ioo q.left q.right := by
      have hh := cluster_margin N M hN q.left q.right hwidth d T t ht
      exact ⟨by linarith only [hh.1, hh.2.2.1], by linarith only [hh.1, hh.2.2.2]⟩
    have hinj : InjOn (fun t ↦ fun i ↦ q.path i t) (C : Set ℝ) := by
      intro t ht v hv he
      exact ControlledGraphParameterPopulation.pointMap_injective P (r + 1) q (hmem t ht) (hmem v hv) he
    have hcard : S.card = C.card := card_image_of_injOn hinj
    have hS : ∀ w ∈ S, ∃ v ∈ Ioo (0 : ℝ) 1, (fun i ↦ path q u c i v) = w := by
      intro w hw
      obtain ⟨t, ht, rfl⟩ := mem_image.mp hw
      exact hcover t ht
    have hSgrid : ∀ w ∈ S, ∃ z : Fin 2 → ℤ, ∀ i, w i = (z i : ℝ) / N := by
      intro w hw
      obtain ⟨t, ht, rfl⟩ := mem_image.mp hw
      exact hgrid t ((mem_cluster N M q.left q.right d T t).mp ht).1
    have hjet : UnitJets (Fintype.card (TotalDegreeMonomials.Index k) - 1) (path q u c) :=
      fun i j hj t ht ↦ hjets i j (hj.trans horder) t ht
    have hh := SimplifiedUnitMapGridCount.logarithmic_point_count k hk N hN hlog
      (path q u c) hsmooth hjet hpoly S hS hSgrid
    rw [hcard] at hh
    exact hh
  · have hz : cluster N M q.left q.right d T = ∅ := not_nonempty_iff_eq_empty.mp hne
    rw [hz, Finset.card_empty, Nat.cast_zero]
    positivity

theorem trimmed_count (P : MvPolynomial (Fin 2) ℝ) (r k : ℕ) (hk : 1 ≤ k)
    (q : Piece P (r + 1)) (horder : Fintype.card (TotalDegreeMonomials.Index k) - 1 ≤ r)
    (hwidth : q.right - q.left ≤ 2) (hbox : ∀ t ∈ Ioo q.left q.right, ∀ i, |q.path i t| ≤ 1)
    (hWr : ∀ t ∈ Ioo q.left q.right, (fun i ↦ q.path i t) ∉ exceptionalPoints P k)
    (N M : ℕ) (hN : 0 < N) (hM : 16 * (r + 1) ≤ M) (hlog : Real.log (N : ℝ) ≤ k)
    (T : Finset ℝ)
    (hmargin : ∀ t ∈ T, q.left + 1 / (N : ℝ) ≤ t ∧ t ≤ q.right - 1 / (N : ℝ))
    (hgrid : ∀ t ∈ T, ∃ z : Fin 2 → ℤ, ∀ i, q.path i t = (z i : ℝ) / N) :
    (T.card : ℝ) ≤ (((2 * (Nat.log2 (2 * N) + 1) * M : ℕ) : ℝ)) *
      (32 * Real.exp 4 * ((k + 1 : ℕ) : ℝ) ^ 8) := by
  classical
  have hcover := finite_cover N M hN (show 0 < M by omega) q.left q.right hwidth T hmargin
  have hh := FiniteCoverCount.cardinal_le T (univ : Finset (Index N M))
    (fun d ↦ cluster N M q.left q.right d T) (32 * Real.exp 4 * ((k + 1 : ℕ) : ℝ) ^ 8)
    (fun t ht ↦ by obtain ⟨d, hd⟩ := hcover t ht; exact ⟨d, mem_univ _, hd⟩)
    (fun d _hd ↦ cluster_count P r k hk q horder hwidth hbox hWr N M hN hM hlog d T hgrid)
  simpa only [card_univ, index_card] using hh

end PaperP1.DyadicBucketGridCount
