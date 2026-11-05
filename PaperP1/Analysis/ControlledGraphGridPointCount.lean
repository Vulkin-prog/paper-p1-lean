module

public import PaperP1.Analysis.DyadicBucketGridCount
public import PaperP1.Analysis.ControlledGraphTrimmedPopulation

/-! # Polynomial-logarithmic grid counts on an entire supplied controlled graph piece

Endpoint trimming and the height-dependent affine cover are both constructed.
No finite affine-map cover or target point-count bound is a hypothesis.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ControlledGraphGridPointCount

open MvPolynomial Set Finset UnitSlopeNormalizedCharts UnitSlopePieceRestriction MonomialWronskianExceptions
open scoped ContDiff


theorem full_count (P : MvPolynomial (Fin 2) ℝ) (r k : ℕ) (hk : 1 ≤ k)
    (q : Piece P (r + 1)) (horder : Fintype.card (TotalDegreeMonomials.Index k) - 1 ≤ r)
    (hWr : ∀ t ∈ Ioo q.left q.right, (fun i ↦ q.path i t) ∉ exceptionalPoints P k)
    (N : ℕ) (hN : 0 < N) (hlog : Real.log (N : ℝ) ≤ k)
    (S : Finset (Fin 2 → ℝ))
    (hS : ∀ w ∈ S, ∃ t ∈ Ioo q.left q.right, (fun i ↦ q.path i t) = w)
    (hbox : ∀ w ∈ S, ∀ i, |w i| ≤ 1)
    (hgrid : ∀ w ∈ S, ∃ z : Fin 2 → ℤ, ∀ i, w i = (z i : ℝ) / N) :
    (S.card : ℝ) ≤ 2 + 1024 * Real.exp 4 * ((r + 1 : ℕ) : ℝ) *
      ((Nat.log2 (2 * N) + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) ^ 8 := by
  classical
  have hB : 0 ≤ 1024 * Real.exp 4 * ((r + 1 : ℕ) : ℝ) *
      ((Nat.log2 (2 * N) + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) ^ 8 := by positivity
  by_cases hne : S.Nonempty
  · obtain ⟨a, b, ha, hb, _hab, R, hcard, hbounded, hretained⟩ :=
      ControlledGraphTrimmedPopulation.exists_trimmed_population P (r + 1) (by omega) q N hN S hne hS hbox hgrid
    by_cases hR : R.Nonempty
    · obtain ⟨t₀, ht₀⟩ := hR
      have hstep : (0 : ℝ) < 1 / (N : ℝ) := by positivity
      have hm := hretained t₀ ht₀
      have hab : a < b := by linarith only [hm.1, hm.2.1, hstep]
      have hsub : Ioo a b ⊆ Ioo q.left q.right :=
        fun _ ht ↦ ⟨ha.1.trans ht.1, ht.2.trans hb.2⟩
      let q' := restrict q a b hab hsub
      have hwidth : q'.right - q'.left ≤ 2 := by
        have hA := hbounded a ⟨le_rfl, hab.le⟩ q.independent
        have hB' := hbounded b ⟨hab.le, le_rfl⟩ q.independent
        rw [q.normalized_coordinate a ha] at hA
        rw [q.normalized_coordinate b hb] at hB'
        change b - a ≤ 2
        have hAA := abs_le.mp hA
        have hBB := abs_le.mp hB'
        linarith only [hAA.1, hBB.2]
      have hbox' : ∀ t ∈ Ioo q'.left q'.right, ∀ i, |q'.path i t| ≤ 1 :=
        fun t ht i ↦ hbounded t ⟨ht.1.le, ht.2.le⟩ i
      have hWr' : ∀ t ∈ Ioo q'.left q'.right, (fun i ↦ q'.path i t) ∉ exceptionalPoints P k :=
        fun t ht ↦ hWr t (hsub ht)
      have hmargin : ∀ t ∈ R, q'.left + 1 / (N : ℝ) ≤ t ∧ t ≤ q'.right - 1 / (N : ℝ) :=
        fun t ht ↦ ⟨(hretained t ht).1, (hretained t ht).2.1⟩
      have hgrid' : ∀ t ∈ R, ∃ z : Fin 2 → ℤ, ∀ i, q'.path i t = (z i : ℝ) / N :=
        fun t ht ↦ hgrid _ (hretained t ht).2.2.2
      let M := 16 * (r + 1)
      have hc := DyadicBucketGridCount.trimmed_count P r k hk q' horder hwidth hbox' hWr' N M hN le_rfl hlog R hmargin hgrid'
      have he : (((2 * (Nat.log2 (2 * N) + 1) * M : ℕ) : ℝ)) *
          (32 * Real.exp 4 * ((k + 1 : ℕ) : ℝ) ^ 8) =
          1024 * Real.exp 4 * ((r + 1 : ℕ) : ℝ) *
            ((Nat.log2 (2 * N) + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) ^ 8 := by
        dsimp only [M]
        push_cast
        ring
      rw [he] at hc
      have hcardR : (S.card : ℝ) ≤ (R.card : ℝ) + 2 := by exact_mod_cast hcard
      linarith only [hc, hcardR]
    · have hz : R = ∅ := not_nonempty_iff_eq_empty.mp hR
      rw [hz, Finset.card_empty] at hcard
      have hh : (S.card : ℝ) ≤ 2 := by exact_mod_cast hcard
      linarith only [hh, hB]
  · have hz : S = ∅ := not_nonempty_iff_eq_empty.mp hne
    rw [hz, Finset.card_empty, Nat.cast_zero]
    linarith only [hB]

theorem minimal_order_count (P : MvPolynomial (Fin 2) ℝ) (k : ℕ) (hk : 1 ≤ k)
    (q : Piece P ((Fintype.card (TotalDegreeMonomials.Index k) - 1) + 1))
    (hWr : ∀ t ∈ Ioo q.left q.right, (fun i ↦ q.path i t) ∉ exceptionalPoints P k)
    (N : ℕ) (hN : 0 < N) (hlog : Real.log (N : ℝ) ≤ k)
    (S : Finset (Fin 2 → ℝ))
    (hS : ∀ w ∈ S, ∃ t ∈ Ioo q.left q.right, (fun i ↦ q.path i t) = w)
    (hbox : ∀ w ∈ S, ∀ i, |w i| ≤ 1)
    (hgrid : ∀ w ∈ S, ∃ z : Fin 2 → ℤ, ∀ i, w i = (z i : ℝ) / N) :
    (S.card : ℝ) ≤ 2 + 1024 * Real.exp 4 * ((Nat.log2 (2 * N) + 1 : ℕ) : ℝ) *
      ((k + 1 : ℕ) : ℝ) ^ 10 := by
  have hh := full_count P (Fintype.card (TotalDegreeMonomials.Index k) - 1) k hk q le_rfl hWr N hN hlog S hS hbox hgrid
  have hpos : 1 ≤ Fintype.card (TotalDegreeMonomials.Index k) := (TotalDegreeMonomials.index_card_pos k)
  rw [Nat.sub_add_cancel hpos] at hh
  have hcard : (Fintype.card (TotalDegreeMonomials.Index k) : ℝ) ≤ ((k + 1 : ℕ) : ℝ) ^ 2 := by
    exact_mod_cast TotalDegreeMonomialFamily.index_card_le k
  have hc := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hcard (show (0 : ℝ) ≤ 1024 * Real.exp 4 by positivity))
      (Nat.cast_nonneg (α := ℝ) (Nat.log2 (2 * N) + 1)))
    (show (0 : ℝ) ≤ ((k + 1 : ℕ) : ℝ) ^ 8 by positivity)
  have he : 1024 * Real.exp 4 * ((k + 1 : ℕ) : ℝ) ^ 2 * ((Nat.log2 (2 * N) + 1 : ℕ) : ℝ) *
      ((k + 1 : ℕ) : ℝ) ^ 8 = 1024 * Real.exp 4 * ((Nat.log2 (2 * N) + 1 : ℕ) : ℝ) *
      ((k + 1 : ℕ) : ℝ) ^ 10 := by ring
  have hcoef := hc.trans_eq he
  linarith only [hh, hcoef]

end PaperP1.ControlledGraphGridPointCount
