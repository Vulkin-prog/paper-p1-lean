module

public import PaperP1.Analysis.UnitMonomialDeterminantScale
public import PaperP1.Analysis.UnitIntervalSubdivision
public import PaperP1.Analysis.ShortIntervalGridPointCount
public import PaperP1.Combinatorics.FiniteCoverCount

/-! # Quantitative grid-point counts on an actual full unit-jet Chebyshev map

The interval length and its finite cover are constructed internally. The
result counts the entire supplied point population in the image of one map.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UnitMapGridPointCount

open MvPolynomial Set Finset TotalDegreeMonomials AffineUnitGraphParametrization
  UnitMonomialDeterminantScale UnitIntervalSubdivision
open scoped ContDiff

theorem point_count (k : ℕ) (hk : 1 ≤ k) (N : ℕ) (hN : 0 < N)
    (ψ : Fin 2 → ℝ → ℝ) (hψ : ∀ i, ContDiffOn ℝ ∞ (ψ i) (Ioo (0 : ℝ) 1))
    (hjet : UnitJets (Fintype.card (Index k) - 1) ψ)
    (hpoly : ∀ Q : MvPolynomial (Fin 2) ℝ, Q ≠ 0 → Q.totalDegree ≤ k →
      ∀ S : Finset (Fin 2 → ℝ),
        (∀ w ∈ S, (∃ t ∈ Ioo (0 : ℝ) 1, (fun i ↦ ψ i t) = w) ∧ eval w Q = 0) →
          S.card < Fintype.card (Index k))
    (S : Finset (Fin 2 → ℝ))
    (hS : ∀ w ∈ S, ∃ t ∈ Ioo (0 : ℝ) 1, (fun i ↦ ψ i t) = w)
    (hgrid : ∀ w ∈ S, ∃ z : Fin 2 → ℤ, ∀ i, w i = (z i : ℝ) / N) :
    let n := Fintype.card (Index k)
    (S.card : ℝ) ≤ 32 * (n : ℝ) ^ 3 * ((k + 1 : ℕ) : ℝ) ^ 2 *
      (N : ℝ) ^ ((((k * n : ℕ) : ℝ)) / ((n * (n - 1) / 2 : ℕ) : ℝ)) := by
  classical
  let n := Fintype.card (Index k)
  have hn : 2 ≤ n := UnitMonomialEvaluationDeterminant.index_card_two_le k hk
  let L := scale n k N
  let M := ⌈L⌉₊
  have hL : 1 ≤ L := scale_one_le n hn k N hN
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hLM : L ≤ (M : ℝ) := Nat.le_ceil L
  have hM : 0 < M := by
    have hh : (0 : ℝ) < M := hLp.trans_le hLM
    exact_mod_cast hh
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hMupper : (M : ℝ) ≤ 2 * L := by
    have hh : (M : ℝ) < L + 1 := Nat.ceil_lt_add_one hLp.le
    linarith only [hh, hL]
  have hδscale : 1 / (M : ℝ) ≤ 1 / L := one_div_le_one_div_of_le hLp hLM
  have hδone : 1 / (M : ℝ) ≤ 1 := by
    exact (div_le_one hMR).mpr (by exact_mod_cast (show 1 ≤ M by omega))
  have hsmall := smallness n hn k N hN (1 / (M : ℝ)) (one_div_pos.mpr hMR).le hδscale
  choose x hx he using fun w : S ↦ hS w.val w.property
  let bucket : (Fin 2 → ℝ) → ℕ := fun w ↦ if hw : w ∈ S then index M (x ⟨w, hw⟩) else 0
  let F : Fin M → Finset (Fin 2 → ℝ) := fun i ↦ S.filter (fun w ↦ bucket w = i.val)
  have hF : ∀ i : Fin M, ((F i).card : ℝ) ≤ n := by
    intro i
    have hFS : ∀ w ∈ F i, ∃ t ∈ Ioo (0 : ℝ) 1,
        |t - center M i| ≤ 1 / (M : ℝ) ∧ (fun a ↦ ψ a t) = w := by
      intro w hw
      have hwS : w ∈ S := (mem_filter.mp hw).1
      let v : S := ⟨w, hwS⟩
      have hb : index M (x v) = i.val := by
        have hh := (mem_filter.mp hw).2
        simpa only [bucket, dite_eq_left hwS] using hh
      exact ⟨x v, hx v, distance_bound M hM (x v) (hx v) i hb, he v⟩
    have hh := ShortIntervalGridPointCount.point_count k hk N hN ψ hψ hjet hpoly
      (center M i) (1 / (M : ℝ)) (center_mem M hM i) (one_div_pos.mpr hMR).le hδone hsmall
      (F i) hFS (fun w hw ↦ hgrid w (mem_filter.mp hw).1)
    exact_mod_cast hh.le
  have hcover : ∀ w ∈ S, ∃ i ∈ (univ : Finset (Fin M)), w ∈ F i := by
    intro w hw
    let v : S := ⟨w, hw⟩
    let i : Fin M := ⟨index M (x v), index_lt M hM (x v) (hx v)⟩
    refine ⟨i, mem_univ _, mem_filter.mpr ⟨hw, ?_⟩⟩
    exact dite_eq_left hw
  have hc := FiniteCoverCount.cardinal_le S (univ : Finset (Fin M)) F (n : ℝ) hcover (fun i _hi ↦ hF i)
  have hc' : (S.card : ℝ) ≤ (M : ℝ) * n := by
    simpa only [card_univ, Fintype.card_fin] using hc
  calc
    _ ≤ 2 * L * n := hc'.trans (mul_le_mul_of_nonneg_right hMupper (Nat.cast_nonneg _))
    _ = 32 * (n : ℝ) ^ 3 * ((k + 1 : ℕ) : ℝ) ^ 2 *
        (N : ℝ) ^ ((((k * n : ℕ) : ℝ)) / ((n * (n - 1) / 2 : ℕ) : ℝ)) := by
      dsimp only [L, scale]
      ring

end PaperP1.UnitMapGridPointCount
