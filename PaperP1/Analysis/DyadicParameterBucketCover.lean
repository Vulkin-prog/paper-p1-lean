module

public import PaperP1.Analysis.NormalizedBandBuckets
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Data.Finset.Filter

/-! # A constructed logarithmic finite cover by small dyadic parameter buckets -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.DyadicParameterBucketCover

open Set Finset DyadicGridMargins


abbrev Index (N M : ℕ) := Fin 2 × (Fin (Nat.log2 (2 * N) + 1) × Fin M)

def cluster (N M : ℕ) (a b : ℝ) (c : Index N M) (T : Finset ℝ) : Finset ℝ :=
  T.filter (fun t ↦ a + radius N c.2.1.val ≤ t ∧ t ≤ b - radius N c.2.1.val ∧
    sideDistance c.1 a b t ∈ Ico (radius N c.2.1.val) (2 * radius N c.2.1.val) ∧
    NormalizedBandBuckets.index M (radius N c.2.1.val) (sideDistance c.1 a b t) = c.2.2.val)

theorem mem_cluster (N M : ℕ) (a b : ℝ) (c : Index N M) (T : Finset ℝ) (t : ℝ) :
    t ∈ cluster N M a b c T ↔ t ∈ T ∧
      a + radius N c.2.1.val ≤ t ∧ t ≤ b - radius N c.2.1.val ∧
      sideDistance c.1 a b t ∈ Ico (radius N c.2.1.val) (2 * radius N c.2.1.val) ∧
      NormalizedBandBuckets.index M (radius N c.2.1.val) (sideDistance c.1 a b t) = c.2.2.val := by
  exact mem_filter

theorem finite_cover (N M : ℕ) (hN : 0 < N) (hM : 0 < M) (a b : ℝ) (hwidth : b - a ≤ 2)
    (T : Finset ℝ) (hT : ∀ t ∈ T, a + 1 / (N : ℝ) ≤ t ∧ t ≤ b - 1 / (N : ℝ)) :
    ∀ t ∈ T, ∃ c : Index N M, t ∈ cluster N M a b c T := by
  intro t ht
  obtain ⟨i, j, hj, hδ, _hδone, hleft, hright, hband⟩ :=
    exists_side_band N hN a b t hwidth (hT t ht).1 (hT t ht).2
  let j' : Fin (Nat.log2 (2 * N) + 1) := ⟨j, by omega⟩
  let v : Fin M := ⟨NormalizedBandBuckets.index M (radius N j) (sideDistance i a b t),
    NormalizedBandBuckets.index_lt M hM _ _ hδ hband⟩
  exact ⟨(i, j', v), mem_filter.mpr ⟨ht, hleft, hright, hband, rfl⟩⟩

theorem cluster_margin (N M : ℕ) (hN : 0 < N) (a b : ℝ) (hwidth : b - a ≤ 2)
    (c : Index N M) (T : Finset ℝ) (t : ℝ) (ht : t ∈ cluster N M a b c T) :
    0 < radius N c.2.1.val ∧ radius N c.2.1.val ≤ 1 ∧
      a + radius N c.2.1.val ≤ t ∧ t ≤ b - radius N c.2.1.val := by
  have hh := (mem_cluster N M a b c T t).mp ht
  exact ⟨radius_pos N hN _, by linarith only [hh.2.1, hh.2.2.1, hwidth], hh.2.1, hh.2.2.1⟩

theorem cluster_distance (N M : ℕ) (hN : 0 < N) (hM : 0 < M) (a b : ℝ)
    (c : Index N M) (T : Finset ℝ) (t u : ℝ)
    (ht : t ∈ cluster N M a b c T) (hu : u ∈ cluster N M a b c T) :
    |t - u| ≤ radius N c.2.1.val / (M : ℝ) := by
  have hT := (mem_cluster N M a b c T t).mp ht
  have hU := (mem_cluster N M a b c T u).mp hu
  exact NormalizedBandBuckets.side_cluster_distance M hM _ (radius_pos N hN _) c.1 a b t u
    hT.2.2.2.1 hU.2.2.2.1 (hT.2.2.2.2.trans hU.2.2.2.2.symm)

theorem index_card (N M : ℕ) : Fintype.card (Index N M) = 2 * (Nat.log2 (2 * N) + 1) * M := by
  simp only [Index, Fintype.card_prod, Fintype.card_fin]
  ring

end PaperP1.DyadicParameterBucketCover
