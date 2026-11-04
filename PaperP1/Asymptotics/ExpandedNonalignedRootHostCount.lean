module

public import PaperP1.Asymptotics.ExpandedGeneralRootHostCount
public import PaperP1.Asymptotics.EnlargedOffsetRegime
public import PaperP1.Arithmetic.EnlargedGridAlignment

/-! # Half-power counts with the displacement radius matched to the offset width

The original critical length and cubic slope height are retained. The
displacement exclusion grows by the fixed factor used for the actual roots.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ExpandedNonalignedRootHostCount

open PaperP1.SplitRadicalPointHeight

theorem uniform_hosts (Q : ℕ) (hQ : 1 ≤ Q) (C A₀ ε : ℝ) (R K : ℕ) (hA₀ : 0 ≤ A₀) (hε : 0 < ε) :
    ∃ D k : ℕ, 0 < D ∧ A₀ + (K : ℝ) ≤ 2 * D ∧
      (UniformSourceSurfaceCover.UniformCover k K D →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound ((D + 2).choose 2 + k) M) →
      ∃ A : ℝ, 0 < A ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L W : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → 1 ≤ W → W ≤ R * (L + 1) →
      ∀ n : ℕ, k ≤ n → ∀ (d : Fin n → ℤ) (I J : Fin n → Finset ℤ),
      (∀ i, d i ≠ 0) → (Pairwise fun i j ↦ Disjoint (I i) (I j)) →
      (Pairwise fun i j ↦ Disjoint (J i) (J j)) → (∀ i, (I i).Nonempty) → (∀ i, (J i).Nonempty) →
      (∀ i, (I i).card + (J i).card ≤ K) →
      (∀ i, ∀ z ∈ I i, z.natAbs ≤ W) → (∀ i, ∀ z ∈ J i, z.natAbs ≤ W) →
      (∀ i, ((d i).natAbs : ℝ) ≤ (N : ℝ) ^ A₀) →
      ∀ F : Finset (ℤ × ℤ),
      (∀ p ∈ F, (N : ℤ) ≤ p.1 ∧ (N : ℤ) ≤ p.2 ∧ p.1.natAbs ≤ 2 * (Q * N) ∧ p.2.natAbs ≤ 2 * (Q * N)) →
      (∀ p ∈ F, ¬ CompressedTargetAlignment.Aligned R p.1.natAbs p.2.natAbs L) →
      (∀ p ∈ F, ∃ w : Fin n → ℤ,
        ∀ i, w i ^ 2 = d i * integerProduct (I i) p.1 * integerProduct (J i) p.2) →
      (F.card : ℝ) ≤ A * (N : ℝ) ^ (1 / 2 + ε)) := by
  obtain ⟨D, k, hD, hdegree, hk⟩ :=
    ExpandedGeneralRootHostCount.uniform_hosts_of_many Q hQ C A₀ ε K 2 hA₀ hε
  obtain ⟨Nw, hw⟩ := EnlargedOffsetRegime.uniform_widths C R
  refine ⟨D, k, hD, hdegree, ?_⟩
  intro hCover hPila
  obtain ⟨A, hA, Nc, hc⟩ := hk hCover hPila
  refine ⟨A, hA, max Nc Nw, ?_⟩
  intro N hN L W hcrit hWpos hW n hn d I J hd hI hJ hneI hneJ hK hiW hjW hdheight F hdyadic hnon hroots
  obtain ⟨hpoly, hheight, hWN⟩ := hw N (by omega) L W hcrit hW
  have hWNZ : (W : ℤ) < (N : ℤ) := by exact_mod_cast hWN
  have hadmiss : ∀ p ∈ F, (W : ℤ) < p.1 ∧ (W : ℤ) < p.2 ∧
      ¬ AffineGridAlignment.Aligned W p.1 p.2 := by
    intro p hp
    obtain ⟨hX, hY, _hXu, _hYu⟩ := hdyadic p hp
    refine ⟨hWNZ.trans_le hX, hWNZ.trans_le hY, fun h ↦ hnon p hp ?_⟩
    exact EnlargedGridAlignment.of_grid hW hheight ((Nat.cast_nonneg N).trans hX)
      ((Nat.cast_nonneg N).trans hY) h
  exact hc N (by omega) L W hcrit hWpos hpoly n hn d I J hd hI hJ hneI hneJ hK hiW hjW hdheight
    F hadmiss (fun p hp ↦ ⟨(hdyadic p hp).2.2.1, (hdyadic p hp).2.2.2⟩) hroots

end PaperP1.ExpandedNonalignedRootHostCount
