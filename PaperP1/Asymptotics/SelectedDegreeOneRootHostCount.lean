module

public import PaperP1.Asymptotics.OrdinaryDyadicRootHostCount
public import PaperP1.Asymptotics.SourceCurvePointCover
public import PaperP1.Arithmetic.OrdinaryRootSystemData
public import PaperP1.Arithmetic.UniformNormalizedCurvePointCount

/-! # A literal degree-one system on actual selected admissible grids has subpower many hosts -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SelectedDegreeOneRootHostCount

open Finset PaperP1.HomogeneousSplitRadicalData PaperP1.SplitRadicalPointHeight

theorem uniform_hosts (C A₀ ε : ℝ) (K : ℕ) (hA₀ : 0 ≤ A₀) (hε : 0 < ε) :
    ∃ k : ℕ, 1 ≤ k ∧ (UniformOrdinarySurfaceCover.UniformCover k K →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound (k + 3) M) →
      ∃ A : ℝ, 0 < A ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ (d : Fin k → ℤ) (I : Fin k → Finset ℤ) (j : Fin k → ℤ),
      ∀ a : ℕ, 0 < a → (∀ i, d i ≠ 0) →
        (Pairwise fun i t ↦ Disjoint (I i) (I t)) → Function.Injective j →
        (∀ i, (I i).card = a) → (∀ i, (I i).card + 1 ≤ K) →
        (∀ i, ∀ z ∈ I i, z.natAbs ≤ L + 1) → (∀ i, (j i).natAbs ≤ L + 1) →
        (∀ i, ((d i).natAbs : ℝ) ≤ (N : ℝ) ^ A₀) →
      ∀ S T : Finset ℤ, (∀ i, I i ⊆ S) → (∀ i, j i ∈ T) →
      ∀ F : Finset (ℤ × ℤ),
        (∀ p ∈ F, (N : ℤ) ≤ p.1 ∧ (N : ℤ) ≤ p.2 ∧ p.1.natAbs ≤ 2 * N ∧ p.2.natAbs ≤ 2 * N) →
        (∀ p ∈ F, SourceCurvePointCover.Admissible S T p) →
        (∀ p ∈ F, ∃ w : Fin k → ℤ,
          ∀ i, w i ^ 2 = d i * integerProduct (I i) p.1 * (p.2 + j i)) →
        (F.card : ℝ) ≤ A * (N : ℝ) ^ ε) := by
  obtain ⟨D, hD, hdegree⟩ := OrdinaryDyadicRootHostCount.choose_homogenization A₀ K
  obtain ⟨k₀, hk⟩ := OrdinaryDyadicRootHostCount.uniform_hosts C A₀ ε K D 1 hA₀ hD hdegree hε
  let k := k₀ + 1
  refine ⟨k, by dsimp [k]; omega, ?_⟩
  intro hCover hPila
  obtain ⟨A, hA, N₀, hc⟩ := hk k (by dsimp [k]; omega) hCover
    (fun M ↦ UniformNormalizedCurvePointCount.ordinary_specialization k M (hPila M))
  refine ⟨A, hA, N₀, ?_⟩
  intro N hN L hcrit d I j a ha hd hI hj hcard hK hiB hjB hdheight S T hiS hjT F hdyadic hadmiss hroots
  let s := OrdinaryRootSystemData.radicands k D d I j
  let e := OrdinaryRootSystemData.indexEquiv k D d I j
  let d' := fun i ↦ d (e i)
  let I' := fun i ↦ I (e i)
  let j' := fun i ↦ j (e i)
  have hs : ∀ i, s.get i = radicand (d' i : ℚ)
      (2 * D - ((I' i).card + ({j' i} : Finset ℤ).card)) (I' i) {j' i} :=
    OrdinaryRootSystemData.get k D d I j
  have hlen : s.length = k := OrdinaryRootSystemData.length k D d I j
  have hI' : Pairwise fun i t ↦ Disjoint (I' i) (I' t) :=
    fun _ _ hne ↦ hI (fun h ↦ hne (e.injective h))
  have hj' : Function.Injective j' := hj.comp e.injective
  have hAdmiss : ∀ p ∈ F, OrdinaryDyadicRootHostCount.AdmissibleHost N S T p := by
    intro p hp
    have hd := hdyadic p hp
    have hg := hadmiss p hp
    exact ⟨hd.1, hd.2.2.2, hg.1, hg.2.1, hg.2.2.1, hg.2.2.2.2⟩
  have hroots' : ∀ p ∈ F, ∃ w : Fin s.length → ℤ,
      ∀ i, w i ^ 2 = d' i * integerProduct (I' i) p.1 * (p.2 + j' i) := by
    intro p hp
    obtain ⟨w, hw⟩ := hroots p hp
    exact ⟨fun i ↦ w (e i), fun i ↦ hw (e i)⟩
  exact hc N hN L (L + 1) hcrit (by omega) (by simp) s (by rw [hlen]; dsimp [k]; omega)
    (by rw [hlen]) d' I' j' hs a ha (fun i ↦ hd (e i)) hI' hj' (fun i ↦ hcard (e i))
    (fun i ↦ hK (e i)) (fun i ↦ hiB (e i)) (fun i ↦ hjB (e i)) (fun i ↦ hdheight (e i))
    S T (fun i ↦ hiS (e i)) (fun i ↦ hjT (e i)) F hAdmiss
    (fun p hp ↦ (hdyadic p hp).2.2.1) hroots'

end PaperP1.SelectedDegreeOneRootHostCount
