module

public import PaperP1.Asymptotics.SelectedDegreeOneRootHostCount
public import PaperP1.Combinatorics.FiniteDegreeSelection

/-! # The selected degree-one count is uniform in larger systems and varying degrees

Offsets may range over any fixed polynomial enlargement of the critical
window. The retained subsystem and every geometric input are fixed before
the original equation count, coefficients and actual host population.
Only the selected left even-selection map must be injective; the right
selected space need only be disjoint from its image.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SelectedDegreeOneSystems

open Finset PaperP1.HomogeneousSplitRadicalData PaperP1.SplitRadicalPointHeight

theorem uniform_hosts (C A₀ ε : ℝ) (K Jexp : ℕ) (hA₀ : 0 ≤ A₀) (hε : 0 < ε) :
    ∃ k : ℕ, 1 ≤ k ∧ (UniformOrdinarySurfaceCover.UniformCover k K →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound (k + 3) M) →
      ∃ A : ℝ, 0 < A ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L B : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → 1 ≤ B → B ≤ (L + 1) ^ Jexp →
      ∀ (d : Fin k → ℤ) (I : Fin k → Finset ℤ) (j : Fin k → ℤ),
      ∀ a : ℕ, 0 < a → (∀ i, d i ≠ 0) →
        (Pairwise fun i t ↦ Disjoint (I i) (I t)) → Function.Injective j →
        (∀ i, (I i).card = a) → (∀ i, (I i).card + 1 ≤ K) →
        (∀ i, ∀ z ∈ I i, z.natAbs ≤ B) → (∀ i, (j i).natAbs ≤ B) →
        (∀ i, ((d i).natAbs : ℝ) ≤ (N : ℝ) ^ A₀) →
      ∀ S T : Finset ℤ, (∀ i, I i ⊆ S) → (∀ i, j i ∈ T) →
      ∀ F : Finset (ℤ × ℤ),
        (∀ p ∈ F, (N : ℤ) ≤ p.1 ∧ (N : ℤ) ≤ p.2 ∧ p.1.natAbs ≤ 2 * N ∧ p.2.natAbs ≤ 2 * N) →
        (∀ p ∈ F, OrdinaryDyadicRootHostCount.AdmissibleHost N S T p) →
        (∀ p ∈ F, ∃ w : Fin k → ℤ,
          ∀ i, w i ^ 2 = d i * integerProduct (I i) p.1 * (p.2 + j i)) →
        (F.card : ℝ) ≤ A * (N : ℝ) ^ ε) := by
  obtain ⟨D, hD, hdegree⟩ := OrdinaryDyadicRootHostCount.choose_homogenization A₀ K
  obtain ⟨k₀, hk⟩ := OrdinaryDyadicRootHostCount.uniform_hosts C A₀ ε K D Jexp hA₀ hD hdegree hε
  let k := k₀ + 1
  refine ⟨k, by dsimp [k]; omega, ?_⟩
  intro hCover hCurve
  obtain ⟨A, hA, N₀, hc⟩ := hk k (by dsimp [k]; omega) hCover
    (fun M ↦ UniformNormalizedCurvePointCount.ordinary_specialization k M (hCurve M))
  refine ⟨A, hA, N₀, ?_⟩
  intro N hN L B hband hB hBL d I j a ha hd hI hj hcard hK hiB hjB hdheight S T hiS hjT F hdyadic hadmiss hroots
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
    fun _ _ hne ↦ hI (e.injective.ne hne)
  have hj' : Function.Injective j' := hj.comp e.injective
  have hroots' : ∀ p ∈ F, ∃ w : Fin s.length → ℤ,
      ∀ i, w i ^ 2 = d' i * integerProduct (I' i) p.1 * (p.2 + j' i) := by
    intro p hp
    obtain ⟨w, hw⟩ := hroots p hp
    exact ⟨fun i ↦ w (e i), fun i ↦ hw (e i)⟩
  exact hc N hN L B hband hB hBL s (by rw [hlen]; dsimp [k]; omega)
    (by rw [hlen]) d' I' j' hs a ha (fun i ↦ hd (e i)) hI' hj' (fun i ↦ hcard (e i))
    (fun i ↦ hK (e i)) (fun i ↦ hiB (e i)) (fun i ↦ hjB (e i)) (fun i ↦ hdheight (e i))
    S T (fun i ↦ hiS (e i)) (fun i ↦ hjT (e i)) F hadmiss
    (fun p hp ↦ (hdyadic p hp).2.2.1) hroots'

theorem uniform_varying (C A₀ ε : ℝ) (K Jexp : ℕ) (hA₀ : 0 ≤ A₀) (hε : 0 < ε) :
    ∃ k : ℕ, 1 ≤ k ∧ (UniformOrdinarySurfaceCover.UniformCover k K →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound (k + 3) M) →
      ∃ A : ℝ, 0 < A ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L B : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → 1 ≤ B → B ≤ (L + 1) ^ Jexp →
      ∀ n : ℕ, (K + 1) * k ≤ n →
      ∀ (d : Fin n → ℤ) (I : Fin n → Finset ℤ) (j : Fin n → ℤ),
        (∀ i, d i ≠ 0) → (Pairwise fun i t ↦ Disjoint (I i) (I t)) → Function.Injective j →
        (∀ i, (I i).Nonempty) → (∀ i, (I i).card + 1 ≤ K) →
        (∀ i, ∀ z ∈ I i, z.natAbs ≤ B) → (∀ i, (j i).natAbs ≤ B) →
        (∀ i, ((d i).natAbs : ℝ) ≤ (N : ℝ) ^ A₀) →
      ∀ S T : Finset ℤ, (∀ i, I i ⊆ S) → (∀ i, j i ∈ T) →
      ∀ F : Finset (ℤ × ℤ),
        (∀ p ∈ F, (N : ℤ) ≤ p.1 ∧ (N : ℤ) ≤ p.2 ∧ p.1.natAbs ≤ 2 * N ∧ p.2.natAbs ≤ 2 * N) →
        (∀ p ∈ F, OrdinaryDyadicRootHostCount.AdmissibleHost N S T p) →
        (∀ p ∈ F, ∃ w : Fin n → ℤ,
          ∀ i, w i ^ 2 = d i * integerProduct (I i) p.1 * (p.2 + j i)) →
        (F.card : ℝ) ≤ A * (N : ℝ) ^ ε) := by
  obtain ⟨k, hk, hp⟩ := uniform_hosts C A₀ ε K Jexp hA₀ hε
  refine ⟨k, hk, ?_⟩
  intro hCover hCurve
  obtain ⟨A, hA, N₀, hc⟩ := hp hCover hCurve
  refine ⟨A, hA, N₀, ?_⟩
  intro N hN L B hband hB hBL n hn d I j hd hI hj hneI hK hiB hjB hdheight S T hiS hjT F hdyadic hadmiss hroots
  obtain ⟨a, ha, _haK, f, hf, hcard⟩ := FiniteDegreeSelection.select (by omega) hn
    (fun i ↦ (I i).card) (fun i ↦ ⟨(hneI i).card_pos, by have hh := hK i; omega⟩)
  have hI' : Pairwise fun i t : Fin k ↦ Disjoint (I (f i)) (I (f t)) :=
    fun _ _ hne ↦ hI (hf.ne hne)
  have hroots' (p : ℤ × ℤ) (hp : p ∈ F) : ∃ w : Fin k → ℤ,
      ∀ i, w i ^ 2 = d (f i) * integerProduct (I (f i)) p.1 * (p.2 + j (f i)) := by
    obtain ⟨w, hw⟩ := hroots p hp
    exact ⟨fun i ↦ w (f i), fun i ↦ hw (f i)⟩
  exact hc N hN L B hband hB hBL (fun i ↦ d (f i)) (fun i ↦ I (f i)) (fun i ↦ j (f i))
    a ha (fun i ↦ hd (f i)) hI' (hj.comp hf) hcard (fun i ↦ hK (f i))
    (fun i ↦ hiB (f i)) (fun i ↦ hjB (f i)) (fun i ↦ hdheight (f i))
    S T (fun i ↦ hiS (f i)) (fun i ↦ hjT (f i)) F hdyadic hadmiss hroots'

end PaperP1.SelectedDegreeOneSystems
