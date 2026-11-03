module

public import PaperP1.Asymptotics.GeneralSourceHalfPowerUnderInputs
public import PaperP1.Asymptotics.OrdinaryDyadicRootHostCount
public import PaperP1.Arithmetic.GeneralRootSystemData

/-! # The general literal integer split-system half-power host count under explicit geometric inputs

The chosen homogeneous data are constructed. The fixed-subsystem version is
uniform in every larger equation count and permits unequal root-set degrees.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GeneralRootHostCount

open PaperP1.HomogeneousSplitRadicalData PaperP1.SplitRadicalPointHeight

theorem uniform_hosts (C A₀ ε : ℝ) (K Jexp : ℕ) (hA₀ : 0 ≤ A₀) (hε : 0 < ε) :
    ∃ D k : ℕ, 0 < D ∧ A₀ + (K : ℝ) ≤ 2 * D ∧ ∀ kmax ≥ k,
      UniformSourceSurfaceCover.UniformCover kmax K D →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound ((D + 2).choose 2 + kmax) M) →
      ∃ A : ℝ, 0 < A ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L B : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → 1 ≤ B → B ≤ (L + 1) ^ Jexp →
      ∀ n : ℕ, k ≤ n → n ≤ kmax → ∀ (d : Fin n → ℤ) (I J : Fin n → Finset ℤ),
      (∀ i, d i ≠ 0) → (Pairwise fun i j ↦ Disjoint (I i) (I j)) →
      (Pairwise fun i j ↦ Disjoint (J i) (J j)) → (∀ i, (I i).Nonempty) → (∀ i, (J i).Nonempty) →
      (∀ i, (I i).card + (J i).card ≤ K) →
      (∀ i, ∀ z ∈ I i, z.natAbs ≤ B) → (∀ i, ∀ z ∈ J i, z.natAbs ≤ B) →
      (∀ i, ((d i).natAbs : ℝ) ≤ (N : ℝ) ^ A₀) →
      ∀ S T : Finset ℤ, (∀ i, I i ⊆ S) → (∀ i, J i ⊆ T) →
      ∀ F : Finset (ℤ × ℤ), (∀ p ∈ F, SourceCurvePointCover.Admissible S T p) →
      (∀ p ∈ F, p.1.natAbs ≤ 2 * N ∧ p.2.natAbs ≤ 2 * N) →
      (∀ p ∈ F, ∃ w : Fin n → ℤ,
        ∀ i, w i ^ 2 = d i * integerProduct (I i) p.1 * integerProduct (J i) p.2) →
      (F.card : ℝ) ≤ A * (N : ℝ) ^ (1 / 2 + ε) := by
  obtain ⟨D, hD, hdegree⟩ := OrdinaryDyadicRootHostCount.choose_homogenization A₀ K
  obtain ⟨k, hk⟩ := GeneralSourceHalfPowerUnderInputs.uniform_hosts C A₀ ε K D Jexp hA₀ hD hdegree hε
  refine ⟨D, k, hD, hdegree, ?_⟩
  intro kmax hkkmax hCover hPila
  obtain ⟨A, hA, N₀, hcount⟩ := hk kmax hkkmax hCover hPila
  refine ⟨A, hA, N₀, ?_⟩
  intro N hN L B hcrit hB hBL n hlength hcap d I J hd hI hJ hneI hneJ hK hiB hjB hdheight S T hiS hjT F hadmiss hxy hroots
  let s := GeneralRootSystemData.radicands n D d I J
  let e := GeneralRootSystemData.indexEquiv n D d I J
  let d' := fun i ↦ d (e i)
  let I' := fun i ↦ I (e i)
  let J' := fun i ↦ J (e i)
  have hs : ∀ i, s.get i = radicand (d' i : ℚ) (2 * D - ((I' i).card + (J' i).card)) (I' i) (J' i) :=
    GeneralRootSystemData.get n D d I J
  have hlen : s.length = n := GeneralRootSystemData.length n D d I J
  have hI' : Pairwise fun i j ↦ Disjoint (I' i) (I' j) :=
    fun _ _ hne ↦ hI (fun heq ↦ hne (e.injective heq))
  have hJ' : Pairwise fun i j ↦ Disjoint (J' i) (J' j) :=
    fun _ _ hne ↦ hJ (fun heq ↦ hne (e.injective heq))
  have hroots' (p) (hp : p ∈ F) : ∃ w : Fin s.length → ℤ,
      ∀ i, w i ^ 2 = d' i * integerProduct (I' i) p.1 * integerProduct (J' i) p.2 := by
    obtain ⟨w, hw⟩ := hroots p hp
    exact ⟨fun i ↦ w (e i), fun i ↦ hw (e i)⟩
  exact hcount N hN L B hcrit hB hBL s (by omega) (by omega) d' I' J' hs
    (fun i ↦ hd (e i)) hI' hJ' (fun i ↦ hneI (e i)) (fun i ↦ hneJ (e i))
    (fun i ↦ hK (e i)) (fun i ↦ hiB (e i)) (fun i ↦ hjB (e i)) (fun i ↦ hdheight (e i))
    S T (fun i ↦ hiS (e i)) (fun i ↦ hjT (e i)) F hadmiss hxy hroots'

theorem uniform_hosts_of_many (C A₀ ε : ℝ) (K Jexp : ℕ) (hA₀ : 0 ≤ A₀) (hε : 0 < ε) :
    ∃ D k : ℕ, 0 < D ∧ A₀ + (K : ℝ) ≤ 2 * D ∧ (UniformSourceSurfaceCover.UniformCover k K D →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound ((D + 2).choose 2 + k) M) →
      ∃ A : ℝ, 0 < A ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L B : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → 1 ≤ B → B ≤ (L + 1) ^ Jexp →
      ∀ n : ℕ, k ≤ n → ∀ (d : Fin n → ℤ) (I J : Fin n → Finset ℤ),
      (∀ i, d i ≠ 0) → (Pairwise fun i j ↦ Disjoint (I i) (I j)) →
      (Pairwise fun i j ↦ Disjoint (J i) (J j)) → (∀ i, (I i).Nonempty) → (∀ i, (J i).Nonempty) →
      (∀ i, (I i).card + (J i).card ≤ K) →
      (∀ i, ∀ z ∈ I i, z.natAbs ≤ B) → (∀ i, ∀ z ∈ J i, z.natAbs ≤ B) →
      (∀ i, ((d i).natAbs : ℝ) ≤ (N : ℝ) ^ A₀) →
      ∀ S T : Finset ℤ, (∀ i, I i ⊆ S) → (∀ i, J i ⊆ T) →
      ∀ F : Finset (ℤ × ℤ), (∀ p ∈ F, SourceCurvePointCover.Admissible S T p) →
      (∀ p ∈ F, p.1.natAbs ≤ 2 * N ∧ p.2.natAbs ≤ 2 * N) →
      (∀ p ∈ F, ∃ w : Fin n → ℤ,
        ∀ i, w i ^ 2 = d i * integerProduct (I i) p.1 * integerProduct (J i) p.2) →
      (F.card : ℝ) ≤ A * (N : ℝ) ^ (1 / 2 + ε)) := by
  obtain ⟨D, k, hD, hdegree, hk⟩ := uniform_hosts C A₀ ε K Jexp hA₀ hε
  refine ⟨D, k, hD, hdegree, ?_⟩
  intro hCover hPila
  obtain ⟨A, hA, N₀, hcount⟩ := hk k le_rfl hCover hPila
  refine ⟨A, hA, N₀, ?_⟩
  intro N hN L B hcrit hB hBL n hkn d I J hd hI hJ hneI hneJ hK hiB hjB hdheight S T hiS hjT F hadmiss hxy hroots
  let e : Fin k → Fin n := Fin.castLE hkn
  have he : Function.Injective e := Fin.castLE_injective hkn
  have hI' : Pairwise fun i j : Fin k ↦ Disjoint (I (e i)) (I (e j)) :=
    fun _ _ hne ↦ hI (fun heq ↦ hne (he heq))
  have hJ' : Pairwise fun i j : Fin k ↦ Disjoint (J (e i)) (J (e j)) :=
    fun _ _ hne ↦ hJ (fun heq ↦ hne (he heq))
  have hroots' (p) (hp : p ∈ F) : ∃ w : Fin k → ℤ,
      ∀ i, w i ^ 2 = d (e i) * integerProduct (I (e i)) p.1 * integerProduct (J (e i)) p.2 := by
    obtain ⟨w, hw⟩ := hroots p hp
    exact ⟨fun i ↦ w (e i), fun i ↦ hw (e i)⟩
  exact hcount N hN L B hcrit hB hBL k le_rfl le_rfl (fun i ↦ d (e i)) (fun i ↦ I (e i)) (fun i ↦ J (e i))
    (fun i ↦ hd (e i)) hI' hJ' (fun i ↦ hneI (e i)) (fun i ↦ hneJ (e i)) (fun i ↦ hK (e i))
    (fun i ↦ hiB (e i)) (fun i ↦ hjB (e i)) (fun i ↦ hdheight (e i))
    S T (fun i ↦ hiS (e i)) (fun i ↦ hjT (e i)) F hadmiss hxy hroots'

end PaperP1.GeneralRootHostCount
