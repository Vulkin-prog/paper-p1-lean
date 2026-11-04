module

public import PaperP1.Asymptotics.RepeatedLeftDyadicRootHostCount
public import PaperP1.Asymptotics.NonalignedDyadicRootHostCount
public import PaperP1.Asymptotics.OrdinaryDyadicRootHostCount
public import PaperP1.Arithmetic.OrdinaryRootSystemData
public import PaperP1.Asymptotics.EnlargedOffsetRegime
public import PaperP1.Arithmetic.EnlargedGridAlignment

/-! # Degree-(a,1) systems with the actual enlarged alignment exclusion

No square-class independence is assumed. Only the degree-one left branch
needs nonalignment, at a displacement radius matched to the offsets.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.EnlargedDegreeOneRootHostCount

open Finset PaperP1.HomogeneousSplitRadicalData PaperP1.SplitRadicalPointHeight

theorem uniform_hosts (C A₀ ε : ℝ) (R K : ℕ) (hA₀ : 0 ≤ A₀) (hε : 0 < ε) :
    ∃ k : ℕ, ∀ kmax ≥ k,
      UniformOrdinarySurfaceCover.UniformCover kmax K →
      (∀ M, UniformAffineCurvePointCount.UniformBound kmax M) →
      ∃ A : ℝ, 0 < A ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L W : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → 1 ≤ W → W ≤ R * (L + 1) →
      ∀ n : ℕ, k ≤ n → n ≤ kmax →
      ∀ (d : Fin n → ℤ) (I : Fin n → Finset ℤ) (j : Fin n → ℤ),
      ∀ a : ℕ, 0 < a → (∀ i, d i ≠ 0) →
        (Pairwise fun i t ↦ Disjoint (I i) (I t)) → Function.Injective j →
        (∀ i, (I i).card = a) → (∀ i, (I i).card + 1 ≤ K) →
        (∀ i, ∀ z ∈ I i, z.natAbs ≤ W) → (∀ i, (j i).natAbs ≤ W) →
        (∀ i, ((d i).natAbs : ℝ) ≤ (N : ℝ) ^ A₀) →
      ∀ F : Finset (ℤ × ℤ),
        (∀ p ∈ F, (N : ℤ) ≤ p.1 ∧ (N : ℤ) ≤ p.2 ∧ p.1.natAbs ≤ 2 * N ∧ p.2.natAbs ≤ 2 * N) →
        (∀ p ∈ F, a = 1 → ¬ CompressedTargetAlignment.Aligned R p.1.natAbs p.2.natAbs L) →
        (∀ p ∈ F, ∃ w : Fin n → ℤ,
          ∀ i, w i ^ 2 = d i * integerProduct (I i) p.1 * (p.2 + j i)) →
        (F.card : ℝ) ≤ A * (N : ℝ) ^ ε := by
  obtain ⟨D, hD, hdegree⟩ := OrdinaryDyadicRootHostCount.choose_homogenization A₀ K
  obtain ⟨kR, hkR⟩ := RepeatedLeftDyadicRootHostCount.uniform_hosts C A₀ ε K D 2 hA₀ hD hdegree hε
  obtain ⟨kS, hkS⟩ := NonalignedDyadicRootHostCount.uniform_hosts C A₀ ε K D 2 hA₀ hD hdegree hε
  obtain ⟨Nw, hw⟩ := EnlargedOffsetRegime.uniform_widths C R
  refine ⟨max kR kS, ?_⟩
  intro kmax hkkmax hCover hPila
  obtain ⟨AR, hAR, NR, hR⟩ := hkR kmax (by omega) hCover hPila
  obtain ⟨AS, hAS, NS, hS⟩ := hkS kmax (by omega) hCover hPila
  refine ⟨max AR AS, hAR.trans_le (le_max_left _ _), max NR (max NS Nw), ?_⟩
  intro N hN L W hcrit hWpos hW n hlength hcap d I j a ha hd hI hj hcard hK hiB hjB hdheight F hdyadic hnon hroots
  classical
  obtain ⟨hpoly, hheight, hWN⟩ := hw N (by omega) L W hcrit hW
  have hBN : (W : ℤ) < (N : ℤ) := by exact_mod_cast hWN
  let s := OrdinaryRootSystemData.radicands n D d I j
  let e := OrdinaryRootSystemData.indexEquiv n D d I j
  let d' := fun i ↦ d (e i)
  let I' := fun i ↦ I (e i)
  let j' := fun i ↦ j (e i)
  have hs : ∀ i, s.get i = radicand (d' i : ℚ)
      (2 * D - ((I' i).card + ({j' i} : Finset ℤ).card)) (I' i) {j' i} :=
    OrdinaryRootSystemData.get n D d I j
  have hlen : s.length = n := OrdinaryRootSystemData.length n D d I j
  have hd' (i) : d' i ≠ 0 := hd (e i)
  have hI' : Pairwise fun i t ↦ Disjoint (I' i) (I' t) :=
    fun _ _ hne ↦ hI (fun heq ↦ hne (e.injective heq))
  have hj' : Function.Injective j' := hj.comp e.injective
  have hcard' (i) : (I' i).card = a := hcard (e i)
  have hK' (i) : (I' i).card + 1 ≤ K := hK (e i)
  have hiB' (i) (z : ℤ) (hz : z ∈ I' i) : z.natAbs ≤ W := hiB (e i) z hz
  have hjB' (i) : (j' i).natAbs ≤ W := hjB (e i)
  have hdheight' (i) : ((d' i).natAbs : ℝ) ≤ (N : ℝ) ^ A₀ := hdheight (e i)
  let S := univ.biUnion I'
  let T := univ.image j'
  have hiS (i) : I' i ⊆ S := fun _ hz ↦ mem_biUnion.mpr ⟨i, mem_univ i, hz⟩
  have hjT (i) : j' i ∈ T := mem_image.mpr ⟨i, mem_univ i, rfl⟩
  have hposS (p) (hp : p ∈ F) (z : ℤ) (hz : z ∈ S) : 0 < p.1 + z := by
    obtain ⟨i, _, hzi⟩ := mem_biUnion.mp hz
    have hzabs : |z| ≤ (W : ℤ) := by
      simpa only [Int.natCast_natAbs] using (Nat.cast_le (α := ℤ)).mpr (hiB (e i) z hzi)
    have hlo := (abs_le.mp hzabs).1
    have hx := (hdyadic p hp).1
    omega
  have hposT (p) (hp : p ∈ F) (z : ℤ) (hz : z ∈ T) : 0 < p.2 + z := by
    obtain ⟨i, _, rfl⟩ := mem_image.mp hz
    have hzabs : |j' i| ≤ (W : ℤ) := by
      simpa only [Int.natCast_natAbs] using (Nat.cast_le (α := ℤ)).mpr (hjB (e i))
    have hlo := (abs_le.mp hzabs).1
    have hy := (hdyadic p hp).2.1
    omega
  have hroots' (p) (hp : p ∈ F) : ∃ w : Fin s.length → ℤ,
      ∀ i, w i ^ 2 = d' i * integerProduct (I' i) p.1 * (p.2 + j' i) := by
    obtain ⟨w, hw⟩ := hroots p hp
    exact ⟨fun i ↦ w (e i), fun i ↦ hw (e i)⟩
  by_cases ha2 : 2 ≤ a
  · have hadmiss : ∀ p ∈ F, RepeatedLeftDyadicRootHostCount.AdmissibleHost N S T p := by
      intro p hp
      exact ⟨(hdyadic p hp).1, (hdyadic p hp).2.2.2, hposS p hp, hposT p hp⟩
    have hbound := hR N (by omega) L W hcrit hWpos hpoly s (by omega) (by omega)
      d' I' j' hs a ha2 hd' hI' hj' hcard' hK' hiB' hjB' hdheight' S T hiS hjT F hadmiss
      (fun p hp ↦ (hdyadic p hp).2.2.1) hroots'
    exact hbound.trans (mul_le_mul_of_nonneg_right (le_max_left AR AS) (Real.rpow_nonneg (Nat.cast_nonneg N) ε))
  · have ha1 : a = 1 := by omega
    have hadmiss : ∀ p ∈ F, NonalignedDyadicRootHostCount.AdmissibleHost N W S T p := by
      intro p hp
      exact ⟨(hdyadic p hp).1, (hdyadic p hp).2.1, (hdyadic p hp).2.2.2,
        hposS p hp, hposT p hp, fun h ↦ hnon p hp ha1
          (EnlargedGridAlignment.of_grid hW hheight
            ((Nat.cast_nonneg N).trans (hdyadic p hp).1)
            ((Nat.cast_nonneg N).trans (hdyadic p hp).2.1) h)⟩
    have hbound := hS N (by omega) L W hcrit hWpos hpoly s (by omega) (by omega)
      d' I' j' hs a ha hd' hI' hj' hcard' hK' hiB' hjB' hdheight' S T hiS hjT F hadmiss
      (fun p hp ↦ (hdyadic p hp).2.2.1) hroots'
    exact hbound.trans (mul_le_mul_of_nonneg_right (le_max_right AR AS) (Real.rpow_nonneg (Nat.cast_nonneg N) ε))

theorem uniform_hosts_of_many (C A₀ ε : ℝ) (R K : ℕ) (hA₀ : 0 ≤ A₀) (hε : 0 < ε) :
    ∃ k : ℕ, UniformOrdinarySurfaceCover.UniformCover k K →
      (∀ M, UniformAffineCurvePointCount.UniformBound k M) →
      ∃ A : ℝ, 0 < A ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L W : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → 1 ≤ W → W ≤ R * (L + 1) →
      ∀ n : ℕ, k ≤ n →
      ∀ (d : Fin n → ℤ) (I : Fin n → Finset ℤ) (j : Fin n → ℤ),
      ∀ a : ℕ, 0 < a → (∀ i, d i ≠ 0) →
        (Pairwise fun i t ↦ Disjoint (I i) (I t)) → Function.Injective j →
        (∀ i, (I i).card = a) → (∀ i, (I i).card + 1 ≤ K) →
        (∀ i, ∀ z ∈ I i, z.natAbs ≤ W) → (∀ i, (j i).natAbs ≤ W) →
        (∀ i, ((d i).natAbs : ℝ) ≤ (N : ℝ) ^ A₀) →
      ∀ F : Finset (ℤ × ℤ),
        (∀ p ∈ F, (N : ℤ) ≤ p.1 ∧ (N : ℤ) ≤ p.2 ∧ p.1.natAbs ≤ 2 * N ∧ p.2.natAbs ≤ 2 * N) →
        (∀ p ∈ F, a = 1 → ¬ CompressedTargetAlignment.Aligned R p.1.natAbs p.2.natAbs L) →
        (∀ p ∈ F, ∃ w : Fin n → ℤ,
          ∀ i, w i ^ 2 = d i * integerProduct (I i) p.1 * (p.2 + j i)) →
        (F.card : ℝ) ≤ A * (N : ℝ) ^ ε := by
  obtain ⟨k, hk⟩ := uniform_hosts C A₀ ε R K hA₀ hε
  refine ⟨k, ?_⟩
  intro hCover hPila
  obtain ⟨A, hA, N₀, hcount⟩ := hk k le_rfl hCover hPila
  refine ⟨A, hA, N₀, ?_⟩
  intro N hN L W hcrit hWpos hW n hkn d I j a ha hd hI hj hcard hK hiB hjB hdheight F hdyadic hnon hroots
  let e : Fin k → Fin n := Fin.castLE hkn
  have he : Function.Injective e := Fin.castLE_injective hkn
  have hI' : Pairwise fun i t : Fin k ↦ Disjoint (I (e i)) (I (e t)) :=
    fun _ _ hne ↦ hI (fun heq ↦ hne (he heq))
  have hroots' (p) (hp : p ∈ F) : ∃ w : Fin k → ℤ,
      ∀ i, w i ^ 2 = d (e i) * integerProduct (I (e i)) p.1 * (p.2 + j (e i)) := by
    obtain ⟨w, hw⟩ := hroots p hp
    exact ⟨fun i ↦ w (e i), fun i ↦ hw (e i)⟩
  exact hcount N hN L W hcrit hWpos hW k le_rfl le_rfl (fun i ↦ d (e i)) (fun i ↦ I (e i)) (fun i ↦ j (e i))
    a ha (fun i ↦ hd (e i)) hI' (hj.comp he) (fun i ↦ hcard (e i)) (fun i ↦ hK (e i))
    (fun i ↦ hiB (e i)) (fun i ↦ hjB (e i)) (fun i ↦ hdheight (e i)) F hdyadic hnon hroots'

end PaperP1.EnlargedDegreeOneRootHostCount
