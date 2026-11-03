module

public import PaperP1.Asymptotics.NonalignedSurfaceSubpowerUnderInputs
public import PaperP1.Asymptotics.CriticalPolynomialScale
public import PaperP1.Arithmetic.OrdinaryRootPointHeight

/-! # Nonaligned literal integer hosts have a conditional subpower count without independence -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.NonalignedDyadicRootHostCount

open Finset PaperP1.HomogeneousSplitRadicalData PaperP1.SplitRadicalPointHeight
  PaperP1.OrdinaryIntegerPoints PaperP1.SelectedProportionalPairs

def AdmissibleHost (N B : ℕ) (S T : Finset ℤ) (p : ℤ × ℤ) : Prop :=
  (N : ℤ) ≤ p.1 ∧ (N : ℤ) ≤ p.2 ∧ p.2.natAbs ≤ 2 * N ∧
    (∀ z ∈ S, 0 < p.1 + z) ∧ (∀ z ∈ T, 0 < p.2 + z) ∧
    ¬ AffineGridAlignment.Aligned B p.1 p.2

theorem uniform_hosts (C A₀ ε : ℝ) (K D J : ℕ) (hA₀ : 0 ≤ A₀) (hD : 0 < D)
    (hdegree : A₀ + (K : ℝ) ≤ 2 * D) (hε : 0 < ε) :
    ∃ k : ℕ, ∀ kmax ≥ k,
      UniformOrdinarySurfaceCover.UniformCover kmax K →
      (∀ M, UniformAffineCurvePointCount.UniformBound kmax M) →
      ∃ A : ℝ, 0 < A ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L B : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → 1 ≤ B → B ≤ (L + 1) ^ J →
      ∀ s : List (PolynomialRing ℚ), k ≤ s.length → s.length ≤ kmax →
      ∀ (d : Fin s.length → ℤ) (I : Fin s.length → Finset ℤ) (j : Fin s.length → ℤ),
      let c : Fin s.length → ℚ := fun i ↦ (d i : ℚ)
      let J₀ : Fin s.length → Finset ℤ := fun i ↦ {j i}
      ∀ (_hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J₀ i).card)) (I i) (J₀ i)),
      ∀ a : ℕ, 0 < a → (∀ i, d i ≠ 0) →
        (Pairwise fun i t ↦ Disjoint (I i) (I t)) → Function.Injective j →
        (∀ i, (I i).card = a) → (∀ i, (I i).card + 1 ≤ K) →
        (∀ i, ∀ z ∈ I i, z.natAbs ≤ B) → (∀ i, (j i).natAbs ≤ B) →
        (∀ i, ((d i).natAbs : ℝ) ≤ (N : ℝ) ^ A₀) →
      ∀ S T : Finset ℤ, (∀ i, I i ⊆ S) → (∀ i, j i ∈ T) →
      ∀ F : Finset (ℤ × ℤ), (∀ p ∈ F, AdmissibleHost N B S T p) →
        (∀ p ∈ F, p.1.natAbs ≤ 2 * N) →
        (∀ p ∈ F, ∃ w : Fin s.length → ℤ,
          ∀ i, w i ^ 2 = d i * integerProduct (I i) p.1 * (p.2 + j i)) →
        (F.card : ℝ) ≤ A * (N : ℝ) ^ ε := by
  obtain ⟨k, hk⟩ := NonalignedSurfaceSubpowerUnderInputs.uniform_subpower C (D : ℝ)
    (OrdinaryRootPointHeight.constant K D) ε K J (Nat.cast_nonneg D) (OrdinaryRootPointHeight.constant_ge_one K D) hε
  obtain ⟨Noff, hoff⟩ := CriticalPolynomialScale.polynomial_lt_scale C 1 (by norm_num) J
  refine ⟨k, ?_⟩
  intro kmax hkkmax hCover hPila
  obtain ⟨A, hA, Ncount, hcount⟩ := hk kmax hkkmax hCover hPila
  refine ⟨A, hA, max 1 (max Ncount Noff), ?_⟩
  intro N hN L B hcrit hB hBL s hlength hcap d I j c J₀ hs a ha hd hI hj hcard hK hiB hjB hdheight S T hiS hjT F hadmiss hXupper hroots
  classical
  have hNpos : 1 ≤ N := by omega
  have hpolyR : ((L + 1 : ℕ) : ℝ) ^ J < (N : ℝ) := by
    simpa only [one_mul] using hoff N (by omega) L hcrit
  have hpoly : (L + 1) ^ J < N := by exact_mod_cast hpolyR
  have hBN : B ≤ N := hBL.trans hpoly.le
  have hiN (i : Fin s.length) (z : ℤ) (hz : z ∈ I i) : z.natAbs ≤ N := (hiB i z hz).trans hBN
  have hjN (i : Fin s.length) (z : ℤ) (hz : z ∈ J₀ i) : z.natAbs ≤ N := by
    have hzi : z = j i := mem_singleton.mp hz
    exact hzi ▸ (hjB i).trans hBN
  have hK₂ : K ≤ 2 * D := by
    have h : (K : ℝ) ≤ 2 * D := by linarith
    exact_mod_cast h
  have hmin (i : Fin s.length) : 2 ≤ (I i).card + (J₀ i).card := by
    change 2 ≤ (I i).card + ({j i} : Finset ℤ).card
    rw [card_singleton, hcard i]
    omega
  have hdeg (i : Fin s.length) : (I i).card + (J₀ i).card ≤ 2 * D := by
    change (I i).card + ({j i} : Finset ℤ).card ≤ 2 * D
    rw [card_singleton]
    exact (hK i).trans hK₂
  have hK' (i : Fin s.length) : (I i).card + (J₀ i).card ≤ K := by
    change (I i).card + ({j i} : Finset ℤ).card ≤ K
    rw [card_singleton]
    exact hK i
  have hexists (p : ℤ × ℤ) : ∃ w : Fin s.length → ℤ,
      p ∈ F → ∀ i, w i ^ 2 = d i * integerProduct (I i) p.1 * (p.2 + j i) := by
    by_cases hp : p ∈ F
    · obtain ⟨w, hw⟩ := hroots p hp
      exact ⟨w, fun _ ↦ hw⟩
    · exact ⟨fun _ ↦ 0, fun h ↦ (hp h).elim⟩
  choose w hw using hexists
  have hw' (p : ℤ × ℤ) (hp : p ∈ F) (i : Fin s.length) :
      w p i ^ 2 = d i * integerProduct (I i) p.1 * integerProduct (J₀ i) p.2 := by
    simpa [J₀, integerProduct] using hw p hp i
  let R := OrdinaryRootPointHeight.constant K D * (N : ℝ) ^ D
  let H := ⌊R⌋₊
  have hR : 1 ≤ R := by
    have hC := OrdinaryRootPointHeight.constant_ge_one K D
    have hNp : (1 : ℝ) ≤ (N : ℝ) ^ D := one_le_pow₀ (by exact_mod_cast hNpos)
    dsimp [R]
    nlinarith
  have hR0 : 0 ≤ R := by linarith
  have hH : 1 ≤ H := (Nat.one_le_floor_iff R).mpr hR
  have hheight : (H : ℝ) ≤ OrdinaryRootPointHeight.constant K D * (N : ℝ) ^ (D : ℝ) := by
    rw [Real.rpow_natCast]
    exact Nat.floor_le hR0
  let U := F.image (fun p ↦ lift p.1 p.2 (w p))
  have hU : U ⊆ curvePoints (WeightedOrdinaryAffineIdeal.ordinaryIdeal c I J₀) H := by
    intro v hv
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hv
    exact (OrdinaryRootPointHeight.point_floor_height I J₀ d (w p) p.1 p.2 N K D A₀ hD hNpos
      (hXupper p hp) (hadmiss p hp).2.2.1 hiN hjN hK' hdegree hdheight (hw' p hp)).2.2
  have hAdmiss : ∀ v ∈ U, CriticalNonalignedPointCover.Admissible N B S T v := by
    intro v hv
    obtain ⟨p, hp, rfl⟩ := mem_image.mp hv
    change AdmissibleHost N B S T p
    exact hadmiss p hp
  have hresult := hcount N (by omega) L B hcrit hB hBL s hlength hcap d D I j hs hdeg hD hmin
    a ha hd hI hj hcard hK hiB hjB S T hiS hjT U H hH hheight hU hAdmiss
  have himage : U.image host = F := by simp [U, image_image, Function.comp_def, host_lift]
  simpa only [himage] using hresult.2

def SourceAdmissibleHost (N L : ℕ) (S T : Finset ℤ) (p : ℤ × ℤ) : Prop :=
  (N : ℤ) ≤ p.1 ∧ (N : ℤ) ≤ p.2 ∧ p.2.natAbs ≤ 2 * N ∧
    (∀ z ∈ S, 0 < p.1 + z) ∧ (∀ z ∈ T, 0 < p.2 + z) ∧
    ¬ CompressedTargetAlignment.Aligned 1 p.1.natAbs p.2.natAbs L

theorem source_admissible {N L : ℕ} {S T : Finset ℤ} {p : ℤ × ℤ}
    (hL : 1 ≤ L) (hp : SourceAdmissibleHost N L S T p) : AdmissibleHost N (L + 1) S T p := by
  obtain ⟨hX, hY, hYupper, hposS, hposT, hnon⟩ := hp
  refine ⟨hX, hY, hYupper, hposS, hposT, fun h ↦ hnon ?_⟩
  exact AffineGridAlignment.source_alignment_of_nonneg hL ((Nat.cast_nonneg N).trans hX)
    ((Nat.cast_nonneg N).trans hY) h

theorem source_uniform_hosts (C A₀ ε : ℝ) (K D : ℕ) (hA₀ : 0 ≤ A₀) (hD : 0 < D)
    (hdegree : A₀ + (K : ℝ) ≤ 2 * D) (hε : 0 < ε) :
    ∃ k : ℕ, ∀ kmax ≥ k,
      UniformOrdinarySurfaceCover.UniformCover kmax K →
      (∀ M, UniformAffineCurvePointCount.UniformBound kmax M) →
      ∃ A : ℝ, 0 < A ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ, 1 ≤ L →
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ s : List (PolynomialRing ℚ), k ≤ s.length → s.length ≤ kmax →
      ∀ (d : Fin s.length → ℤ) (I : Fin s.length → Finset ℤ) (j : Fin s.length → ℤ),
      let c : Fin s.length → ℚ := fun i ↦ (d i : ℚ)
      let J₀ : Fin s.length → Finset ℤ := fun i ↦ {j i}
      ∀ (_hs : ∀ i, s.get i = radicand (c i) (2 * D - ((I i).card + (J₀ i).card)) (I i) (J₀ i)),
      ∀ a : ℕ, 0 < a → (∀ i, d i ≠ 0) →
        (Pairwise fun i t ↦ Disjoint (I i) (I t)) → Function.Injective j →
        (∀ i, (I i).card = a) → (∀ i, (I i).card + 1 ≤ K) →
        (∀ i, ∀ z ∈ I i, z.natAbs ≤ L + 1) → (∀ i, (j i).natAbs ≤ L + 1) →
        (∀ i, ((d i).natAbs : ℝ) ≤ (N : ℝ) ^ A₀) →
      ∀ S T : Finset ℤ, (∀ i, I i ⊆ S) → (∀ i, j i ∈ T) →
      ∀ F : Finset (ℤ × ℤ), (∀ p ∈ F, SourceAdmissibleHost N L S T p) →
        (∀ p ∈ F, p.1.natAbs ≤ 2 * N) →
        (∀ p ∈ F, ∃ w : Fin s.length → ℤ,
          ∀ i, w i ^ 2 = d i * integerProduct (I i) p.1 * (p.2 + j i)) →
        (F.card : ℝ) ≤ A * (N : ℝ) ^ ε := by
  obtain ⟨k, hk⟩ := uniform_hosts C A₀ ε K D 1 hA₀ hD hdegree hε
  refine ⟨k, ?_⟩
  intro kmax hkkmax hCover hPila
  obtain ⟨A, hA, N₀, hcount⟩ := hk kmax hkkmax hCover hPila
  refine ⟨A, hA, N₀, ?_⟩
  intro N hN L hL hcrit s hlength hcap d I j c J₀ hs a ha hd hI hj hcard hK hiB hjB hdheight S T hiS hjT F hadmiss hXupper hroots
  exact hcount N hN L (L + 1) hcrit (by omega) (by simp) s hlength hcap d I j hs a ha hd hI hj hcard hK
    hiB hjB hdheight S T hiS hjT F (fun p hp ↦ source_admissible hL (hadmiss p hp)) hXupper hroots

end PaperP1.NonalignedDyadicRootHostCount
