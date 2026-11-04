module

public import PaperP1.Asymptotics.GeneralRootHostCount
public import PaperP1.Asymptotics.SelectedDegreeOneSystems

/-! # Both per-system assertions of companion T1.7 with one uniform larger-system threshold

The same coefficient-uniform constant and scale threshold work for arbitrarily
many equations. When every right factor has degree one, a proved subsystem
selection supplies the sharper subpower estimate, even for varying left degrees.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.UniformGeometricSystemsUnderInputs

open Finset PaperP1.SplitRadicalPointHeight

theorem companion_T1_7_systems (C A₀ ε : ℝ) (K Jexp : ℕ) (hA₀ : 0 ≤ A₀) (hε : 0 < ε) :
    ∃ D kg kl : ℕ, 0 < D ∧ 1 ≤ kl ∧
      (UniformSourceSurfaceCover.UniformCover kg K D →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound ((D + 2).choose 2 + kg) M) →
      UniformOrdinarySurfaceCover.UniformCover kl K →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound (kl + 3) M) →
      ∃ A : ℝ, 0 < A ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L B : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C → 1 ≤ B → B ≤ (L + 1) ^ Jexp →
      ∀ n : ℕ, kg + (K + 1) * kl ≤ n →
      ∀ (d : Fin n → ℤ) (I J : Fin n → Finset ℤ),
        (∀ i, d i ≠ 0) → (Pairwise fun i j ↦ Disjoint (I i) (I j)) →
        (Pairwise fun i j ↦ Disjoint (J i) (J j)) →
        (∀ i, (I i).Nonempty) → (∀ i, (J i).Nonempty) →
        (∀ i, (I i).card + (J i).card ≤ K) →
        (∀ i, ∀ z ∈ I i, z.natAbs ≤ B) → (∀ i, ∀ z ∈ J i, z.natAbs ≤ B) →
        (∀ i, ((d i).natAbs : ℝ) ≤ (N : ℝ) ^ A₀) →
      ∀ S T : Finset ℤ, (∀ i, I i ⊆ S) → (∀ i, J i ⊆ T) →
      ∀ F : Finset (ℤ × ℤ),
        (∀ p ∈ F, (N : ℤ) ≤ p.1 ∧ (N : ℤ) ≤ p.2 ∧ p.1.natAbs ≤ 2 * N ∧ p.2.natAbs ≤ 2 * N) →
        (∀ p ∈ F, SourceCurvePointCover.Admissible S T p) →
        (∀ p ∈ F, ∃ w : Fin n → ℤ,
          ∀ i, w i ^ 2 = d i * integerProduct (I i) p.1 * integerProduct (J i) p.2) →
        (F.card : ℝ) ≤ A * (N : ℝ) ^ (1 / 2 + ε) ∧
          ((∀ i, (J i).card = 1) → (F.card : ℝ) ≤ A * (N : ℝ) ^ ε)) := by
  obtain ⟨D, kg, hD, _hdegree, hg⟩ := GeneralRootHostCount.uniform_hosts_of_many C A₀ ε K Jexp hA₀ hε
  obtain ⟨kl, hkl, hl⟩ := SelectedDegreeOneSystems.uniform_varying C A₀ ε K Jexp hA₀ hε
  refine ⟨D, kg, kl, hD, hkl, ?_⟩
  intro hSource hCurveG hOrdinary hCurveL
  obtain ⟨AG, hAG, NG, hG⟩ := hg hSource hCurveG
  obtain ⟨AL, hAL, NL, hL⟩ := hl hOrdinary hCurveL
  refine ⟨AG + AL, by positivity, max NG NL, ?_⟩
  intro N hN L B hband hB hBL n hn d I J hd hI hJ hneI hneJ hK hiB hjB hdheight S T hiS hjT F hdyadic hadmiss hroots
  have hgeneral := hG N (by omega) L B hband hB hBL n (by omega) d I J hd hI hJ hneI hneJ
    hK hiB hjB hdheight S T hiS hjT F hadmiss
    (fun p hp ↦ ⟨(hdyadic p hp).2.2.1, (hdyadic p hp).2.2.2⟩) hroots
  refine ⟨hgeneral.trans (mul_le_mul_of_nonneg_right (by linarith only [hAL])
    (Real.rpow_nonneg (Nat.cast_nonneg N) _)), ?_⟩
  intro hsingle
  have hJone (i : Fin n) : ∃ j : ℤ, J i = {j} := card_eq_one.mp (hsingle i)
  choose j hj using hJone
  have hji : Function.Injective j := by
    intro i t he
    by_contra hit
    have hh : Disjoint (J i) (J t) := hJ hit
    rw [hj i, hj t, he] at hh
    exact not_disjoint_iff.mpr ⟨j t, mem_singleton_self _, mem_singleton_self _⟩ hh
  have hK' (i : Fin n) : (I i).card + 1 ≤ K := by
    have hh := hK i
    rwa [hj i, card_singleton] at hh
  have hjB' (i : Fin n) : (j i).natAbs ≤ B := hjB i (j i) (by rw [hj i]; exact mem_singleton_self _)
  have hjT' (i : Fin n) : j i ∈ T := hjT i (by rw [hj i]; exact mem_singleton_self _)
  have hAdmiss : ∀ p ∈ F, OrdinaryDyadicRootHostCount.AdmissibleHost N S T p := by
    intro p hp
    have hd := hdyadic p hp
    have hg := hadmiss p hp
    exact ⟨hd.1, hd.2.2.2, hg.1, hg.2.1, hg.2.2.1, hg.2.2.2.2⟩
  have hroots' (p : ℤ × ℤ) (hp : p ∈ F) : ∃ w : Fin n → ℤ,
      ∀ i, w i ^ 2 = d i * integerProduct (I i) p.1 * (p.2 + j i) := by
    obtain ⟨w, hw⟩ := hroots p hp
    exact ⟨w, fun i ↦ by simpa only [hj i, integerProduct, prod_singleton] using hw i⟩
  have hlinear := hL N (by omega) L B hband hB hBL n (by omega) d I j hd hI hji hneI hK'
    hiB hjB' hdheight S T hiS hjT' F hdyadic hAdmiss hroots'
  exact hlinear.trans (mul_le_mul_of_nonneg_right (by linarith only [hAG])
    (Real.rpow_nonneg (Nat.cast_nonneg N) _))

end PaperP1.UniformGeometricSystemsUnderInputs
