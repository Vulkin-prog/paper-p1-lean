module

public import PaperP1.Asymptotics.CoefficientNonalignedHostCount
public import PaperP1.Arithmetic.UniformNormalizedCurvePointCount

/-! # A common subpower coefficient list preserves the degree-one nonaligned host bound -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.CoefficientDegreeOneHostCount

open Finset PaperP1.CoefficientSplitRadicalPatterns PaperP1.CriticalCoefficientPatterns
  PaperP1.SplitRadicalPointHeight

def Valid {k : ℕ} (K : ℕ) (p : Pattern k) : Prop :=
  CoefficientNonalignedHostCount.Valid K p ∧
    ∃ a : ℕ, 0 < a ∧ ∀ i, (p.1.1 i).card = a ∧ (p.1.2 i).card = 1

theorem uniform_hosts (C A₀ ε : ℝ) (K : ℕ) (hA₀ : 0 ≤ A₀) (hε : 0 < ε) :
    ∃ k : ℕ, 1 ≤ k ∧ (UniformOrdinarySurfaceCover.UniformCover k K →
      (∀ M, UniformNormalizedCurvePointCount.UniformBound (k + 3) M) →
      ∃ A : ℝ, 0 < A ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
        |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ Q : Finset ℕ, (Q.card : ℝ) ≤ (N : ℝ) ^ coefficientMargin (ε / 2) k →
        (∀ d ∈ Q, 0 < d ∧ (d : ℝ) ≤ (N : ℝ) ^ A₀) →
      ∀ F : Finset (ℤ × ℤ),
        (∀ p ∈ F, (N : ℤ) ≤ p.1 ∧ (N : ℤ) ≤ p.2 ∧ p.1.natAbs ≤ 2 * N ∧ p.2.natAbs ≤ 2 * N) →
        (∀ p ∈ F, ¬ CompressedTargetAlignment.Aligned 1 p.1.natAbs p.2.natAbs L) →
        (∀ p ∈ F, ∃ q ∈ pool k L K Q, Valid K q ∧ ∃ w : Fin k → ℤ,
          ∀ i, w i ^ 2 = coefficient q i * integerProduct (q.1.1 i) p.1 * integerProduct (q.1.2 i) p.2) →
        (F.card : ℝ) ≤ A * (N : ℝ) ^ ε) := by
  obtain ⟨k₀, hk⟩ := DegreeOneRootHostCount.uniform_hosts C A₀ (ε / 2) K hA₀ (by positivity)
  let k := k₀ + 1
  obtain ⟨Np, _hNp, hp⟩ := CriticalCoefficientPatterns.uniform_pool C (ε / 2) k K (by positivity)
  refine ⟨k, by dsimp [k]; omega, ?_⟩
  intro hCover hPila
  obtain ⟨A, hA, Nc, hcount⟩ := hk k (by dsimp [k]; omega) hCover
    (fun M ↦ UniformNormalizedCurvePointCount.ordinary_specialization k M (hPila M))
  refine ⟨A, hA, max 1 (max Np Nc), ?_⟩
  intro N hN L hcrit Q hQcard hQ F hdyadic hnon hsystems
  classical
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  let patterns := (pool k L K Q).filter (Valid K)
  let hosts := fun q : Pattern k ↦ F.filter fun p ↦ ∃ w : Fin k → ℤ,
    ∀ i, w i ^ 2 = coefficient q i * integerProduct (q.1.1 i) p.1 * integerProduct (q.1.2 i) p.2
  have hcover : ∀ p ∈ F, ∃ q ∈ patterns, p ∈ hosts q := by
    intro p hpF
    obtain ⟨q, hq, hvalid, w, hw⟩ := hsystems p hpF
    exact ⟨q, mem_filter.mpr ⟨hq, hvalid⟩, mem_filter.mpr ⟨hpF, w, hw⟩⟩
  have hbound : ∀ q ∈ patterns, ((hosts q).card : ℝ) ≤ A * (N : ℝ) ^ (ε / 2) := by
    intro q hq
    obtain ⟨hqpool, ⟨hI, hJ, _hneI, _hneJ, hK⟩, a, ha, hdegrees⟩ := mem_filter.mp hq
    have hsingle (i : Fin k) : ∃ j : ℤ, q.1.2 i = {j} := card_eq_one.mp (hdegrees i).2
    choose j hj using hsingle
    have hji : Function.Injective j := by
      intro i n heq
      by_contra hine
      have hdisj : Disjoint (q.1.2 i) (q.1.2 n) := hJ hine
      rw [hj i, hj n, heq] at hdisj
      exact not_disjoint_iff.mpr ⟨j n, mem_singleton_self _, mem_singleton_self _⟩ hdisj
    have hjbound (i : Fin k) : (j i).natAbs ≤ L + 1 :=
      right_bound hqpool i _ (by rw [hj i]; exact mem_singleton_self _)
    have hdegree (i : Fin k) : (q.1.1 i).card + 1 ≤ K := by
      have h := hK i
      rwa [(hdegrees i).2] at h
    have hheight (i : Fin k) : ((coefficient q i).natAbs : ℝ) ≤ (N : ℝ) ^ A₀ := by
      simpa only [coefficient, Int.natAbs_natCast] using (hQ _ (coefficient_mem hqpool i)).2
    apply hcount N (by omega) L hcrit k (by dsimp [k]; omega) le_rfl (coefficient q) q.1.1 j a ha
      (fun i ↦ (coefficient_pos (fun d hd ↦ (hQ d hd).1) hqpool i).ne') hI hji
      (fun i ↦ (hdegrees i).1) hdegree (left_bound hqpool) hjbound hheight (hosts q)
      (fun p hpF ↦ hdyadic p (mem_filter.mp hpF).1)
      (fun p hpF _ ↦ hnon p (mem_filter.mp hpF).1)
    intro p hpF
    obtain ⟨w, hw⟩ := (mem_filter.mp hpF).2
    refine ⟨w, ?_⟩
    intro i
    have hprod : integerProduct (q.1.2 i) p.2 = p.2 + j i := by
      rw [hj i, integerProduct, prod_singleton]
    simpa only [hprod] using hw i
  have hfinite := FiniteCoverCount.cardinal_le F patterns hosts (A * (N : ℝ) ^ (ε / 2)) hcover hbound
  have hpatterns : (patterns.card : ℝ) ≤ (N : ℝ) ^ (ε / 2) :=
    (show (patterns.card : ℝ) ≤ (pool k L K Q).card by exact_mod_cast card_filter_le _ _).trans
      (hp N (by omega) L hcrit Q hQcard)
  calc
    _ ≤ (patterns.card : ℝ) * (A * (N : ℝ) ^ (ε / 2)) := hfinite
    _ ≤ (N : ℝ) ^ (ε / 2) * (A * (N : ℝ) ^ (ε / 2)) :=
      mul_le_mul_of_nonneg_right hpatterns (mul_nonneg hA.le (Real.rpow_nonneg hNpos.le _))
    _ = A * (N : ℝ) ^ ε := by
      rw [mul_left_comm, ← Real.rpow_add hNpos, show ε / 2 + ε / 2 = ε by ring]

end PaperP1.CoefficientDegreeOneHostCount
