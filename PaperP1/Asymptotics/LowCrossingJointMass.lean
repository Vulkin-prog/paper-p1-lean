module

public import PaperP1.Model.ExtensionJointFactor
public import PaperP1.Model.MinimalCrossingWindows
public import PaperP1.Model.TwoTargetPrimitiveData
public import PaperP1.Asymptotics.RelativeOriginalWindowMass
public import PaperP1.Asymptotics.CriticalPairKernelPowers

/-! # Minimal crossings of small relative rank have a uniform actual source-times-half-count joint bound -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LowCrossingJointMass

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.Model.InfiniteStarts
  PaperP1.SubspaceFamilyRank PaperP1.FiniteFamilyEnumeration PaperP1.TwoTargetPrimitiveData

theorem uniform_bound (r s : ℕ) (a C ε : ℝ) (ha : 0 ≤ a) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ e : Finset ℕ, e.card = s → e ⊆ dyadicBlock N →
      ∀ G : Finset ℕ, G ⊆ dyadicBlock N → ∀ F : Finset (Finset ℕ),
      (∀ A ∈ F, A ⊆ G ∧ A.card = r ∧ Disjoint e A ∧
        span (fun x ↦ squareClassSpace x L) e ⊓ span (fun x ↦ squareClassSpace x L) A ≠ ⊥ ∧
        (∀ B : Finset ℕ, B ⊂ A →
          Disjoint (span (fun x ↦ squareClassSpace x L) e) (span (fun x ↦ squareClassSpace x L) B)) ∧
        (MinimalRelativeRelations.nullity (span (fun x ↦ squareClassSpace x L) e)
          (fun x ↦ squareClassSpace x L) A : ℝ) ≤ a * L) →
      (∑ A ∈ F, infiniteJointMoment L (e ∪ A)) ≤
        infiniteJointMoment L e * (N : ℝ) ^ (-(r : ℝ) / 2 + a + ε) := by
  obtain ⟨NI, _hNI, hi⟩ := RelativeOriginalWindowMass.uniform_mass r s C (ε / 2) (by positivity)
  obtain ⟨NP, hp⟩ := CriticalPairKernelPowers.power_of_rank C a 0 (ε / 2) ha (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨3 + NI + NP + NG, by omega, ?_⟩
  intro N hN L hband e hecard heG G hG F hF
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  let W := span (fun x ↦ squareClassSpace x L) e
  have hsub : F ⊆ RelativeWindowFamilies.families G L r W := by
    intro A hA
    obtain ⟨hAG, hcard, _hdis, hcross, hproper, _hlow⟩ := hF A hA
    exact MinimalCrossingWindows.mem_families G L r W A hAG hcard hcross hproper
  have hind : FamilyIndependentMass.independentMass F L ≤ (N : ℝ) ^ (-(r : ℝ) / 2 + ε / 2) :=
    (sum_le_sum_of_subset_of_nonneg hsub (fun A _ _ ↦ prod_nonneg fun x _ ↦
      MissingBlockProbabilities.infiniteMarginal_nonneg x L)).trans
        (hi N (by omega) L hband (centres e hecard) (centres_mem _ e hecard heG)
          W (source_enumeration e L hecard).le G hG).2
  have hrank (A : Finset ℕ) (hA : A ∈ F) :
      (2 ^ MinimalRelativeRelations.nullity W (fun x ↦ squareClassSpace x L) A : ℝ) ≤
        (N : ℝ) ^ (a + ε / 2) := by
    apply hp N (by omega) L _ hband
    have hd := (hF A hA).2.2.2.2.2
    simp only [Nat.cast_add, Nat.cast_one]
    have hLnonneg : (0 : ℝ) ≤ L := Nat.cast_nonneg _
    have hprod : 0 ≤ ε * (L : ℝ) := mul_nonneg hε.le hLnonneg
    nlinarith only [hd, ha, hε, hprod]
  calc
    _ ≤ ∑ A ∈ F, infiniteJointMoment L e *
        ((∏ x ∈ A, infiniteMarginal x L) *
          (2 ^ MinimalRelativeRelations.nullity W (fun x ↦ squareClassSpace x L) A : ℝ)) :=
      sum_le_sum fun A hA ↦ ExtensionJointFactor.upper_bound L hL e A (hF A hA).2.2.1
    _ ≤ ∑ A ∈ F, infiniteJointMoment L e *
        ((∏ x ∈ A, infiniteMarginal x L) * (N : ℝ) ^ (a + ε / 2)) := by
      apply sum_le_sum
      intro A hA
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hrank A hA)
        (prod_nonneg fun x _ ↦ MissingBlockProbabilities.infiniteMarginal_nonneg x L))
        (infiniteJointMoment_nonneg L e)
    _ = (infiniteJointMoment L e * (N : ℝ) ^ (a + ε / 2)) *
        FamilyIndependentMass.independentMass F L := by
      rw [FamilyIndependentMass.independentMass, mul_sum]
      apply sum_congr rfl
      intro A _
      ring
    _ ≤ (infiniteJointMoment L e * (N : ℝ) ^ (a + ε / 2)) *
        (N : ℝ) ^ (-(r : ℝ) / 2 + ε / 2) := mul_le_mul_of_nonneg_left hind
      (mul_nonneg (infiniteJointMoment_nonneg L e) (Real.rpow_nonneg hn.le _))
    _ = _ := by
      rw [mul_assoc, ← Real.rpow_add hn]
      congr 1
      ring

end PaperP1.LowCrossingJointMass
