module

public import PaperP1.Model.CompatibleJointMajorant
public import PaperP1.Model.ConnectedParticipatingWindows
public import PaperP1.Asymptotics.OriginalParticipatingTail
public import PaperP1.Asymptotics.ActualPairRowActivity
public import PaperP1.Asymptotics.CriticalPairKernelPowers

/-! # All sufficiently large connected orders have unconditional actual joint mass rate2-η under a compatible-nullity cap -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ConnectedJointBoundedNullityTail

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts PaperP1.ConnectedWindowFamilies

theorem uniform_bound (η u C ε : ℝ) (hη : 0 ≤ η) (hu : 0 < u) (hε : 0 < ε) :
    ∃ s : ℕ, 1 ≤ s ∧ ∃ N₀ : ℕ, 10 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → ∀ F : Finset (Finset ℕ),
      (∀ I ∈ F, I ⊆ dyadicBlock N ∧ 3 ≤ I.card ∧ s ≤ I.card ∧ Connected L I ∧
        (runCompatibleNullity L I : ℝ) ≤ η * L) →
      (∑ I ∈ F, u ^ I.card * infiniteJointMoment L I) ≤ (N : ℝ) ^ (-(2 - η) + ε) := by
  classical
  let M := u * (2 * (2 : ℝ) ^ C)
  obtain ⟨s, hs, NI, _hNI, hi⟩ := OriginalParticipatingTail.subcritical_tail
    C M (2 - ε / 3) (ε / 3) (by dsimp [M]; positivity) (by linarith only [hε]) (by positivity)
  obtain ⟨NP, hp⟩ := CriticalPairKernelPowers.power_of_rank C η 0 (ε / 3) hη (by positivity)
  obtain ⟨NM, _hNM, hm⟩ := ActualPairRowActivity.uniform_marginal_cap C
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  refine ⟨s, hs, 10 + NI + NP + NM + NG, by omega, ?_⟩
  intro N hN L hband F hF
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL : 0 < L := by have h := (hg N (by omega) L hband).2.2.1; omega
  have hamp (I : Finset ℕ) (hI : I ∈ F) :
      (2 ^ runCompatibleNullity L I : ℝ) ≤ (N : ℝ) ^ (η + ε / 3) := by
    apply hp N (by omega) L (runCompatibleNullity L I) hband
    have hcap := (hF I hI).2.2.2.2
    have hεL : 0 ≤ ε * (L : ℝ) := mul_nonneg hε.le (Nat.cast_nonneg L)
    push_cast
    nlinarith only [hcap, hη, hε, hεL]
  have hcap (x : ℕ) (hx : x ∈ dyadicBlock N) : u * infiniteMarginal x L ≤ M / N := by
    have h := mul_le_mul_of_nonneg_left (hm N (by omega) L hband x hx) hu.le
    simpa only [M, mul_div_assoc] using h
  have hindep := hi N (by omega) L hband (fun x ↦ u * infiniteMarginal x L)
    (fun x ↦ mul_nonneg hu.le (MissingBlockProbabilities.infiniteMarginal_nonneg x L)) hcap F (by
      intro I hI
      obtain ⟨hIG, hthree, hlarge, hconn, _hrank⟩ := hF I hI
      exact ⟨hIG, hlarge, ConnectedParticipatingWindows.witnesses L I (by omega) hconn⟩)
  calc
    _ ≤ (N : ℝ) ^ (η + ε / 3) * ∑ I ∈ F, ∏ x ∈ I, u * infiniteMarginal x L :=
      CompatibleJointMajorant.weighted_bound F L hL u _ hu.le hamp
    _ ≤ (N : ℝ) ^ (η + ε / 3) * (N : ℝ) ^ (-(2 - ε / 3) + ε / 3) :=
      mul_le_mul_of_nonneg_left hindep (Real.rpow_nonneg hn.le _)
    _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring

end PaperP1.ConnectedJointBoundedNullityTail
