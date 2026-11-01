module

public import PaperP1.Asymptotics.OriginalPairHosts
public import PaperP1.Asymptotics.OriginalWindowFamilyMass

/-! # Exact heterogeneous independent weights of all full-loss pair hosts -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PairHostIndependentMass

open Finset PaperP1.Model PaperP1.Model.InfiniteStarts

def mass (N L : ℕ) : ℝ :=
  ∑ p ∈ PairHostCover.hosts N L, infiniteMarginal p.1 L * infiniteMarginal p.2 L

theorem finite_mass_cap (N L : ℕ) {M : ℝ} (hM : 0 ≤ M)
    (hcap : ∀ x ∈ dyadicBlock N, 0 ≤ infiniteMarginal x L ∧ infiniteMarginal x L ≤ M) :
    mass N L ≤ (PairHostCover.hosts N L).card * M ^ 2 := by
  unfold mass
  calc
    _ ≤ ∑ _p ∈ PairHostCover.hosts N L, M ^ 2 := by
      apply sum_le_sum
      intro p hp
      obtain ⟨hx, hy⟩ := mem_product.mp (mem_filter.mp hp).1
      simpa only [pow_two] using mul_le_mul (hcap p.1 hx).2 (hcap p.2 hy).2 (hcap p.2 hy).1 hM
    _ = _ := by rw [sum_const, nsmul_eq_mul]

theorem uniform_mass (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → mass N L ≤ (N : ℝ) ^ (-1 + ε) := by
  let η := ε / 2
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨NH, hNHtwo, hNH⟩ := OriginalPairHosts.uniform_count C η hη
  obtain ⟨K, hK, NM, hNM⟩ := OriginalWindowFamilyMass.uniform_marginals C
  obtain ⟨NF, hNF⟩ := HalfCountSchedule.factor_absorption (K ^ 2) (-1 + η) η hη
  refine ⟨max NH (max NM NF), ?_⟩
  intro N hN L hband
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hcap := finite_mass_cap N L (div_nonneg hK.le hn.le)
    (fun x hx ↦ hNM N (by omega) L x hband hx)
  have hhosts := hNH N (by omega) L hband
  have hproduct : (N : ℝ) ^ (1 + η) * (K / N) ^ 2 = K ^ 2 * (N : ℝ) ^ (-1 + η) := by
    calc
      _ = K ^ 2 * ((N : ℝ) ^ (1 + η) / (N : ℝ) ^ 2) := by rw [div_pow]; ring
      _ = K ^ 2 * (N : ℝ) ^ ((1 + η) - 2) := by rw [Real.rpow_sub hn]; norm_num
      _ = _ := by congr 2; ring
  calc
    _ ≤ ((PairHostCover.hosts N L).card : ℝ) * (K / N) ^ 2 := hcap
    _ ≤ (N : ℝ) ^ (1 + η) * (K / N) ^ 2 := mul_le_mul_of_nonneg_right hhosts (sq_nonneg _)
    _ = _ := hproduct
    _ ≤ (N : ℝ) ^ ((-1 + η) + η) := hNF N (by omega)
    _ = _ := by congr 1; dsimp [η]; ring

end PaperP1.PairHostIndependentMass
