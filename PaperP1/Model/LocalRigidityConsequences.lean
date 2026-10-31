module

public import PaperP1.Model.RelativeSignIndependence

/-!
# Critical-band effective ranks and actual heterogeneous marginals

The uniform critical relation bound gives dimensions L or L-1, the exact
positive marginals p or 2p, and a uniform pointwise O(1/N) bound. All actual
positive-probability starts are retained. No nominal-marginal substitution
is made in a dependent or incompatible window.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LocalRigidityConsequences

open PaperP1.Arithmetic PaperP1.Affine Model.InfiniteStarts WindowRelationCode

local instance localConsequencesPrimeTwo : Fact (Nat.Prime 2) := Fact.mk Nat.prime_two

theorem effective_rank_eq_or_pred {x L : ℕ} (hx : 0 < x)
    (hrel : Module.finrank F₂ (windowRelationCode (x - 1) (L + 1)) ≤ 1) :
    Module.finrank F₂ (squareClassSpace x L) = L ∨
      Module.finrank F₂ (squareClassSpace x L) = L - 1 := by
  have h := LocalRunRank.squareClass_rank_add_relation_rank (L := L) hx
  omega

theorem inverse_two_pow_pred {L : ℕ} (hL : 0 < L) :
    (2 ^ (L - 1) : ℝ)⁻¹ = 2 * (2 ^ L : ℝ)⁻¹ := by
  have hpow : (2 ^ L : ℝ) = 2 ^ (L - 1) * 2 := by
    calc
      (2 ^ L : ℝ) = 2 ^ ((L - 1) + 1) := congrArg (fun n : ℕ ↦ (2 ^ n : ℝ)) (by omega)
      _ = _ := pow_succ _ _
  rw [hpow]
  field_simp

theorem exact_marginal_eq_nominal_or_double {x L : ℕ} (hx : 0 < x) (hL : 0 < L)
    (hp : 0 < infiniteMarginal x L)
    (hrel : Module.finrank F₂ (windowRelationCode (x - 1) (L + 1)) ≤ 1) :
    infiniteMarginal x L = (2 ^ L : ℝ)⁻¹ ∨
      infiniteMarginal x L = 2 * (2 ^ L : ℝ)⁻¹ := by
  rw [LocalRunRank.infiniteMarginal_eq_squareClass_rank hL hp]
  rcases effective_rank_eq_or_pred hx hrel with h | h
  · exact Or.inl (congrArg (fun n : ℕ ↦ (2 ^ n : ℝ)⁻¹) h)
  · right
    rw [h]
    exact inverse_two_pow_pred hL

/-- A finite critical-band inequality, with an explicit constant depending only on C. -/
theorem nominal_marginal_bound {N L : ℕ} {C : ℝ} (hN : 2 ≤ N)
    (hband : |(L : ℝ) - Real.log N / Real.log 2| ≤ C) :
    (2 ^ L : ℝ)⁻¹ ≤ (2 : ℝ) ^ C / N := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlow : Real.log N / Real.log 2 ≤ (L : ℝ) + C := by
    have h := (abs_le.mp hband).1
    linarith
  have hlog : Real.log N ≤ ((L : ℝ) + C) * Real.log 2 := (div_le_iff₀ h2).mp hlow
  have he := Real.exp_le_exp.mpr hlog
  rw [Real.exp_log hn] at he
  have heq : Real.exp (((L : ℝ) + C) * Real.log 2) = (2 ^ L : ℝ) * (2 : ℝ) ^ C := by
    rw [add_mul, Real.exp_add, Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    congr 1
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), mul_comm C (Real.log 2)]
  rw [heq] at he
  rw [inv_eq_one_div]
  apply (div_le_div_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) L) hn).mpr
  nlinarith only [he]

/-- One threshold and one constant apply to every admissible start and every
length in the fixed critical band. The base has no upper bound. -/
theorem critical_band_marginals (a C : ℝ) (ha : 0 < a) :
    ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ x L : ℕ,
      0 < L → a * N ≤ ((x - 1 : ℕ) : ℝ) →
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → 0 < infiniteMarginal x L →
        (Module.finrank F₂ (squareClassSpace x L) = L ∨
          Module.finrank F₂ (squareClassSpace x L) = L - 1) ∧
        (infiniteMarginal x L = (2 ^ L : ℝ)⁻¹ ∨
          infiniteMarginal x L = 2 * (2 ^ L : ℝ)⁻¹) ∧
        infiniteMarginal x L ≤ K / N := by
  let K : ℝ := 2 * (2 : ℝ) ^ C
  have hK : 0 < K := mul_pos (by norm_num) (Real.rpow_pos_of_pos (by norm_num) C)
  obtain ⟨N₁, hN₁⟩ := LocalRigidityRegimes.critical_band_relation_rank_le_one a C ha
  refine ⟨K, hK, max 2 N₁, fun N hN x L hL hbase hband hp ↦ ?_⟩
  have hNtwo : 2 ≤ N := by omega
  have hN₁' : N₁ ≤ N := by omega
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hbasepos : 0 < ((x - 1 : ℕ) : ℝ) := (mul_pos ha hn).trans_le hbase
  have hx : 0 < x := by
    have h : 0 < x - 1 := by exact_mod_cast hbasepos
    omega
  have hrel := hN₁ N hN₁' (x - 1) L hbase hband
  have hdim := effective_rank_eq_or_pred hx hrel
  have hmarg := exact_marginal_eq_nominal_or_double hx hL hp hrel
  refine ⟨hdim, hmarg, ?_⟩
  have hnom := nominal_marginal_bound hNtwo hband
  have hpupper : infiniteMarginal x L ≤ 2 * (2 ^ L : ℝ)⁻¹ := by
    rcases hmarg with h | h
    · rw [h]
      have hnonneg : 0 ≤ (2 ^ L : ℝ)⁻¹ := by positivity
      linarith
    · exact h.le
  calc
    infiniteMarginal x L ≤ 2 * (2 ^ L : ℝ)⁻¹ := hpupper
    _ ≤ 2 * ((2 : ℝ) ^ C / N) := mul_le_mul_of_nonneg_left hnom (by norm_num)
    _ = K / N := by dsimp [K]; ring

end PaperP1.LocalRigidityConsequences
