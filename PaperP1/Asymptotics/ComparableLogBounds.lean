module

public import PaperP1.Asymptotics.GrowingDegreePrimeError

/-! # Uniform logarithmic degree and width transfer between comparable scales -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ComparableLogBounds

open Filter

def widthConstant (D A₀ : ℝ) : ℝ := max 1 D * (2 : ℝ) ^ |A₀|

theorem exists_nat_comparison (a b : ℝ) (ha : 0 < a) :
    ∃ C : ℕ, 1 ≤ C ∧ ∀ N n : ℕ, a * N ≤ n → (n : ℝ) ≤ b * N →
      N ≤ C * n ∧ n ≤ C * N := by
  obtain ⟨C, hC⟩ := exists_nat_ge (max 1 (max b (1 / a)))
  have hC1 : (1 : ℝ) ≤ C := (le_max_left _ _).trans hC
  have hCb : b ≤ C := (le_max_left _ _).trans ((le_max_right _ _).trans hC)
  have hCi : 1 / a ≤ (C : ℝ) := (le_max_right _ _).trans ((le_max_right _ _).trans hC)
  have hCa : (1 : ℝ) ≤ C * a := (div_le_iff₀ ha).mp hCi
  refine ⟨C, by exact_mod_cast hC1, ?_⟩
  intro N n hlo hhi
  have hl : (N : ℝ) ≤ (C : ℝ) * n := by
    calc
      (N : ℝ) = 1 * N := (one_mul _).symm
      _ ≤ ((C : ℝ) * a) * N := mul_le_mul_of_nonneg_right hCa (Nat.cast_nonneg _)
      _ = (C : ℝ) * (a * N) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hlo (by linarith)
  have hu : (n : ℝ) ≤ (C : ℝ) * N := hhi.trans (mul_le_mul_of_nonneg_right hCb (Nat.cast_nonneg _))
  exact ⟨by exact_mod_cast hl, by exact_mod_cast hu⟩

theorem widthConstant_ge_one (D A₀ : ℝ) : 1 ≤ widthConstant D A₀ := by
  have hp : (1 : ℝ) ≤ (2 : ℝ) ^ |A₀| := Real.one_le_rpow (by norm_num) (abs_nonneg _)
  unfold widthConstant
  calc
    1 ≤ max 1 D := le_max_left _ _
    _ = max 1 D * 1 := (mul_one _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hp (by positivity)

theorem log_comparison (C N M : ℕ) (hC : 1 ≤ C) (hN : 3 ≤ N) (hCN : C ^ 2 ≤ N)
    (hlo : N ≤ C * M) (hhi : M ≤ C * N) :
    Real.log N ≤ 2 * Real.log M ∧ Real.log M ≤ 2 * Real.log N := by
  have hCp : (0 : ℝ) < C := by exact_mod_cast (show 0 < C by omega)
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hMpNat : 0 < M := by
    by_contra hnot
    have hz : M = 0 := by omega
    rw [hz, mul_zero] at hlo
    omega
  have hMp : (0 : ℝ) < M := by exact_mod_cast hMpNat
  have hlN : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hloglo := Real.log_le_log hNp (by exact_mod_cast hlo : (N : ℝ) ≤ C * M)
  have hloghi := Real.log_le_log hMp (by exact_mod_cast hhi : (M : ℝ) ≤ C * N)
  rw [Real.log_mul hCp.ne' hMp.ne'] at hloglo
  rw [Real.log_mul hCp.ne' hNp.ne'] at hloghi
  have hlogC := Real.log_le_log (sq_pos_of_pos hCp) (by exact_mod_cast hCN : (C : ℝ) ^ 2 ≤ N)
  rw [Real.log_pow] at hlogC
  norm_num at hlogC
  constructor <;> linarith

theorem degree_transfer (c η : ℝ) (hc : 0 ≤ c) (hη : 0 < η) (C : ℕ) (hC : 1 ≤ C) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ M d : ℕ, N ≤ C * M → M ≤ C * N →
      (d : ℝ) ≤ c * Real.log (Real.log N) → (d : ℝ) ≤ (c + η) * Real.log (Real.log M) := by
  obtain ⟨Nl, hNl⟩ := eventually_atTop.mp
    (PaperP1.ModerateOrder.loglog_tendsto_atTop.eventually
      (eventually_ge_atTop ((c + η) * Real.log 2 / η)))
  refine ⟨max 3 (max (C ^ 2) Nl), ?_⟩
  intro N hN M d hlo hhi hd
  have hlN : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hcomp := log_comparison C N M hC (by omega) (by omega) hlo hhi
  have hhalf : Real.log N / 2 ≤ Real.log M := by linarith only [hcomp.1]
  have hLL := Real.log_le_log (by positivity : 0 < Real.log N / 2) hhalf
  rw [Real.log_div hlN.ne' (by norm_num : (2 : ℝ) ≠ 0)] at hLL
  have hmargin := (div_le_iff₀ hη).mp (hNl N (by omega))
  have hmul := mul_le_mul_of_nonneg_left hLL (by positivity : 0 ≤ c + η)
  nlinarith only [hd, hmargin, hmul]

theorem width_transfer (D A₀ : ℝ) (C N M W : ℕ) (hC : 1 ≤ C) (hN : 3 ≤ N) (hCN : C ^ 2 ≤ N)
    (hlo : N ≤ C * M) (hhi : M ≤ C * N) (hW : (W : ℝ) ≤ D * (Real.log N) ^ A₀) :
    (W : ℝ) ≤ widthConstant D A₀ * (Real.log M) ^ A₀ := by
  have hlN : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hcomp := log_comparison C N M hC hN hCN hlo hhi
  have hlM : 0 < Real.log M := by linarith only [hlN, hcomp.1]
  have hpow : (Real.log N) ^ A₀ ≤ (2 : ℝ) ^ |A₀| * (Real.log M) ^ A₀ := by
    by_cases hA : 0 ≤ A₀
    · have hb := Real.rpow_le_rpow hlN.le hcomp.1 hA
      rw [abs_of_nonneg hA, ← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hlM.le]
      exact hb
    · have hAn : A₀ < 0 := lt_of_not_ge hA
      have hhalf : Real.log M / 2 ≤ Real.log N := by linarith only [hcomp.2]
      have hb := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < Real.log M / 2) hhalf hAn.le
      calc
        _ ≤ (Real.log M / 2) ^ A₀ := hb
        _ = _ := by
          rw [Real.div_rpow hlM.le (by norm_num : (0 : ℝ) ≤ 2), abs_of_neg hAn,
            Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
          ring
  calc
    (W : ℝ) ≤ max 1 D * (Real.log N) ^ A₀ := hW.trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hlN.le _))
    _ ≤ max 1 D * ((2 : ℝ) ^ |A₀| * (Real.log M) ^ A₀) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = _ := by unfold widthConstant; ring

end PaperP1.ComparableLogBounds
