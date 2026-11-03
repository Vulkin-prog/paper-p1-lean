module

public import PaperP1.Asymptotics.TernaryPrimeBudget
public import PaperP1.Asymptotics.TernaryUnboundedCutoff
public import PaperP1.Combinatorics.LabeledPopulationCount

/-! # Individual-prime fixed-k budgets with arbitrary source cutoffs and actual pattern labels -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TernaryPrimeTheorem

open Finset PaperP1.TernaryPrimeTopProducts PaperP1.TernaryUnboundedCutoff PaperP1.CriticalBandScale

theorem population_bound (C : ℝ) (D k : ℕ) (hk : 3 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L R : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → R ≤ D * (L + 1) →
      ∀ (F : Finset (Fin 3 → ℕ)) (U : (Fin 3 → ℕ) → Fin 3 → Finset ℕ)
        (H : (Fin 3 → ℕ) → ℕ) (base : Fin 3 → ℕ) (T : ℝ), 1 ≤ T →
      (∀ X ∈ F, SourceConditions N R D base U H X) →
      (∀ X ∈ F, T < (topProduct (U X) (H X) k : ℝ)) →
      (F.card : ℝ) ≤ (N : ℝ) ^ ε * ((N : ℝ) ^ 3 * T ^ (-2 : ℝ) + (N : ℝ) ^ (6 / 5 : ℝ)) := by
  obtain ⟨N₀, hN₀, hb⟩ := TernaryPrimeBudget.uniform_bound C (2 * D + 1) k hk ε hε
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L R hband hR F U H base T hT hadm hprod
  have hR' : R ≤ (2 * D + 1) * (L + 1) := hR.trans (Nat.mul_le_mul_right _ (by omega : D ≤ 2 * D + 1))
  apply hb N hN L R hband hR' F U (fun X ↦ min (H X) (2 * R + 1)) base T hT
  · intro X hX
    exact ((hadm X hX).capped hR).toAdmissible
  · intro X hX
    exact (hprod X hX).trans_le (by
      exact_mod_cast cutoff_mono (U X) k (min_le_left (H X) (2 * R + 1)))

theorem labeled_bound (C : ℝ) (D k J : ℕ) (hk : 3 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L R : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → R ≤ D * (L + 1) →
      ∀ (α : Type*) [DecidableEq α], ∀ (F : Finset (α × (Fin 3 → ℕ)))
        (U : α → (Fin 3 → ℕ) → Fin 3 → Finset ℕ) (H : α → (Fin 3 → ℕ) → ℕ)
        (base : α → Fin 3 → ℕ) (T : ℝ), 1 ≤ T →
      (F.image Prod.fst).card ≤ (L + 1) ^ J →
      (∀ z ∈ F, SourceConditions N R D (base z.1) (U z.1) (H z.1) z.2) →
      (∀ z ∈ F, T < (topProduct (U z.1 z.2) (H z.1 z.2) k : ℝ)) →
      (F.card : ℝ) ≤ (N : ℝ) ^ ε * ((N : ℝ) ^ 3 / T ^ 2 + (N : ℝ) ^ (6 / 5 : ℝ)) := by
  let δ := ε / 2
  obtain ⟨NG, _hNG, hg⟩ := population_bound C D k hk δ (by dsimp [δ]; positivity)
  obtain ⟨NS, hs⟩ := critical_band_scale C
  obtain ⟨NP, hp⟩ := LogarithmicWordPowers.polynomial_factor_le_rpow_eventually
    upperScale upperScale_pos.le 1 J δ (by dsimp [δ]; positivity)
  refine ⟨max 2 (max NG (max NS NP)), by omega, ?_⟩
  intro N hN L R hband hR α _instα F U H base T hT hlabels hadm hprod
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  let B : ℝ := (N : ℝ) ^ 3 * T ^ (-2 : ℝ) + (N : ℝ) ^ (6 / 5 : ℝ)
  have hfibre (a : α) : (((F.filter fun z ↦ z.1 = a).image Prod.snd).card : ℝ) ≤ (N : ℝ) ^ δ * B := by
    apply hg N (by omega) L R hband hR _ (U a) (H a) (base a) T hT
    · intro X hX
      obtain ⟨z, hz, rfl⟩ := mem_image.mp hX
      obtain ⟨hzF, hza⟩ := mem_filter.mp hz
      simpa only [hza] using hadm z hzF
    · intro X hX
      obtain ⟨z, hz, rfl⟩ := mem_image.mp hX
      obtain ⟨hzF, hza⟩ := mem_filter.mp hz
      simpa only [hza] using hprod z hzF
  have hcard := LabeledPopulationCount.cardinal_le F ((N : ℝ) ^ δ * B) hfibre
  have hL := (hs N (by omega) L hband).2
  have hpoly : ((L + 1 : ℕ) : ℝ) ^ J ≤ (N : ℝ) ^ δ := by
    simpa only [one_mul, Nat.cast_add, Nat.cast_one, abs_of_nonneg (by positivity : 0 ≤ (L + 1 : ℝ) ^ J)]
      using hp N (by omega) L hL
  have hI : ((F.image Prod.fst).card : ℝ) ≤ (N : ℝ) ^ δ :=
    (show ((F.image Prod.fst).card : ℝ) ≤ ((L + 1 : ℕ) : ℝ) ^ J by exact_mod_cast hlabels).trans hpoly
  have heq : (N : ℝ) ^ 3 * T ^ (-2 : ℝ) = (N : ℝ) ^ 3 / T ^ 2 := by
    rw [div_eq_mul_inv]
    congr 1
    norm_num
  calc
    _ ≤ (N : ℝ) ^ δ * ((N : ℝ) ^ δ * B) :=
      hcard.trans (mul_le_mul_of_nonneg_right hI (by dsimp [B]; positivity))
    _ = (N : ℝ) ^ ε * B := by rw [← mul_assoc, ← Real.rpow_add hn]; congr 2; dsimp [δ]; ring
    _ = _ := by dsimp only [B]; rw [heq]

end PaperP1.TernaryPrimeTheorem
