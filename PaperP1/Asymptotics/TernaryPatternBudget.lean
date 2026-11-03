module

public import PaperP1.Asymptotics.TernaryGroupBudget
public import PaperP1.Arithmetic.TernaryLargestSelection

/-! # The full ternary budget with polynomially many actual offset-pattern labels -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TernaryPatternBudget

open Finset PaperP1.TernaryTopProducts PaperP1.TernaryBudgetDomain PaperP1.CriticalBandScale

theorem uniform_bound (C : ℝ) (D k J : ℕ) (hk : 3 ≤ k)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L R : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → R ≤ D * (L + 1) →
      ∀ (α : Type*) [DecidableEq α], ∀ (F : Finset (α × (Fin 3 → ℕ))) (U : α → (Fin 3 → ℕ) → Fin 3 → Finset ℕ)
        (H : α → (Fin 3 → ℕ) → ℕ) (base : α → Fin 3 → ℕ) (T : ℝ), 1 ≤ T →
      (F.image Prod.fst).card ≤ (L + 1) ^ J →
      (∀ z ∈ F, Admissible N L R D (base z.1) (U z.1) (H z.1) z.2) →
      (∀ z ∈ F, T < (topProduct (U z.1 z.2) (H z.1 z.2) k : ℝ)) →
      (F.card : ℝ) ≤ (N : ℝ) ^ ε * ((N : ℝ) ^ 3 * T ^ (-2 : ℝ) + (N : ℝ) ^ (6 / 5 : ℝ)) := by
  let δ := ε / 2
  obtain ⟨NG, _hNG, hg⟩ := TernaryGroupBudget.uniform_bound C D k hk δ (by dsimp [δ]; positivity)
  obtain ⟨NS, hs⟩ := critical_band_scale C
  obtain ⟨NP, hp⟩ := LogarithmicWordPowers.polynomial_factor_le_rpow_eventually
    upperScale upperScale_pos.le 1 J δ (by dsimp [δ]; positivity)
  refine ⟨max 2 (max NG (max NS NP)), by omega, ?_⟩
  intro N hN L R hband hR α _instα F U H base T hT hlabels hadm hprod
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  let B : ℝ := (N : ℝ) ^ 3 * T ^ (-2 : ℝ) + (N : ℝ) ^ (6 / 5 : ℝ)
  let I := F.image Prod.fst
  let fibre (a : α) := F.filter fun z ↦ z.1 = a
  let centers (a : α) := (fibre a).image Prod.snd
  have hcenter (a : α) : ((centers a).card : ℝ) ≤ (N : ℝ) ^ δ * B := by
    apply hg N (by omega) L R hband hR (centers a) (U a) (H a) (base a) T hT
    · intro X hX
      obtain ⟨z, hz, rfl⟩ := mem_image.mp hX
      obtain ⟨hzF, hza⟩ := mem_filter.mp hz
      simpa only [hza] using hadm z hzF
    · intro X hX
      obtain ⟨z, hz, rfl⟩ := mem_image.mp hX
      obtain ⟨hzF, hza⟩ := mem_filter.mp hz
      simpa only [hza] using hprod z hzF
  have hfibre (a : α) : ((fibre a).card : ℝ) ≤ (N : ℝ) ^ δ * B := by
    have hinj : Set.InjOn (fun z : α × (Fin 3 → ℕ) ↦ z.2) (fibre a) := by
      intro z hz w hw heq
      apply Prod.ext
      · exact (mem_filter.mp hz).2.trans (mem_filter.mp hw).2.symm
      · exact heq
    rw [← card_image_of_injOn hinj]
    exact hcenter a
  have hcover : ∀ z ∈ F, ∃ a ∈ I, z ∈ fibre a := by
    intro z hz
    exact ⟨z.1, mem_image_of_mem _ hz, mem_filter.mpr ⟨hz, rfl⟩⟩
  have hcount := FiniteCoverCount.cardinal_le F I fibre ((N : ℝ) ^ δ * B) hcover
    (fun a _ ↦ hfibre a)
  have hL := (hs N (by omega) L hband).2
  have hpoly : ((L + 1 : ℕ) : ℝ) ^ J ≤ (N : ℝ) ^ δ := by
    simpa only [one_mul, Nat.cast_add, Nat.cast_one, abs_of_nonneg (by positivity : 0 ≤ (L + 1 : ℝ) ^ J)]
      using hp N (by omega) L hL
  have hI : (I.card : ℝ) ≤ (N : ℝ) ^ δ :=
    (show (I.card : ℝ) ≤ ((L + 1 : ℕ) : ℝ) ^ J by exact_mod_cast hlabels).trans hpoly
  calc
    _ ≤ (N : ℝ) ^ δ * ((N : ℝ) ^ δ * B) := hcount.trans (mul_le_mul_of_nonneg_right hI (by dsimp [B]; positivity))
    _ = ((N : ℝ) ^ δ * (N : ℝ) ^ δ) * B := by ring
    _ = _ := by rw [← Real.rpow_add hn]; congr 2; dsimp [δ]; ring

end PaperP1.TernaryPatternBudget
