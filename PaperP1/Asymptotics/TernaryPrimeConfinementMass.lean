module

public import PaperP1.Asymptotics.TernaryPrimeConfinement
public import PaperP1.Combinatorics.LabeledPopulationCount

/-! # Positive weighted individual-prime confinement, including actual offset-pattern multiplicities -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TernaryPrimeConfinementMass

open Finset PaperP1.TernaryPrimeValueConfinement PaperP1.TernaryUnboundedCutoff
  PaperP1.TernaryPrimeConfinement PaperP1.TernaryGroupConfinement PaperP1.CriticalBandScale

theorem labeled_count (c ε : ℝ) (hc : 0 < c) (hε : 0 < ε) :
    ∃ k : ℕ, 3 ≤ k ∧ ∀ C : ℝ, ∀ D J : ℕ,
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L R : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → R ≤ D * (L + 1) →
      ∀ (α : Type*) [DecidableEq α], ∀ (F : Finset (α × (Fin 3 → ℕ)))
        (U : α → (Fin 3 → ℕ) → Fin 3 → Finset ℕ) (H : α → (Fin 3 → ℕ) → ℕ)
        (base : α → Fin 3 → ℕ), (F.image Prod.fst).card ≤ (L + 1) ^ J →
      (∀ z ∈ F, SourceConditions N R D (base z.1) (U z.1) (H z.1) z.2) →
      (∀ z ∈ F, threshold k N L c < (largePrimes (U z.1 z.2) (H z.1 z.2) (((L + 1 : ℕ) : ℝ) ^ c)).card) →
      (F.card : ℝ) ≤ (N : ℝ) ^ (budgetExponent c + ε) := by
  let δ := ε / 2
  obtain ⟨k, hk, hcount⟩ := uniform_prime_count c δ hc (by dsimp [δ]; positivity)
  refine ⟨k, hk, ?_⟩
  intro C D J
  obtain ⟨NC, _hNC, hcCount⟩ := hcount C D
  obtain ⟨NG, hg⟩ := critical_band_scale C
  obtain ⟨NP, hp⟩ := LogarithmicWordPowers.polynomial_factor_le_rpow_eventually upperScale upperScale_pos.le
    1 J δ (by dsimp [δ]; positivity)
  refine ⟨max 2 (max NC (max NG NP)), by omega, ?_⟩
  intro N hN L R hband hR α _instα F U H base hlabels hadm hbad
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hfibre (a : α) : (((F.filter fun z ↦ z.1 = a).image Prod.snd).card : ℝ) ≤
      (N : ℝ) ^ (budgetExponent c + δ) := by
    apply hcCount N (by omega) L R hband hR _ (U a) (H a) (base a)
    · intro X hX
      obtain ⟨z, hz, rfl⟩ := mem_image.mp hX
      obtain ⟨hzF, hza⟩ := mem_filter.mp hz
      simpa only [hza] using hadm z hzF
    · intro X hX
      obtain ⟨z, hz, rfl⟩ := mem_image.mp hX
      obtain ⟨hzF, hza⟩ := mem_filter.mp hz
      simpa only [hza] using hbad z hzF
  have hcard := LabeledPopulationCount.cardinal_le F ((N : ℝ) ^ (budgetExponent c + δ)) hfibre
  have hB := (hg N (by omega) L hband).2
  have hpoly : ((L + 1 : ℕ) : ℝ) ^ J ≤ (N : ℝ) ^ δ := by
    simpa only [one_mul, Nat.cast_add, Nat.cast_one, abs_of_nonneg (by positivity : 0 ≤ (L + 1 : ℝ) ^ J)]
      using hp N (by omega) L hB
  have hI : ((F.image Prod.fst).card : ℝ) ≤ (N : ℝ) ^ δ :=
    (show ((F.image Prod.fst).card : ℝ) ≤ ((L + 1 : ℕ) : ℝ) ^ J by exact_mod_cast hlabels).trans hpoly
  calc
    _ ≤ (N : ℝ) ^ δ * (N : ℝ) ^ (budgetExponent c + δ) :=
      hcard.trans (mul_le_mul_of_nonneg_right hI (by positivity))
    _ = _ := by rw [← Real.rpow_add hn]; congr 1; dsimp [δ]; ring

theorem mass_exponent (c β : ℝ) : -β + budgetExponent c = -min (β - 6 / 5) (β - 1 - 2 / c) := by
  unfold budgetExponent
  by_cases h : (6 / 5 : ℝ) ≤ 1 + 2 / c
  · rw [max_eq_right h, min_eq_right (by linarith)]
    ring
  · rw [max_eq_left (le_of_not_ge h), min_eq_left (by linarith)]
    ring

theorem prime_mass (c ε : ℝ) (hc : 0 < c) (hε : 0 < ε) :
    ∃ k : ℕ, 3 ≤ k ∧ ∀ C : ℝ, ∀ D J : ℕ,
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L R : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → R ≤ D * (L + 1) →
      ∀ (α : Type*) [DecidableEq α], ∀ (F : Finset (α × (Fin 3 → ℕ)))
        (U : α → (Fin 3 → ℕ) → Fin 3 → Finset ℕ) (H : α → (Fin 3 → ℕ) → ℕ)
        (base : α → Fin 3 → ℕ) (β : ℝ) (w : α × (Fin 3 → ℕ) → ℝ),
      (F.image Prod.fst).card ≤ (L + 1) ^ J →
      (∀ z ∈ F, SourceConditions N R D (base z.1) (U z.1) (H z.1) z.2) →
      (∀ z ∈ F, threshold k N L c < (largePrimes (U z.1 z.2) (H z.1 z.2) (((L + 1 : ℕ) : ℝ) ^ c)).card) →
      (∀ z ∈ F, 0 ≤ w z ∧ w z ≤ (N : ℝ) ^ (-β + ε / 2)) →
      (∑ z ∈ F, w z) ≤ (N : ℝ) ^ (-min (β - 6 / 5) (β - 1 - 2 / c) + ε) := by
  obtain ⟨k, hk, hcount⟩ := labeled_count c (ε / 2) hc (by positivity)
  refine ⟨k, hk, ?_⟩
  intro C D J
  obtain ⟨N₀, hN₀, hcCount⟩ := hcount C D J
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L R hband hR α _instα F U H base β w hlabels hadm hbad hw
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hcard := hcCount N hN L R hband hR α F U H base hlabels hadm hbad
  calc
    _ ≤ ∑ _z ∈ F, (N : ℝ) ^ (-β + ε / 2) := sum_le_sum (fun z hz ↦ (hw z hz).2)
    _ = (F.card : ℝ) * (N : ℝ) ^ (-β + ε / 2) := by simp only [sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ) ^ (budgetExponent c + ε / 2) * (N : ℝ) ^ (-β + ε / 2) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by
      rw [← Real.rpow_add hn]
      congr 1
      have h := mass_exponent c β
      linarith

def exceptional {α : Type*} [DecidableEq α] (F : Finset (α × (Fin 3 → ℕ)))
    (U : α → (Fin 3 → ℕ) → Fin 3 → Finset ℕ) (H : α → (Fin 3 → ℕ) → ℕ)
    (k N L : ℕ) (c : ℝ) : Finset (α × (Fin 3 → ℕ)) := by
  classical
  exact F.filter fun z ↦ threshold k N L c < (largePrimes (U z.1 z.2) (H z.1 z.2) (((L + 1 : ℕ) : ℝ) ^ c)).card

theorem actual_prime_confinement (c ε : ℝ) (hc : 0 < c) (hε : 0 < ε) :
    ∃ k : ℕ, 3 ≤ k ∧ ∀ C : ℝ, ∀ D J : ℕ,
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L R : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → R ≤ D * (L + 1) →
      ∀ (α : Type*) [DecidableEq α], ∀ (F : Finset (α × (Fin 3 → ℕ)))
        (U : α → (Fin 3 → ℕ) → Fin 3 → Finset ℕ) (H : α → (Fin 3 → ℕ) → ℕ)
        (base : α → Fin 3 → ℕ) (β : ℝ) (w : α × (Fin 3 → ℕ) → ℝ),
      (F.image Prod.fst).card ≤ (L + 1) ^ J →
      (∀ z ∈ F, SourceConditions N R D (base z.1) (U z.1) (H z.1) z.2) →
      (∀ z ∈ F, 0 ≤ w z ∧ w z ≤ (N : ℝ) ^ (-β + ε / 2)) →
      ((∑ z ∈ exceptional F U H k N L c, w z) ≤
          (N : ℝ) ^ (-min (β - 6 / 5) (β - 1 - 2 / c) + ε)) ∧
        ∀ z ∈ F \ exceptional F U H k N L c,
          (largePrimes (U z.1 z.2) (H z.1 z.2) (((L + 1 : ℕ) : ℝ) ^ c)).card ≤ threshold k N L c := by
  obtain ⟨k, hk, hm⟩ := prime_mass c ε hc hε
  refine ⟨k, hk, ?_⟩
  intro C D J
  obtain ⟨N₀, hN₀, hmass⟩ := hm C D J
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L R hband hR α _instα F U H base β w hlabels hadm hw
  classical
  have hsub : exceptional F U H k N L c ⊆ F := filter_subset _ _
  constructor
  · apply hmass N hN L R hband hR α (exceptional F U H k N L c) U H base β w
    · exact (card_le_card (image_subset_image hsub)).trans hlabels
    · intro z hz
      exact hadm z (hsub hz)
    · intro _ hz
      exact (mem_filter.mp hz).2
    · intro z hz
      exact hw z (hsub hz)
  · intro z hz
    obtain ⟨hzF, hzbad⟩ := mem_sdiff.mp hz
    by_contra hnot
    exact hzbad (mem_filter.mpr ⟨hzF, lt_of_not_ge hnot⟩)

end PaperP1.TernaryPrimeConfinementMass
