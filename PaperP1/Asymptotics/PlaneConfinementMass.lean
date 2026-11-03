module

public import PaperP1.Asymptotics.PlaneTernaryConfinement
public import PaperP1.Combinatorics.LabeledPopulationCount

/-! # The full fixed-plane confinement mass, simultaneously for groups and individual primes -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PlaneConfinementMass

open Finset PaperP1.TernaryUnboundedCutoff PaperP1.PlaneSupportCover
  PaperP1.PlaneTernaryConfinement PaperP1.CriticalBandScale

def Excessive (U : Fin 3 → Finset ℕ) (H k N L : ℕ) (c : ℝ) : Prop :=
  TernaryGroupConfinement.threshold k N L c < (TernaryValueConfinement.largeSupports U H (((L + 1 : ℕ) : ℝ) ^ c)).card ∨
    TernaryGroupConfinement.threshold k N L c < (TernaryPrimeValueConfinement.largePrimes U H (((L + 1 : ℕ) : ℝ) ^ c)).card

theorem labeled_count (c ε : ℝ) (hc : 0 < c) (hε : 0 < ε) :
    ∃ k : ℕ, 3 ≤ k ∧ ∀ C : ℝ, ∀ D J K : ℕ,
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L R : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → R ≤ D * (L + 1) →
      ∀ (α : Type*) [DecidableEq α], ∀ (F : Finset (α × (Fin 3 → ℕ)))
        (U : α → (Fin 3 → ℕ) → Fin 3 → Finset ℕ) (H : α → (Fin 3 → ℕ) → ℕ)
        (base : α → Fin 3 → ℕ) (planes : α → Finset Plane),
      (F.image Prod.fst).card ≤ (L + 1) ^ J →
      (∀ a ∈ F.image Prod.fst, (planes a).card ≤ (L + 1) ^ K) →
      (∀ z ∈ F, SourceConditions N R D (base z.1) (U z.1) (H z.1) z.2) →
      (∀ z ∈ F, ∃ P ∈ planes z.1, P.1 ≠ 0 ∧ (∑ i, P.1 i * (z.2 i : ℝ)) = P.2) →
      (∀ z ∈ F, Excessive (U z.1 z.2) (H z.1 z.2) k N L c) →
      (F.card : ℝ) ≤ (N : ℝ) ^ (budgetExponent c + ε) := by
  let δ := ε / 2
  obtain ⟨k, hk, hcount⟩ := uniform_count c δ hc (by dsimp [δ]; positivity)
  refine ⟨k, hk, ?_⟩
  intro C D J K
  obtain ⟨NC, _hNC, hcCount⟩ := hcount C D K
  obtain ⟨NG, hg⟩ := critical_band_scale C
  obtain ⟨NP, hp⟩ := LogarithmicWordPowers.polynomial_factor_le_rpow_eventually upperScale upperScale_pos.le
    1 J δ (by dsimp [δ]; positivity)
  refine ⟨max 2 (max NC (max NG NP)), by omega, ?_⟩
  intro N hN L R hband hR α _instα F U H base planes hlabels hplaneCard hadm hplane hbad
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hfibre (a : α) (ha : a ∈ F.image Prod.fst) :
      (((F.filter fun z ↦ z.1 = a).image Prod.snd).card : ℝ) ≤ (N : ℝ) ^ (budgetExponent c + δ) := by
    apply hcCount N (by omega) L R hband hR _ (U a) (H a) (base a) (planes a) (hplaneCard a ha)
    · intro X hX
      obtain ⟨z, hz, rfl⟩ := mem_image.mp hX
      obtain ⟨hzF, hza⟩ := mem_filter.mp hz
      simpa only [hza] using hadm z hzF
    · intro X hX
      obtain ⟨z, hz, rfl⟩ := mem_image.mp hX
      obtain ⟨hzF, hza⟩ := mem_filter.mp hz
      simpa only [hza] using hplane z hzF
    · intro X hX
      obtain ⟨z, hz, rfl⟩ := mem_image.mp hX
      obtain ⟨hzF, hza⟩ := mem_filter.mp hz
      simpa only [Excessive, hza] using hbad z hzF
  have hcard := LabeledPopulationCount.cardinal_le_on F ((N : ℝ) ^ (budgetExponent c + δ)) hfibre
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

theorem mass_exponent (c β : ℝ) : -β + budgetExponent c = -min (β - 6 / 5) (β - 1 - 1 / c) := by
  unfold budgetExponent
  by_cases h : (6 / 5 : ℝ) ≤ 1 + 1 / c
  · rw [max_eq_right h, min_eq_right (by linarith)]
    ring
  · rw [max_eq_left (le_of_not_ge h), min_eq_left (by linarith)]
    ring

theorem excessive_mass (c ε : ℝ) (hc : 0 < c) (hε : 0 < ε) :
    ∃ k : ℕ, 3 ≤ k ∧ ∀ C : ℝ, ∀ D J K : ℕ,
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L R : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → R ≤ D * (L + 1) →
      ∀ (α : Type*) [DecidableEq α], ∀ (F : Finset (α × (Fin 3 → ℕ)))
        (U : α → (Fin 3 → ℕ) → Fin 3 → Finset ℕ) (H : α → (Fin 3 → ℕ) → ℕ)
        (base : α → Fin 3 → ℕ) (planes : α → Finset Plane) (β : ℝ) (w : α × (Fin 3 → ℕ) → ℝ),
      (F.image Prod.fst).card ≤ (L + 1) ^ J →
      (∀ a ∈ F.image Prod.fst, (planes a).card ≤ (L + 1) ^ K) →
      (∀ z ∈ F, SourceConditions N R D (base z.1) (U z.1) (H z.1) z.2) →
      (∀ z ∈ F, ∃ P ∈ planes z.1, P.1 ≠ 0 ∧ (∑ i, P.1 i * (z.2 i : ℝ)) = P.2) →
      (∀ z ∈ F, Excessive (U z.1 z.2) (H z.1 z.2) k N L c) →
      (∀ z ∈ F, 0 ≤ w z ∧ w z ≤ (N : ℝ) ^ (-β + ε / 2)) →
      (∑ z ∈ F, w z) ≤ (N : ℝ) ^ (-min (β - 6 / 5) (β - 1 - 1 / c) + ε) := by
  obtain ⟨k, hk, hcount⟩ := labeled_count c (ε / 2) hc (by positivity)
  refine ⟨k, hk, ?_⟩
  intro C D J K
  obtain ⟨N₀, hN₀, hcCount⟩ := hcount C D J K
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L R hband hR α _instα F U H base planes β w hlabels hplaneCard hadm hplane hbad hw
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hcard := hcCount N hN L R hband hR α F U H base planes hlabels hplaneCard hadm hplane hbad
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
  exact F.filter fun z ↦ Excessive (U z.1 z.2) (H z.1 z.2) k N L c

theorem actual_plane_confinement (c ε : ℝ) (hc : 0 < c) (hε : 0 < ε) :
    ∃ k : ℕ, 3 ≤ k ∧ ∀ C : ℝ, ∀ D J K : ℕ,
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L R : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → R ≤ D * (L + 1) →
      ∀ (α : Type*) [DecidableEq α], ∀ (F : Finset (α × (Fin 3 → ℕ)))
        (U : α → (Fin 3 → ℕ) → Fin 3 → Finset ℕ) (H : α → (Fin 3 → ℕ) → ℕ)
        (base : α → Fin 3 → ℕ) (planes : α → Finset Plane) (β : ℝ) (w : α × (Fin 3 → ℕ) → ℝ),
      (F.image Prod.fst).card ≤ (L + 1) ^ J →
      (∀ a ∈ F.image Prod.fst, (planes a).card ≤ (L + 1) ^ K) →
      (∀ z ∈ F, SourceConditions N R D (base z.1) (U z.1) (H z.1) z.2) →
      (∀ z ∈ F, ∃ P ∈ planes z.1, P.1 ≠ 0 ∧ (∑ i, P.1 i * (z.2 i : ℝ)) = P.2) →
      (∀ z ∈ F, 0 ≤ w z ∧ w z ≤ (N : ℝ) ^ (-β + ε / 2)) →
      ((∑ z ∈ exceptional F U H k N L c, w z) ≤
          (N : ℝ) ^ (-min (β - 6 / 5) (β - 1 - 1 / c) + ε)) ∧
        ∀ z ∈ F \ exceptional F U H k N L c,
          (TernaryValueConfinement.largeSupports (U z.1 z.2) (H z.1 z.2) (((L + 1 : ℕ) : ℝ) ^ c)).card ≤ TernaryGroupConfinement.threshold k N L c ∧
          (TernaryPrimeValueConfinement.largePrimes (U z.1 z.2) (H z.1 z.2) (((L + 1 : ℕ) : ℝ) ^ c)).card ≤ TernaryGroupConfinement.threshold k N L c := by
  obtain ⟨k, hk, hm⟩ := excessive_mass c ε hc hε
  refine ⟨k, hk, ?_⟩
  intro C D J K
  obtain ⟨N₀, hN₀, hmass⟩ := hm C D J K
  refine ⟨N₀, hN₀, ?_⟩
  intro N hN L R hband hR α _instα F U H base planes β w hlabels hplaneCard hadm hplane hw
  classical
  have hsub : exceptional F U H k N L c ⊆ F := filter_subset _ _
  constructor
  · apply hmass N hN L R hband hR α (exceptional F U H k N L c) U H base planes β w
    · exact (card_le_card (image_subset_image hsub)).trans hlabels
    · intro a ha
      exact hplaneCard a (image_subset_image hsub ha)
    · intro z hz
      exact hadm z (hsub hz)
    · intro z hz
      exact hplane z (hsub hz)
    · intro _ hz
      exact (mem_filter.mp hz).2
    · intro z hz
      exact hw z (hsub hz)
  · intro z hz
    obtain ⟨hzF, hzbad⟩ := mem_sdiff.mp hz
    have hnot : ¬ Excessive (U z.1 z.2) (H z.1 z.2) k N L c := fun he ↦ hzbad (mem_filter.mpr ⟨hzF, he⟩)
    constructor
    · by_contra hgt
      exact hnot (Or.inl (lt_of_not_ge hgt))
    · by_contra hgt
      exact hnot (Or.inr (lt_of_not_ge hgt))

end PaperP1.PlaneConfinementMass
