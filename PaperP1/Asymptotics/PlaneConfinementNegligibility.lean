module

public import PaperP1.Asymptotics.PlaneConfinementMass

/-! # The sufficient c>3 cutoff on polynomial families of genuine real planes -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PlaneConfinementNegligibility

open Finset Filter PaperP1.PlaneConfinementMass PaperP1.PlaneTernaryConfinement
  PaperP1.PlaneSupportCover PaperP1.TernaryUnboundedCutoff

theorem exponent_gap (c : ℝ) (hc : 3 < c) : 0 < 4 / 3 - budgetExponent c := by
  have hcp : 0 < c := by linarith
  have hfrac : 1 / c < (1 / 3 : ℝ) := (div_lt_iff₀ hcp).mpr (by linarith)
  apply sub_pos.mpr
  exact max_lt (by norm_num) (by linarith)

theorem sufficient_cutoff (c : ℝ) (hc : 3 < c) :
    ∃ θ : ℝ, 0 < θ ∧ ∃ k : ℕ, 3 ≤ k ∧ ∀ C : ℝ, ∀ D J K : ℕ, ∀ η : ℝ, 0 < η →
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L R : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → R ≤ D * (L + 1) →
      ∀ (α : Type*) [DecidableEq α], ∀ (F : Finset (α × (Fin 3 → ℕ)))
        (U : α → (Fin 3 → ℕ) → Fin 3 → Finset ℕ) (H : α → (Fin 3 → ℕ) → ℕ)
        (base : α → Fin 3 → ℕ) (planes : α → Finset Plane) (w : α × (Fin 3 → ℕ) → ℝ),
      (F.image Prod.fst).card ≤ (L + 1) ^ J →
      (∀ a ∈ F.image Prod.fst, (planes a).card ≤ (L + 1) ^ K) →
      (∀ z ∈ F, SourceConditions N R D (base z.1) (U z.1) (H z.1) z.2) →
      (∀ z ∈ F, ∃ P ∈ planes z.1, P.1 ≠ 0 ∧ (∑ i, P.1 i * (z.2 i : ℝ)) = P.2) →
      (∀ z ∈ F, 0 ≤ w z ∧ w z ≤ (N : ℝ) ^ (-2 + θ)) →
      ((∑ z ∈ exceptional F U H k N L c, w z) ≤ η * L * (N : ℝ) ^ (-2 / 3 : ℝ)) ∧
        ∀ z ∈ F \ exceptional F U H k N L c,
          (TernaryValueConfinement.largeSupports (U z.1 z.2) (H z.1 z.2) (((L + 1 : ℕ) : ℝ) ^ c)).card ≤ TernaryGroupConfinement.threshold k N L c ∧
          (TernaryPrimeValueConfinement.largePrimes (U z.1 z.2) (H z.1 z.2) (((L + 1 : ℕ) : ℝ) ^ c)).card ≤ TernaryGroupConfinement.threshold k N L c := by
  let δ := (4 / 3 - budgetExponent c) / 2
  have hδ : 0 < δ := by dsimp [δ]; exact div_pos (exponent_gap c hc) (by norm_num)
  obtain ⟨k, hk, hmass⟩ := actual_plane_confinement c δ (by linarith) hδ
  refine ⟨δ / 2, by positivity, k, hk, ?_⟩
  intro C D J K η hη
  obtain ⟨NM, _hNM, hm⟩ := hmass C D J K
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  have hlim : Tendsto (fun N : ℕ ↦ (N : ℝ) ^ (-δ)) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hδ).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨NE, he⟩ := eventually_atTop.mp (hlim.eventually (eventually_lt_nhds hη))
  refine ⟨max 2 (max NM (max NG NE)), by omega, ?_⟩
  intro N hN L R hband hR α _instα F U H base planes w hlabels hplaneCard hadm hplane hw
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL : (1 : ℝ) ≤ L := by
    have hb := (hg N (by omega) L hband).2.2.1
    exact_mod_cast (by omega : 1 ≤ L)
  obtain ⟨hbound, hconf⟩ := hm N (by omega) L R hband hR α F U H base planes 2 w hlabels hplaneCard hadm hplane hw
  refine ⟨?_, hconf⟩
  have hid : (N : ℝ) ^ (-min ((2 : ℝ) - 6 / 5) (2 - 1 - 1 / c) + δ) =
      (N : ℝ) ^ (-δ) * (N : ℝ) ^ (-2 / 3 : ℝ) := by
    rw [← Real.rpow_add hn]
    congr 1
    have hm := mass_exponent c 2
    dsimp only [δ]
    linarith
  calc
    _ ≤ (N : ℝ) ^ (-δ) * (N : ℝ) ^ (-2 / 3 : ℝ) := by simpa only [hid] using hbound
    _ ≤ η * (N : ℝ) ^ (-2 / 3 : ℝ) := mul_le_mul_of_nonneg_right (he N (by omega)).le (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right (by nlinarith : η ≤ η * (L : ℝ)) (by positivity)

end PaperP1.PlaneConfinementNegligibility
