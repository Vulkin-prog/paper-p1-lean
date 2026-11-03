module

public import PaperP1.Asymptotics.PlaneConfinementNegligibility
public import PaperP1.Asymptotics.TernaryConfinementMass
public import PaperP1.Asymptotics.TernaryPrimeConfinementMass
public import PaperP1.Asymptotics.TernaryGroupNegligibility

/-! # Companion T21.4: one actual exceptional set for groups and individual primes -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PolylogConfinementTheorem

open Finset Filter PaperP1.TernaryUnboundedCutoff PaperP1.TernaryGroupConfinement
  PaperP1.PlaneConfinementMass

theorem threshold_mono {k l N L : ℕ} {c : ℝ} (hkl : k ≤ l) : threshold k N L c ≤ threshold l N L c := by
  unfold threshold
  omega

theorem positive_union_bound {α : Type*} [DecidableEq α] (F J G P : Finset α) (w : α → ℝ)
    (hJ : J ⊆ G ∪ P) (hG : G ⊆ F) (hP : P ⊆ F) (hw : ∀ z ∈ F, 0 ≤ w z) :
    (∑ z ∈ J, w z) ≤ (∑ z ∈ G, w z) + ∑ z ∈ P, w z := by
  have hsub : G ∪ P ⊆ F := union_subset hG hP
  have hle : (∑ z ∈ J, w z) ≤ ∑ z ∈ G ∪ P, w z :=
    sum_le_sum_of_subset_of_nonneg hJ (fun z hz _ ↦ hw z (hsub hz))
  have hid := sum_union_inter (s₁ := G) (s₂ := P) (f := w)
  have hint : 0 ≤ ∑ z ∈ G ∩ P, w z := sum_nonneg (fun z hz ↦ hw z (hG (mem_inter.mp hz).1))
  linarith

theorem companion_T21_4_three_dimensional (c ε : ℝ) (hc : 0 < c) (hε : 0 < ε) :
    ∃ k : ℕ, 3 ≤ k ∧ ∀ C : ℝ, ∀ D J : ℕ,
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L R : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → R ≤ D * (L + 1) →
      ∀ (α : Type*) [DecidableEq α], ∀ (F : Finset (α × (Fin 3 → ℕ)))
        (U : α → (Fin 3 → ℕ) → Fin 3 → Finset ℕ) (H : α → (Fin 3 → ℕ) → ℕ)
        (base : α → Fin 3 → ℕ) (β : ℝ) (w : α × (Fin 3 → ℕ) → ℝ),
      (F.image Prod.fst).card ≤ (L + 1) ^ J →
      (∀ z ∈ F, SourceConditions N R D (base z.1) (U z.1) (H z.1) z.2) →
      (∀ z ∈ F, 0 ≤ w z ∧ w z ≤ (N : ℝ) ^ (-β + ε / 4)) →
      ((∑ z ∈ exceptional F U H k N L c, w z) ≤
          (N : ℝ) ^ (-min (β - 6 / 5) (β - 1 - 2 / c) + ε)) ∧
        ∀ z ∈ F \ exceptional F U H k N L c,
          (TernaryValueConfinement.largeSupports (U z.1 z.2) (H z.1 z.2) (((L + 1 : ℕ) : ℝ) ^ c)).card ≤ threshold k N L c ∧
          (TernaryPrimeValueConfinement.largePrimes (U z.1 z.2) (H z.1 z.2) (((L + 1 : ℕ) : ℝ) ^ c)).card ≤ threshold k N L c := by
  obtain ⟨kg, hkg, hgroups⟩ := TernaryConfinementMass.actual_group_confinement c (ε / 2) hc (by positivity)
  obtain ⟨kp, hkp, hprimes⟩ := TernaryPrimeConfinementMass.actual_prime_confinement c (ε / 2) hc (by positivity)
  let k := max kg kp
  have hkgk : kg ≤ k := le_max_left _ _
  have hkpk : kp ≤ k := le_max_right _ _
  refine ⟨k, hkg.trans hkgk, ?_⟩
  intro C D J
  obtain ⟨NG, _hNG, hg⟩ := hgroups C D J
  obtain ⟨NP, _hNP, hp⟩ := hprimes C D J
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 2 0 (ε / 2) (by positivity)
  refine ⟨max 2 (max NG (max NP NF)), by omega, ?_⟩
  intro N hN L R hband hR α _instα F U H base β w hlabels hadm hw
  classical
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hw' : ∀ z ∈ F, 0 ≤ w z ∧ w z ≤ (N : ℝ) ^ (-β + (ε / 2) / 2) := by
    simpa only [show (ε / 2) / 2 = ε / 4 by ring] using hw
  obtain ⟨hgmass, _hgconf⟩ := hg N (by omega) L R hband hR α F U H base β w hlabels hadm hw'
  obtain ⟨hpmass, _hpconf⟩ := hp N (by omega) L R hband hR α F U H base β w hlabels hadm hw'
  let G := TernaryConfinementMass.exceptional F U H kg N L c
  let P := TernaryPrimeConfinementMass.exceptional F U H kp N L c
  let E := exceptional F U H k N L c
  have hGF : G ⊆ F := filter_subset _ _
  have hPF : P ⊆ F := filter_subset _ _
  have hcover : E ⊆ G ∪ P := by
    intro z hz
    obtain ⟨hzF, hbad⟩ := mem_filter.mp hz
    rcases hbad with hbadG | hbadP
    · exact mem_union.mpr (Or.inl (mem_filter.mpr ⟨hzF, (threshold_mono hkgk).trans_lt hbadG⟩))
    · exact mem_union.mpr (Or.inr (mem_filter.mpr ⟨hzF, (threshold_mono hkpk).trans_lt hbadP⟩))
  constructor
  · have hunion := positive_union_bound F E G P w hcover hGF hPF (fun z hz ↦ (hw z hz).1)
    have htwo : (2 : ℝ) ≤ (N : ℝ) ^ (ε / 2) := by
      simpa only [Real.rpow_zero, mul_one, zero_add] using hf N (by omega)
    calc
      _ ≤ 2 * (N : ℝ) ^ (-min (β - 6 / 5) (β - 1 - 2 / c) + ε / 2) := by
        linarith [hunion, hgmass, hpmass]
      _ ≤ (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (-min (β - 6 / 5) (β - 1 - 2 / c) + ε / 2) :=
        mul_le_mul_of_nonneg_right htwo (by positivity)
      _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring
  · intro z hz
    obtain ⟨hzF, hzbad⟩ := mem_sdiff.mp hz
    have hnot : ¬ Excessive (U z.1 z.2) (H z.1 z.2) k N L c := fun he ↦ hzbad (mem_filter.mpr ⟨hzF, he⟩)
    constructor
    · by_contra hgt
      exact hnot (Or.inl (lt_of_not_ge hgt))
    · by_contra hgt
      exact hnot (Or.inr (lt_of_not_ge hgt))

theorem three_dimensional_sufficient_cutoff (c : ℝ) (hc : 6 < c) :
    ∃ θ : ℝ, 0 < θ ∧ ∃ k : ℕ, 3 ≤ k ∧ ∀ C : ℝ, ∀ D J : ℕ, ∀ η : ℝ, 0 < η →
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L R : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → R ≤ D * (L + 1) →
      ∀ (α : Type*) [DecidableEq α], ∀ (F : Finset (α × (Fin 3 → ℕ)))
        (U : α → (Fin 3 → ℕ) → Fin 3 → Finset ℕ) (H : α → (Fin 3 → ℕ) → ℕ)
        (base : α → Fin 3 → ℕ) (w : α × (Fin 3 → ℕ) → ℝ),
      (F.image Prod.fst).card ≤ (L + 1) ^ J →
      (∀ z ∈ F, SourceConditions N R D (base z.1) (U z.1) (H z.1) z.2) →
      (∀ z ∈ F, 0 ≤ w z ∧ w z ≤ (N : ℝ) ^ (-2 + θ)) →
      ((∑ z ∈ exceptional F U H k N L c, w z) ≤ η * L * (N : ℝ) ^ (-2 / 3 : ℝ)) ∧
        ∀ z ∈ F \ exceptional F U H k N L c,
          (TernaryValueConfinement.largeSupports (U z.1 z.2) (H z.1 z.2) (((L + 1 : ℕ) : ℝ) ^ c)).card ≤ threshold k N L c ∧
          (TernaryPrimeValueConfinement.largePrimes (U z.1 z.2) (H z.1 z.2) (((L + 1 : ℕ) : ℝ) ^ c)).card ≤ threshold k N L c := by
  let δ := (4 / 3 - budgetExponent c) / 2
  have hδ : 0 < δ := by dsimp [δ]; exact div_pos (TernaryGroupNegligibility.exponent_gap c hc) (by norm_num)
  obtain ⟨k, hk, hmass⟩ := companion_T21_4_three_dimensional c δ (by linarith) hδ
  refine ⟨δ / 4, by positivity, k, hk, ?_⟩
  intro C D J η hη
  obtain ⟨NM, _hNM, hm⟩ := hmass C D J
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  have hlim : Tendsto (fun N : ℕ ↦ (N : ℝ) ^ (-δ)) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hδ).comp (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨NE, he⟩ := eventually_atTop.mp (hlim.eventually (eventually_lt_nhds hη))
  refine ⟨max 2 (max NM (max NG NE)), by omega, ?_⟩
  intro N hN L R hband hR α _instα F U H base w hlabels hadm hw
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL : (1 : ℝ) ≤ L := by
    have hb := (hg N (by omega) L hband).2.2.1
    exact_mod_cast (by omega : 1 ≤ L)
  obtain ⟨hbound, hconf⟩ := hm N (by omega) L R hband hR α F U H base 2 w hlabels hadm hw
  refine ⟨?_, hconf⟩
  have hid : (N : ℝ) ^ (-min ((2 : ℝ) - 6 / 5) (2 - 1 - 2 / c) + δ) =
      (N : ℝ) ^ (-δ) * (N : ℝ) ^ (-2 / 3 : ℝ) := by
    rw [← Real.rpow_add hn]
    congr 1
    have hm := TernaryConfinementMass.mass_exponent c 2
    dsimp only [δ]
    linarith
  calc
    _ ≤ (N : ℝ) ^ (-δ) * (N : ℝ) ^ (-2 / 3 : ℝ) := by simpa only [hid] using hbound
    _ ≤ η * (N : ℝ) ^ (-2 / 3 : ℝ) := mul_le_mul_of_nonneg_right (he N (by omega)).le (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_right (by nlinarith : η ≤ η * (L : ℝ)) (by positivity)

end PaperP1.PolylogConfinementTheorem
