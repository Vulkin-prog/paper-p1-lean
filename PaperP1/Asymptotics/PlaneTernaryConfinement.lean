module

public import PaperP1.Asymptotics.PlaneRankinCritical
public import PaperP1.Asymptotics.TernaryPrimeTheorem
public import PaperP1.Asymptotics.PolylogConfinementScales
public import PaperP1.Asymptotics.TernaryGroupConfinement
public import PaperP1.Arithmetic.TernaryValueConfinement
public import PaperP1.Arithmetic.TernaryPrimeValueConfinement

/-! # Simultaneous support-group and individual-prime confinement on actual real planes -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PlaneTernaryConfinement

open Finset PaperP1.TernaryUnboundedCutoff PaperP1.PlaneSupportCover

def budgetExponent (c : ℝ) : ℝ := max (6 / 5) (1 + 1 / c)

theorem first_term_bound (N : ℕ) (hN : 1 ≤ N) (δ m : ℝ) (hm : 6 / 5 ≤ m) :
    (N : ℝ) ^ δ * ((N : ℝ) + (N : ℝ) ^ (6 / 5 : ℝ)) ≤ 2 * (N : ℝ) ^ (m + δ) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hsmall : (N : ℝ) ≤ (N : ℝ) ^ (6 / 5 : ℝ) := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (1 : ℝ) ≤ 6 / 5)
  have hbig : (N : ℝ) ^ (6 / 5 + δ) ≤ (N : ℝ) ^ (m + δ) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (add_le_add hm le_rfl)
  have heq : (N : ℝ) ^ δ * (N : ℝ) ^ (6 / 5 : ℝ) = (N : ℝ) ^ (6 / 5 + δ) := by
    rw [← Real.rpow_add hn]
    congr 1
    ring
  nlinarith [mul_le_mul_of_nonneg_left hsmall (by positivity : 0 ≤ (N : ℝ) ^ δ)]

theorem uniform_count (c ε : ℝ) (hc : 0 < c) (hε : 0 < ε) :
    ∃ k : ℕ, 3 ≤ k ∧ ∀ C : ℝ, ∀ D J : ℕ,
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L R : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → R ≤ D * (L + 1) →
      ∀ (F : Finset (Fin 3 → ℕ)) (U : (Fin 3 → ℕ) → Fin 3 → Finset ℕ)
        (H : (Fin 3 → ℕ) → ℕ) (base : Fin 3 → ℕ) (planes : Finset Plane), planes.card ≤ (L + 1) ^ J →
      (∀ X ∈ F, SourceConditions N R D base U H X) →
      (∀ X ∈ F, ∃ P ∈ planes, P.1 ≠ 0 ∧ (∑ i, P.1 i * (X i : ℝ)) = P.2) →
      (∀ X ∈ F,
        TernaryGroupConfinement.threshold k N L c < (TernaryValueConfinement.largeSupports (U X) (H X) (((L + 1 : ℕ) : ℝ) ^ c)).card ∨
        TernaryGroupConfinement.threshold k N L c < (TernaryPrimeValueConfinement.largePrimes (U X) (H X) (((L + 1 : ℕ) : ℝ) ^ c)).card) →
      (F.card : ℝ) ≤ (N : ℝ) ^ (budgetExponent c + ε) := by
  obtain ⟨k, hk, ζ, hζ, hζ1, hp⟩ := PolylogConfinementScales.choose_parameters c (ε / 2) hc (by positivity)
  refine ⟨k, hk, ?_⟩
  intro C D J
  let δ := ε / 2
  obtain ⟨NT, _hNT, ht⟩ := TernaryGroupBudget.uniform_bound C (2 * D + 1) k hk δ (by dsimp [δ]; positivity)
  obtain ⟨NP, _hNP, hprime⟩ := TernaryPrimeTheorem.population_bound C D k hk δ (by dsimp [δ]; positivity)
  obtain ⟨NC, _hNC, hcCount⟩ := PlaneRankinCritical.uniform_bound C c hc D k J (by omega)
    ζ (ε / 4) hζ hζ1 (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 5 (budgetExponent c + δ) δ (by dsimp [δ]; positivity)
  refine ⟨max 2 (max NT (max NP (max NC (max NG NF)))), by omega, ?_⟩
  intro N hN L R hband hR F U H base planes hplanes hadm hplane hbad
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hgeom := hg N (by omega) L hband
  have hB : (1 : ℝ) < ((L + 1 : ℕ) : ℝ) := by exact_mod_cast (by have := hgeom.2.2.1; omega : 1 < L + 1)
  let Y := ((L + 1 : ℕ) : ℝ) ^ c
  let V := (N : ℝ) ^ (1 + 1 / (k : ℝ))
  have hY : 1 < Y := Real.one_lt_rpow hB hc
  have hV : 0 ≤ V := by dsimp [V]; positivity
  let firstG := F.filter fun X ↦ (N : ℝ) < (TernaryTopProducts.topProduct (U X) (H X) k : ℝ)
  let firstP := F.filter fun X ↦ (N : ℝ) < (TernaryPrimeTopProducts.topProduct (U X) (H X) k : ℝ)
  let second := F.filter fun X ↦ (TernaryTopProducts.topProduct (U X) (H X) k : ℝ) ≤ N ∧
    (TernaryPrimeTopProducts.topProduct (U X) (H X) k : ℝ) ≤ N
  have hGF : firstG ⊆ F := filter_subset _ _
  have hPF : firstP ⊆ F := filter_subset _ _
  have hSF : second ⊆ F := filter_subset _ _
  have hR' : R ≤ (2 * D + 1) * (L + 1) := hR.trans (Nat.mul_le_mul_right _ (by omega : D ≤ 2 * D + 1))
  have hG := ht N (by omega) L R hband hR' firstG U (fun X ↦ min (H X) (2 * R + 1)) base N hn1
    (fun X hX ↦ ((hadm X (hGF hX)).capped hR).toAdmissible) (by
      intro X hX
      exact (mem_filter.mp hX).2.trans_le (by
        exact_mod_cast TernaryCutoffMonotonicity.top_product_le (U X) k (min_le_left (H X) (2 * R + 1))))
  have hP := hprime N (by omega) L R hband hR firstP U H base N hn1
    (fun X hX ↦ hadm X (hPF hX)) (fun _ hX ↦ (mem_filter.mp hX).2)
  have hpow : (N : ℝ) ^ 3 * (N : ℝ) ^ (-2 : ℝ) = (N : ℝ) := by
    rw [← Real.rpow_natCast (N : ℝ) 3, ← Real.rpow_add hn]
    norm_num
  rw [hpow] at hG hP
  have hterm := first_term_bound N (by omega) δ (budgetExponent c) (le_max_left _ _)
  have hG' : (firstG.card : ℝ) ≤ 2 * (N : ℝ) ^ (budgetExponent c + δ) := hG.trans hterm
  have hP' : (firstP.card : ℝ) ≤ 2 * (N : ℝ) ^ (budgetExponent c + δ) := hP.trans hterm
  have hcert : second ⊆ PlaneSupportCover.certificates base N D R Y V planes := by
    intro X hX
    have hxF := hSF hX
    have hdomain := hadm X hxF
    have hbounds := (mem_filter.mp hX).2
    have hlog : Real.log Y = c * Real.log ((L + 1 : ℕ) : ℝ) := Real.log_rpow (by linarith : 0 < ((L + 1 : ℕ) : ℝ)) c
    have hold : X ∈ CRTSupportCover.certificates base N D R Y V := by
      rcases hbad X hxF with hbadG | hbadP
      · rcases TernaryValueConfinement.confinement_or_certificate hdomain.diameter Y N hY hn1 (by omega : 1 ≤ k) hbounds.1 with
          hconf | ⟨A, hA, _hsmallFactors, hlarge, hsmall⟩
        · rw [hlog] at hconf
          exact False.elim (not_le_of_gt hbadG hconf)
        · exact TernaryValueConfinement.certificate_mem X hdomain.diameter (fun i n hn ↦ (hdomain.values i n hn).2.2)
            base hdomain.box Y V hY.le hV A hA hlarge hsmall
      · rcases TernaryPrimeValueConfinement.confinement_or_certificate (U X) (H X) k Y N hY hn1 (by omega : 1 ≤ k) hbounds.2 with
          hconf | ⟨A, hA, _hsmallFactors, hlarge, hsmall⟩
        · rw [hlog] at hconf
          exact False.elim (not_le_of_gt hbadP hconf)
        · exact TernaryPrimeValueConfinement.certificate_mem X (fun i n hn ↦ (hdomain.values i n hn).2.2)
            base hdomain.box Y V hY.le hV A hA hlarge hsmall
    exact restrict_certificates base N D R Y V planes X hold (hplane X hxF)
  have hsecond : (second.card : ℝ) ≤ (N : ℝ) ^ (budgetExponent c + δ) := by
    have hcard : (second.card : ℝ) ≤ (PlaneSupportCover.certificates base N D R Y V planes).card := by
      exact_mod_cast card_le_card hcert
    have hcount := hcCount N (by omega) L R hband hR base planes hplanes
    have hfrac : 1 / c ≤ (1 + 1 / (k : ℝ)) / c := div_le_div_of_nonneg_right
      (le_add_of_nonneg_right (by positivity : 0 ≤ 1 / (k : ℝ))) hc.le
    have hid : (1 + 1 / (k : ℝ)) * (1 + (2 + ζ) / c) -
        (1 + 1 / (k : ℝ)) * (1 + (1 + ζ) / c) = (1 + 1 / (k : ℝ)) / c := by ring
    have hp1 : (1 + 1 / (k : ℝ)) * (1 + (1 + ζ) / c) < 1 + 1 / c + ε / 4 := by
      calc
        _ = (1 + 1 / (k : ℝ)) * (1 + (2 + ζ) / c) - (1 + 1 / (k : ℝ)) / c := by linarith only [hid]
        _ ≤ (1 + 1 / (k : ℝ)) * (1 + (2 + ζ) / c) - 1 / c := sub_le_sub_left hfrac _
        _ < (1 + 2 / c + ε / 2 / 2) - 1 / c := sub_lt_sub_right hp _
        _ = _ := by ring
    have hexp : (1 + 1 / (k : ℝ)) * (1 + (1 + ζ) / c) + ε / 4 ≤ budgetExponent c + δ := by
      have hmax := le_max_right (6 / 5 : ℝ) (1 + 1 / c)
      dsimp only [budgetExponent, δ] at *
      linarith
    exact hcard.trans (hcount.trans (Real.rpow_le_rpow_of_exponent_le hn1 hexp))
  have hcover : F ⊆ (firstG ∪ firstP) ∪ second := by
    intro X hX
    rcases lt_or_ge (N : ℝ) (TernaryTopProducts.topProduct (U X) (H X) k : ℝ) with hg | hg
    · exact mem_union.mpr (Or.inl (mem_union.mpr (Or.inl (mem_filter.mpr ⟨hX, hg⟩))))
    · rcases lt_or_ge (N : ℝ) (TernaryPrimeTopProducts.topProduct (U X) (H X) k : ℝ) with hp | hp
      · exact mem_union.mpr (Or.inl (mem_union.mpr (Or.inr (mem_filter.mpr ⟨hX, hp⟩))))
      · exact mem_union.mpr (Or.inr (mem_filter.mpr ⟨hX, hg, hp⟩))
  have hcard : (F.card : ℝ) ≤ firstG.card + firstP.card + second.card := by
    have h1 := card_le_card hcover
    have h2 := card_union_le (firstG ∪ firstP) second
    have h3 := card_union_le firstG firstP
    have hh : F.card ≤ firstG.card + firstP.card + second.card := by omega
    exact_mod_cast hh
  calc
    _ ≤ 5 * (N : ℝ) ^ (budgetExponent c + δ) := by linarith [hcard, hG', hP', hsecond]
    _ ≤ (N : ℝ) ^ ((budgetExponent c + δ) + δ) := hf N (by omega)
    _ = _ := by congr 1; dsimp [δ]; ring

end PaperP1.PlaneTernaryConfinement
