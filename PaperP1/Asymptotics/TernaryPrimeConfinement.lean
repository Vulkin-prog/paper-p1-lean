module

public import PaperP1.Asymptotics.PolylogConfinementScales
public import PaperP1.Asymptotics.TernaryUnboundedCutoff
public import PaperP1.Arithmetic.TernaryPrimeValueConfinement
public import PaperP1.Asymptotics.TernaryPrimeTheorem
public import PaperP1.Asymptotics.TernaryGroupConfinement

/-! # The full three-dimensional confinement count for actual individual primes -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.TernaryPrimeConfinement

open Finset PaperP1.TernaryPrimeTopProducts PaperP1.TernaryPrimeValueConfinement
  PaperP1.TernaryUnboundedCutoff PaperP1.PolylogConfinementScales PaperP1.TernaryGroupConfinement

theorem uniform_prime_count (c ε : ℝ) (hc : 0 < c) (hε : 0 < ε) :
    ∃ k : ℕ, 3 ≤ k ∧ ∀ C : ℝ, ∀ D : ℕ,
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L R : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C → R ≤ D * (L + 1) →
      ∀ (F : Finset (Fin 3 → ℕ)) (U : (Fin 3 → ℕ) → Fin 3 → Finset ℕ)
        (H : (Fin 3 → ℕ) → ℕ) (base : Fin 3 → ℕ),
      (∀ X ∈ F, SourceConditions N R D base U H X) →
      (∀ X ∈ F, threshold k N L c < (largePrimes (U X) (H X) (((L + 1 : ℕ) : ℝ) ^ c)).card) →
      (F.card : ℝ) ≤ (N : ℝ) ^ (budgetExponent c + ε) := by
  obtain ⟨k, hk, ζ, hζ, hζ1, hp⟩ := choose_parameters c (ε / 2) hc (by positivity)
  refine ⟨k, hk, ?_⟩
  intro C D
  let δ := ε / 2
  obtain ⟨NT, _hNT, ht⟩ := TernaryPrimeTheorem.population_bound C D k hk δ (by dsimp [δ]; positivity)
  obtain ⟨NC, _hNC, hcCount⟩ := RankinCertificateCritical.uniform_bound C c hc D k (by omega)
    ζ (ε / 4) hζ hζ1 (by positivity)
  obtain ⟨NG, hg⟩ := CriticalWindowGeometry.uniform_geometry C 2
  obtain ⟨NF, hf⟩ := HalfCountSchedule.factor_absorption 3 (budgetExponent c + δ) δ (by dsimp [δ]; positivity)
  refine ⟨max 2 (max NT (max NC (max NG NF))), by omega, ?_⟩
  intro N hN L R hband hR F U H base hadm hbad
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hgeom := hg N (by omega) L hband
  have hB : (1 : ℝ) < ((L + 1 : ℕ) : ℝ) := by exact_mod_cast (by have := hgeom.2.2.1; omega : 1 < L + 1)
  let Y := ((L + 1 : ℕ) : ℝ) ^ c
  let V := (N : ℝ) ^ (1 + 1 / (k : ℝ))
  have hY : 1 < Y := Real.one_lt_rpow hB hc
  have hV : 0 ≤ V := by dsimp [V]; positivity
  let first := F.filter fun X ↦ (N : ℝ) < (topProduct (U X) (H X) k : ℝ)
  let second := F.filter fun X ↦ (topProduct (U X) (H X) k : ℝ) ≤ N
  have hfirstF : first ⊆ F := filter_subset _ _
  have hsecondF : second ⊆ F := filter_subset _ _
  have hfirst := ht N (by omega) L R hband hR first U H base N hn1
    (fun X hX ↦ hadm X (hfirstF hX)) (fun _ hX ↦ (mem_filter.mp hX).2)
  have hpow : (N : ℝ) ^ 3 * (N : ℝ) ^ (-2 : ℝ) = (N : ℝ) := by
    rw [← Real.rpow_natCast (N : ℝ) 3, ← Real.rpow_add hn]
    norm_num
  rw [hpow] at hfirst
  have hfirst' : (first.card : ℝ) ≤ 2 * (N : ℝ) ^ (budgetExponent c + δ) := by
    have hNsmall : (N : ℝ) ≤ (N : ℝ) ^ (6 / 5 : ℝ) := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num : (1 : ℝ) ≤ 6 / 5)
    have hpowbig : (N : ℝ) ^ (6 / 5 + δ) ≤ (N : ℝ) ^ (budgetExponent c + δ) :=
      Real.rpow_le_rpow_of_exponent_le hn1 (add_le_add (show (6 / 5 : ℝ) ≤ budgetExponent c from le_max_left _ _) le_rfl)
    have heq : (N : ℝ) ^ δ * (N : ℝ) ^ (6 / 5 : ℝ) = (N : ℝ) ^ (6 / 5 + δ) := by
      rw [← Real.rpow_add hn]
      congr 1
      ring
    nlinarith [mul_le_mul_of_nonneg_left hNsmall (by positivity : 0 ≤ (N : ℝ) ^ δ)]
  have hcert : second ⊆ CRTSupportCover.certificates base N D R Y V := by
    intro X hX
    have hxF := hsecondF hX
    have hdomain := hadm X hxF
    have hcases := confinement_or_certificate (U X) (H X) k Y N hY hn1 (by omega : 1 ≤ k) (mem_filter.mp hX).2
    rcases hcases with hconf | ⟨A, hA, _hsmallFactors, hlarge, hsmall⟩
    · have hlog : Real.log Y = c * Real.log ((L + 1 : ℕ) : ℝ) := Real.log_rpow (by linarith : 0 < ((L + 1 : ℕ) : ℝ)) c
      rw [hlog] at hconf
      exact False.elim (not_le_of_gt (hbad X hxF) hconf)
    · exact certificate_mem X (fun i n hn ↦ (hdomain.values i n hn).2.2)
        base hdomain.box Y V hY.le hV A hA hlarge hsmall
  have hsecond : (second.card : ℝ) ≤ (N : ℝ) ^ (budgetExponent c + δ) := by
    have hcard : (second.card : ℝ) ≤ (CRTSupportCover.certificates base N D R Y V).card := by
      exact_mod_cast card_le_card hcert
    have hcount := hcCount N (by omega) L R hband hR base
    have hexp : (1 + 1 / (k : ℝ)) * (1 + (2 + ζ) / c) + ε / 4 ≤ budgetExponent c + δ := by
      have hmax := le_max_right (6 / 5 : ℝ) (1 + 2 / c)
      dsimp only [budgetExponent, δ] at *
      linarith
    exact hcard.trans (hcount.trans (Real.rpow_le_rpow_of_exponent_le hn1 hexp))
  have hcover : F ⊆ first ∪ second := by
    intro X hX
    rcases lt_or_ge (N : ℝ) (topProduct (U X) (H X) k : ℝ) with hf | hs
    · exact mem_union.mpr (Or.inl (mem_filter.mpr ⟨hX, hf⟩))
    · exact mem_union.mpr (Or.inr (mem_filter.mpr ⟨hX, hs⟩))
  have hcard : (F.card : ℝ) ≤ first.card + second.card := by
    exact_mod_cast (card_le_card hcover).trans (card_union_le first second)
  calc
    _ ≤ 3 * (N : ℝ) ^ (budgetExponent c + δ) := by linarith [hcard, hfirst', hsecond]
    _ ≤ (N : ℝ) ^ ((budgetExponent c + δ) + δ) := hf N (by omega)
    _ = _ := by congr 1; dsimp [δ]; ring

end PaperP1.TernaryPrimeConfinement
