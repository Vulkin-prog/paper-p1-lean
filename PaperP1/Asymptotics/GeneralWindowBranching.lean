module

public import PaperP1.Asymptotics.BoundedObservationPool
public import PaperP1.Arithmetic.GeneralBranchingExceptions
public import PaperP1.Model.SelectedRelativeBits

/-! # Branching for arbitrary bounded observations, enlarged windows and injective selections -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GeneralWindowBranching

open Finset MeasureTheory ProbabilityTheory PaperP1.Arithmetic PaperP1.Model
  PaperP1.ConditionalWindowRank PaperP1.WindowPoolCount PaperP1.GeneralBranchingExceptions
  PaperP1.ConditionalRelativeBits PaperP1.RelativeSignIndependence PaperP1.SelectedRelativeBits
  PaperP1.Model.InfiniteRademacher PaperP1.BoundedObservationPool

local instance generalWindowMeasurableF2 : MeasurableSpace F₂ := ⊤

def Conclusion (G R : Finset ℕ) (L : ℕ) (E : Finset ℕ) : Prop :=
  ∀ x ∈ G, x ∉ E →
    (infiniteRademacherMeasure.map (infiniteStartBits x L) = Measure.pi (fun _ : Fin L ↦ coordinateMeasure)) ∧
    IndepFun (infiniteStartBits x L) (infiniteOldBits R) infiniteRademacherMeasure ∧
    ∀ (k : ℕ) (g : Fin (k + 1) → Fin (L + 1)), Function.Injective g →
      infiniteRademacherMeasure.map (selectedBits x L g) = Measure.pi (fun _ : Fin k ↦ coordinateMeasure) ∧
      IndepFun (selectedBits x L g) (infiniteOldBits R) infiniteRademacherMeasure

theorem finite_conclusion {G R : Finset ℕ} {L M : ℕ}
    (hlo : ∀ x ∈ G, 2 ≤ x) (hhi : ∀ x ∈ G, x + L ≤ M) (hR : ∀ n ∈ R, n ≤ M) :
    Conclusion G R L (exceptions G R L) := by
  intro x hx hnot
  have hxpos : 0 < x := (by norm_num : 0 < (2 : ℕ)).trans_le (hlo x hx)
  have hcard := retained_card_le_one hx hnot
  exact ⟨map_new_eq_fair hxpos (hhi x hx) hR hcard, independent_of_old hxpos (hhi x hx) hR hcard,
    fun k g hg ↦ ⟨map_selected_eq_fair hxpos (hhi x hx) hR hcard g hg,
      selected_independent_of_old hxpos (hhi x hx) hR hcard g⟩⟩

theorem logarithmic_windows (D : ℝ) (hD : 0 ≤ D) (j : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ, ((L + 1 : ℕ) : ℝ) ≤ D * Real.log N →
      ∀ G R : Finset ℕ, (∀ x ∈ G, 2 ≤ x) → (∀ x ∈ G, x + L ≤ 3 * N) →
        (∀ n ∈ R, 1 ≤ n ∧ n ≤ 3 * N) → R.card ≤ j * (L + 1) →
          ∃ E : Finset ℕ, E ⊆ G ∧ (E.card : ℝ) ≤ (N : ℝ) ^ (1 / 2 + ε) ∧ Conclusion G R L E := by
  obtain ⟨Npool, hNpool, hpool⟩ := pool_count_logarithmic D hD j (ε / 2) (by linarith)
  obtain ⟨NB, hB⟩ := LogarithmicWordPowers.polynomial_factor_le_rpow_eventually D hD 1 1 (ε / 2) (by linarith)
  refine ⟨max Npool NB, by omega, ?_⟩
  intro N hN L hwidth G R hlo hhi hR hcard
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hpoolN := hpool N (by omega) (L + 1) hwidth R hR hcard
  have hBN : ((L + 1 : ℕ) : ℝ) ≤ (N : ℝ) ^ (ε / 2) := by
    simpa only [Nat.cast_add, Nat.cast_one, one_mul, pow_one,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ L + 1)] using hB N (by omega) L hwidth
  have hhalf := card_le_half (R := R) hlo hhi
  have hcoarse : ((exceptions G R L).card : ℝ) ≤
      ((L + 1 : ℕ) : ℝ) * (poolValues R (L + 1) (3 * N)).card := by
    have hp : 0 ≤ ((L + 1 : ℕ) : ℝ) * (poolValues R (L + 1) (3 * N)).card := by positivity
    nlinarith
  refine ⟨exceptions G R L, exceptions_subset _ _ _, ?_, finite_conclusion hlo hhi (fun n hn ↦ (hR n hn).2)⟩
  calc
    _ ≤ ((L + 1 : ℕ) : ℝ) * (poolValues R (L + 1) (3 * N)).card := hcoarse
    _ ≤ (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (1 / 2 + ε / 2) :=
      mul_le_mul hBN hpoolN (Nat.cast_nonneg _) (Real.rpow_nonneg hNpos.le _)
    _ = _ := by rw [← Real.rpow_add hNpos]; congr 1; ring

/-- Any fixed positive height multiple is absorbed before the old choices are made. -/
theorem bounded_height_windows (K : ℕ) (hK : 1 ≤ K) (D : ℝ) (hD : 0 ≤ D) (j : ℕ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 3 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ L : ℕ, ((L + 1 : ℕ) : ℝ) ≤ D * Real.log N →
      ∀ G R : Finset ℕ, (∀ x ∈ G, 2 ≤ x) → (∀ x ∈ G, x + L ≤ K * N) →
        (∀ n ∈ R, 1 ≤ n ∧ n ≤ K * N) → R.card ≤ j * (L + 1) →
          ∃ E : Finset ℕ, E ⊆ G ∧ (E.card : ℝ) ≤ (N : ℝ) ^ (1 / 2 + ε) ∧ Conclusion G R L E := by
  obtain ⟨Nbase, hNbase, hbase⟩ := logarithmic_windows D hD j (ε / 2) (by linarith)
  obtain ⟨Nconst, hconst⟩ := LogarithmicWordPowers.polynomial_factor_le_rpow_eventually
    D hD ((K : ℝ) ^ (1 / 2 + ε / 2)) 0 (ε / 2) (by linarith)
  refine ⟨max Nbase Nconst, by omega, ?_⟩
  intro N hN L hwidth G R hlo hhi hR hcard
  have hNN : N ≤ K * N := by nlinarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hwidth' : ((L + 1 : ℕ) : ℝ) ≤ D * Real.log (K * N : ℕ) := hwidth.trans
    (mul_le_mul_of_nonneg_left (Real.log_le_log hNpos (by exact_mod_cast hNN)) hD)
  obtain ⟨E, hEG, hE, hind⟩ := hbase (K * N) (by omega) L hwidth' G R hlo
    (fun x hx ↦ (hhi x hx).trans (by omega))
    (fun n hn ↦ ⟨(hR n hn).1, (hR n hn).2.trans (by omega)⟩) hcard
  have hconstN : (K : ℝ) ^ (1 / 2 + ε / 2) ≤ (N : ℝ) ^ (ε / 2) := by
    simpa only [pow_zero, mul_one, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg K) _)] using
      hconst N (by omega) L hwidth
  refine ⟨E, hEG, hE.trans ?_, hind⟩
  rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg K) (Nat.cast_nonneg N)]
  calc
    _ ≤ (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (1 / 2 + ε / 2) :=
      mul_le_mul_of_nonneg_right hconstN (Real.rpow_nonneg hNpos.le _)
    _ = _ := by rw [← Real.rpow_add hNpos]; congr 1; ring

end PaperP1.GeneralWindowBranching
