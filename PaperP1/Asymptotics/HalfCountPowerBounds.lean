module

public import PaperP1.Asymptotics.HalfCountStageBounds
public import PaperP1.Asymptotics.HalfCountSchedule

/-! # Exact exponent costs of the actual conditional half-count classes

The explicit fewer-target bounds below are finite induction interfaces.
They do not assert or assume the full target-count conclusion.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HalfCountPowerBounds

open Finset PaperP1.ProjectedWindowLists PaperP1.ChosenWindowWitness
  PaperP1.HalfCountStages PaperP1.AnchorCertificateGraph PaperP1.HalfCountSchedule

theorem rare_coordinate_bound {r s : ℕ} (G P : Finset ℕ) (N W : ℕ)
    (old : Fin s → ℕ) (η : ℝ) (hN : 2 ≤ N)
    (hP : (P.card : ℝ) ≤ (N : ℝ) ^ (1 / 2 + η))
    (hB : ∀ x ∈ P, ((lists (r := r) G W (Fin.cons x old)).card : ℝ) ≤
      (N : ℝ) ^ ((r : ℝ) / 2 + η)) :
    (((lists (r := r + 1) G W old).filter fun n ↦ ∃ i, n i ∈ P).card : ℝ) ≤
      (r + 1 : ℝ) * (N : ℝ) ^ (((r + 1 : ℕ) : ℝ) / 2 + 2 * η) := by
  classical
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hprod : (P.card : ℝ) * (N : ℝ) ^ ((r : ℝ) / 2 + η) ≤
      (N : ℝ) ^ (((r + 1 : ℕ) : ℝ) / 2 + 2 * η) := by
    calc
      _ ≤ (N : ℝ) ^ (1 / 2 + η) * (N : ℝ) ^ ((r : ℝ) / 2 + η) :=
        mul_le_mul_of_nonneg_right hP (Real.rpow_nonneg hn.le _)
      _ = _ := by rw [← Real.rpow_add hn]; congr 1; push_cast; ring
  exact (PaperP1.ProjectedWindowCounts.any_coordinate_bound G W old P _ hB).trans
    (mul_le_mul_of_nonneg_left hprod (by positivity))

theorem removed_power_bound {r s : ℕ} (G P : Finset ℕ) (N X W : ℕ) (old : Fin s → ℕ)
    (hold : ∀ k, old k ∈ G) (m t j J : ℕ) (Y : ℕ → ℝ) (η : ℝ)
    (hN : 2 ≤ N) (hJ : 0 < J) (hj : j < J) (hPsub : P ⊆ G)
    (hP : ∀ n ∈ survivors (r := r + 1) G N W old m t Y j, ∀ i,
      m < (chosen W old n i).card → n i ∈ P)
    (hPcard : (P.card : ℝ) ≤ (N : ℝ) ^ (1 - x J j + η))
    (hdegree : ∀ z ∈ G,
      ((outgoing G X W t (Y j) z).card : ℝ) ≤ (N : ℝ) ^ (x J (j + 1) + η) ∧
      ((incoming G X W t (Y j) z).card : ℝ) ≤ (N : ℝ) ^ (x J (j + 1) + η))
    (hcontrol : PaperP1.AnchorRelationCertificates.ProjectedControl
      (ν := Fin r) (κ := Fin s) G X W t (Y j) N)
    (hB₁ : ∀ z ∈ G, ((lists (r := r) G W (Fin.cons z old)).card : ℝ) ≤
      (N : ℝ) ^ ((r : ℝ) / 2 + η))
    (hB₂ : ∀ k : ℕ, r = k + 1 → ∀ z ∈ G, ∀ w ∈ G,
      ((lists (r := k) G W (Fin.cons w (Fin.cons z old))).card : ℝ) ≤
        (N : ℝ) ^ ((k : ℝ) / 2 + η)) :
    ((survivors (r := r + 1) G N W old m t Y j \ survivors G N W old m t Y (j + 1)).card : ℝ) ≤
      (((r + 1) * r : ℕ) : ℝ) * (N : ℝ) ^ (((r + 1 : ℕ) : ℝ) / 2 + step J + 3 * η) +
        (((r + 1) * s : ℕ) : ℝ) * (N : ℝ) ^ (((r + 1 : ℕ) : ℝ) / 2 + 2 * η) := by
  classical
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  cases r with
  | zero =>
    have hc := PaperP1.HalfCountStageBounds.removed_single_bound G N X W old hold m t j Y
      ((N : ℝ) ^ (x J (j + 1) + η)) ((N : ℝ) ^ ((0 : ℝ) / 2 + η))
      (fun z hz ↦ (hdegree z hz).2) hcontrol (by simpa only [Nat.cast_zero] using hB₁) (Real.rpow_nonneg hn.le _)
    have hprod : (N : ℝ) ^ (x J (j + 1) + η) * (N : ℝ) ^ ((0 : ℝ) / 2 + η) ≤
        (N : ℝ) ^ (1 / 2 + 2 * η) := by
      rw [← Real.rpow_add hn]
      exact Real.rpow_le_rpow_of_exponent_le hn1 (by have := x_le_half J (j + 1) hJ (by omega); linarith)
    have hbound := hc.trans (mul_le_mul_of_nonneg_left hprod (Nat.cast_nonneg s))
    simpa only [Nat.zero_add, Nat.mul_zero, Nat.one_mul, Nat.cast_zero, Nat.cast_one, zero_mul, zero_add] using hbound
  | succ r =>
    have hc := PaperP1.HalfCountStageBounds.removed_bound G P N X W old hold m t j Y
      ((N : ℝ) ^ (x J (j + 1) + η)) ((N : ℝ) ^ (((r + 1 : ℕ) : ℝ) / 2 + η))
      ((N : ℝ) ^ ((r : ℝ) / 2 + η)) hPsub hP hdegree hcontrol hB₁ (hB₂ r rfl)
      (Real.rpow_nonneg hn.le _) (Real.rpow_nonneg hn.le _)
    have hnew : (P.card : ℝ) * (N : ℝ) ^ (x J (j + 1) + η) * (N : ℝ) ^ ((r : ℝ) / 2 + η) ≤
        (N : ℝ) ^ (((r + 2 : ℕ) : ℝ) / 2 + step J + 3 * η) := by
      calc
        _ ≤ (N : ℝ) ^ (1 - x J j + η) * (N : ℝ) ^ (x J (j + 1) + η) * (N : ℝ) ^ ((r : ℝ) / 2 + η) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hPcard (Real.rpow_nonneg hn.le _)) (Real.rpow_nonneg hn.le _)
        _ = _ := by rw [← Real.rpow_add hn, ← Real.rpow_add hn, pair_cost]
    have holdpow : (N : ℝ) ^ (x J (j + 1) + η) * (N : ℝ) ^ (((r + 1 : ℕ) : ℝ) / 2 + η) ≤
        (N : ℝ) ^ (((r + 2 : ℕ) : ℝ) / 2 + 2 * η) := by
      rw [← Real.rpow_add hn]
      exact Real.rpow_le_rpow_of_exponent_le hn1 (old_cost J j r η hJ hj)
    exact hc.trans (add_le_add
      (mul_le_mul_of_nonneg_left hnew (Nat.cast_nonneg _))
      (mul_le_mul_of_nonneg_left holdpow (Nat.cast_nonneg _)))

theorem finite_assembly {r s : ℕ} (G : Finset ℕ) (N W : ℕ) (old : Fin s → ℕ)
    (m t J : ℕ) (Y : ℕ → ℝ) (T : ℝ)
    (hshort : ((shortLists (r := r + 1) G W old m).card : ℝ) ≤ T)
    (hexception : ((exceptionalLists (r := r + 1) G N W old).card : ℝ) ≤ (r + 1 : ℝ) * T)
    (hlast : ((survivors (r := r + 1) G N W old m t Y J).card : ℝ) ≤ (r + 1 : ℝ) * T)
    (hremoved : ∀ j < J,
      ((survivors (r := r + 1) G N W old m t Y j \ survivors G N W old m t Y (j + 1)).card : ℝ) ≤
        (((r + 1) * r + (r + 1) * s : ℕ) : ℝ) * T) :
    ((lists (r := r + 1) G W old).card : ℝ) ≤
      ((1 + 2 * (r + 1) + J * ((r + 1) * r + (r + 1) * s) : ℕ) : ℝ) * T := by
  classical
  have hinit : ((lists (r := r + 1) G W old).card : ℝ) ≤
      ((shortLists (r := r + 1) G W old m).card : ℝ) +
        ((exceptionalLists (r := r + 1) G N W old).card : ℝ) +
          ((survivors (r := r + 1) G N W old m t Y 0).card : ℝ) := by
    exact_mod_cast PaperP1.FiniteStageCounts.initial_cover
      (lists (r := r + 1) G W old) (shortLists G W old m) (exceptionalLists G N W old)
  have hstage := PaperP1.FiniteStageCounts.decreasing_bound
    (survivors (r := r + 1) G N W old m t Y) J ((r + 1 : ℝ) * T)
    ((((r + 1) * r + (r + 1) * s : ℕ) : ℝ) * T)
    (fun j _ ↦ survivors_succ_subset G N W old m t j Y) hlast hremoved
  calc
    _ ≤ T + (r + 1 : ℝ) * T + ((r + 1 : ℝ) * T + (J : ℝ) *
        ((((r + 1) * r + (r + 1) * s : ℕ) : ℝ) * T)) := by linarith only [hinit, hstage, hshort, hexception]
    _ = _ := by push_cast; ring

end PaperP1.HalfCountPowerBounds
