module

public import PaperP1.Asymptotics.ColoredMassPropagation
public import PaperP1.Model.ReplicaPositiveSum
public import PaperP1.Combinatorics.ReplicaWeightedCover
public import PaperP1.Asymptotics.SplitQuadraticCongruenceCount

/-! # Actual positive replica moments are bounded by a subpower times their exact first moment -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ReplicaFiniteMoment

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.ColoredReplicaMass
  PaperP1.UniformFubini PaperP1.ReplicaTupleIndex PaperP1.ReplicaPositiveSum PaperP1.ReplicaWeightedCover

theorem bounded_weight_moment (r : ℕ) (hr : 0 < r) (q : ℕ) (C ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ (κ : Type*) [Fintype κ], ∀ M Y : ℕ, 2 * N + L ≤ M →
      ∀ color : Fin r → κ, ∀ c : ℕ → Fin L → F₂,
      ∀ A : Finset (Fin r → ℕ), (∀ x ∈ A, ∀ i, x i ∈ Ico N (2 * N)) →
      ∀ w : (Fin r → ℕ) → ℝ, (∀ x ∈ A, 0 ≤ w x) →
      ∀ W : ℝ, 0 ≤ W → (∀ x ∈ A, w x ≤ W) →
        average (fun σ : SampleSpace M ↦ (randomSum Y L color c A w σ) ^ (q + 1)) ≤
          W ^ q * (N : ℝ) ^ ε * average (randomSum Y L color c A w : SampleSpace M → ℝ) := by
  obtain ⟨N₀, hN₀⟩ := ColoredMassPropagation.weighted_subfamilies r hr (q * r) C ε hε
  refine ⟨N₀, ?_⟩
  intro N hN L hband κ _ M Y hM color c A hA w hw W hW hbound
  let χ := ReplicaWordColors.word r q hr color
  let a := seedWeight A w
  have ha : ∀ x, 0 ≤ a x := seedWeight_nonneg A w hw
  have hprop := hN₀ N hN L hband (Fin (q + 1) × κ) M Y hM χ (fun _ ↦ c) A hA a ha
    (family A q) (family_subset_more (Ico N (2 * N)) A hA q)
  have hseed : (∑ x ∈ A, a x * ColoredTupleMass.joint M Y L χ (fun _ ↦ c) x) =
      average (randomSum Y L color c A w : SampleSpace M → ℝ) := by
    rw [first_moment]
    apply sum_congr rfl
    intro x hx
    rw [show a x = w x from seedWeight_mem A w hx, ReplicaWordColors.seed_mass]
  rw [hseed] at hprop
  calc
    _ = ∑ t : Fin (q + 1) → A, (∏ j, w (t j).val) *
        ColoredTupleMass.joint M Y L χ (fun _ ↦ c) (flatten (fun j ↦ (t j).val)) :=
      flattened_moment M Y L q hr color c A w
    _ ≤ W ^ q * ∑ y ∈ family A q,
        a (TupleExtensions.initial (q * r) y) * ColoredTupleMass.joint M Y L χ (fun _ ↦ c) y :=
      weighted_cover A w W hw hbound (ColoredTupleMass.joint M Y L χ (fun _ ↦ c))
        (ColoredTupleMass.joint_nonneg M Y L χ (fun _ ↦ c))
    _ ≤ W ^ q * ((N : ℝ) ^ ε * average (randomSum Y L color c A w : SampleSpace M → ℝ)) :=
      mul_le_mul_of_nonneg_left hprop (pow_nonneg hW q)
    _ = _ := (mul_assoc _ _ _).symm

theorem logarithmic_weight_moment (r : ℕ) (hr : 0 < r) (q : ℕ) (C D A₀ ε : ℝ)
    (hD : 0 ≤ D) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ L : ℕ,
      |(L : ℝ) - Real.log N / Real.log 2| ≤ C →
      ∀ (κ : Type*) [Fintype κ], ∀ M Y : ℕ, 2 * N + L ≤ M →
      ∀ color : Fin r → κ, ∀ c : ℕ → Fin L → F₂,
      ∀ A : Finset (Fin r → ℕ), (∀ x ∈ A, ∀ i, x i ∈ Ico N (2 * N)) →
      ∀ w : (Fin r → ℕ) → ℝ, (∀ x ∈ A, 0 ≤ w x) →
      (∀ x ∈ A, w x ≤ D * (Real.log N) ^ A₀) →
        average (fun σ : SampleSpace M ↦ (randomSum Y L color c A w σ) ^ (q + 1)) ≤
          (N : ℝ) ^ ε * average (randomSum Y L color c A w : SampleSpace M → ℝ) := by
  obtain ⟨NS, hNS⟩ := bounded_weight_moment r hr q C (ε / 2) (by positivity)
  obtain ⟨NW, hNW⟩ := SplitQuadraticCongruenceCount.polylog_le_rpow (D ^ q) (A₀ * q) (ε / 2) (by positivity)
  refine ⟨max 2 (max NS NW), ?_⟩
  intro N hN L hband κ _ M Y hM color c A hA w hw hbound
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hNr : (0 : ℝ) < N := lt_of_lt_of_le zero_lt_one hN1
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN1
  have hW : 0 ≤ D * (Real.log N) ^ A₀ := mul_nonneg hD (Real.rpow_nonneg hlog _)
  have hpower : (D * (Real.log N) ^ A₀) ^ q ≤ (N : ℝ) ^ (ε / 2) := by
    have heq : ((Real.log N) ^ A₀) ^ q = (Real.log N) ^ (A₀ * (q : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hlog]
    rw [mul_pow, heq]
    exact hNW N (by omega)
  have hsum := first_moment_nonneg M Y L color c A w hw
  have hcoefficient : (D * (Real.log N) ^ A₀) ^ q * (N : ℝ) ^ (ε / 2) ≤ (N : ℝ) ^ ε := by
    calc
      _ ≤ (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / 2) :=
        mul_le_mul_of_nonneg_right hpower (Real.rpow_nonneg hNr.le _)
      _ = _ := by rw [← Real.rpow_add hNr]; congr 1; ring
  exact (hNS N (by omega) L hband κ M Y hM color c A hA w hw _ hW hbound).trans
    (mul_le_mul_of_nonneg_right hcoefficient hsum)

end PaperP1.ReplicaFiniteMoment
