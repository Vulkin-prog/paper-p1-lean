module

public import PaperP1.Asymptotics.SelectedQuadraticCells
public import PaperP1.Combinatorics.FiniteCoverCount
public import PaperP1.Asymptotics.SplitOffsetFixedKernelCount

/-! # The actual cumulative prescribed-kernel count for growing-degree split products -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PrescribedSplitProductCount

open Finset PaperP1.SplitOffsetProducts PaperP1.SelectedQuadraticCells
open PaperP1.SelectedQuadraticBudget PaperP1.SquarefreeOutsideDivisor

@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

def values (A : Finset ℤ) (N e : ℕ) (β : ℝ) : Finset ℕ :=
  (Icc N (2 * N)).filter fun n ↦ (N : ℝ) ^ β ≤ kernel A n ∧
    (kernel A n : ℝ) < 2 * (N : ℝ) ^ β ∧ e ∣ kernel A n

theorem mem_values (A : Finset ℤ) (N e n : ℕ) (β : ℝ) : n ∈ values A N e β ↔
    N ≤ n ∧ n ≤ 2 * N ∧ (N : ℝ) ^ β ≤ kernel A n ∧
      (kernel A n : ℝ) < 2 * (N : ℝ) ^ β ∧ e ∣ kernel A n := by
  simp only [values, mem_filter, mem_Icc, and_assoc]

theorem cumulative_count_core (c D A₀ ε : ℝ) (hc : 0 ≤ c) (hD : 1 ≤ D) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ W e : ℕ, ∀ A : Finset ℤ, ∀ β : ℝ,
      0 < W → Even A.card → 2 ≤ A.card → (W : ℝ) ≤ D * (Real.log N) ^ A₀ →
      (A.card : ℝ) ≤ c * Real.log (Real.log N) → (∀ a ∈ A, a.natAbs ≤ W) →
      ∀ S : Finset ℕ,
        (∀ n ∈ S, N ≤ n ∧ n ≤ 2 * N ∧ e ∣ kernel A n ∧ (kernel A n : ℝ) ≤ (N : ℝ) ^ β) →
        (S.card : ℝ) ≤ (N : ℝ) ^ (baseExponent A.card β (Real.log e / Real.log N) + c * Real.log 2 + ε) := by
  let η := ε / 8
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨Ns, hNs⟩ := PaperP1.SelectedQuadraticError.source_fixed_pair_selection c D A₀ η hc hD hη
  obtain ⟨Nc, hNc⟩ := uniform_cell_count D A₀ η hη
  obtain ⟨Nd, hNd⟩ := PaperP1.ActualPrescribedDivisorBudget.actual_outside_divisor_count c D A₀ η hc hη
  obtain ⟨Np, hNp⟩ := PaperP1.DyadicQuadraticBudgets.logarithmic_card_budget c η hc hη
  obtain ⟨Nj, hNj⟩ := PaperP1.DyadicQuadraticBudgets.indices_card_budget η hη
  obtain ⟨Nw, hNw⟩ := PaperP1.SplitQuadraticCongruenceCount.polylog_le_rpow (2 * D) A₀ 1 (by norm_num)
  refine ⟨max 3 (max Ns (max Nc (max Nd (max Np (max Nj Nw))))), ?_⟩
  intro N hN W e A β hW heven hcard hwidth hdegree hA S hS
  have hNtwo : 2 ≤ N := by omega
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hd : (0 : ℝ) < A.card := by exact_mod_cast (show 0 < A.card by omega)
  let d := A.card
  let δ := Real.log e / Real.log N
  let e' := outside e (resultant A)
  have he' : 0 < e' := outside_pos e (resultant A)
  have hWNr : (2 * W : ℝ) ≤ N := by
    have hw := hNw N (by omega)
    rw [Real.rpow_one] at hw
    nlinarith
  have hWN : 2 * W ≤ N := by exact_mod_cast hWNr
  by_cases hne : S.Nonempty
  · obtain ⟨P, hdis, hunion, hpairs⟩ := PaperP1.FinitePairPartition.exists_pair_partition A heven
    have hPcard := PaperP1.FinitePairPartition.partition_cardinality A P hdis hunion hpairs
    have hsub : ∀ B ∈ P, B ⊆ A := by
      intro B hB a ha
      rw [← hunion]
      exact mem_biUnion.mpr ⟨B, hB, ha⟩
    have hselected : ∀ n ∈ S, ∃ B ∈ P, weight e' n B / Real.log N ≤ threshold d β δ η := by
      intro n hnS
      obtain ⟨hnlo, _, hediv, hupper⟩ := hS n hnS
      obtain ⟨B, hB, hweight⟩ := hNs N (by omega) n W e A P hnlo hW hcard hwidth hdegree hA
        hediv hdis hunion hpairs
      have hnorm := normalized_kernel_le N (kernel A n) β hNtwo (kernel_pos A n) hupper
      have hT : (Real.log (kernel A n) / Real.log N - 2 * Real.log e / Real.log N) /
          ((A.card : ℝ) / 2) + η ≤ threshold d β δ η := by
        unfold threshold
        dsimp [d, δ]
        apply add_le_add _ le_rfl
        apply div_le_div_of_nonneg_right _ (by positivity)
        simp only [mul_div_assoc]
        exact sub_le_sub_right hnorm (2 * (Real.log e / Real.log N))
      exact ⟨B, hB, hweight.trans hT⟩
    have hheight : ∀ n ∈ S, ∀ B ∈ P, kernel B n ≤ N ^ 6 := by
      intro n hnS B hB
      exact PaperP1.DyadicQuadraticBudgets.block_kernel_height N n W B hNtwo hWN
        (hS n hnS).1 (hS n hnS).2.1 (hpairs B hB) (fun a ha ↦ hA a (hsub B hB ha))
    have hcover := PaperP1.SelectedQuadraticCells.cover S P e' N d β δ η he'
      (by omega : 0 < N) hselected hheight
    obtain ⟨n₀, hn₀⟩ := hne
    have hdiv := hNd N (by omega) n₀ W e A (hS n₀ hn₀).1 (hS n₀ hn₀).2.1
      hwidth hdegree hA (hS n₀ hn₀).2.2.1
    have hpNat : P.card ≤ A.card := by omega
    have hpReal : (P.card : ℝ) ≤ c * Real.log (Real.log N) :=
      (by exact_mod_cast hpNat : (P.card : ℝ) ≤ A.card).trans hdegree
    have hp := hNp N (by omega) P.card hpReal
    have hj := hNj N (by omega)
    have hcodes : ((codes P e' N).card : ℝ) ≤ (N : ℝ) ^ (c * Real.log 2 + 3 * η) := by
      calc
        _ = (P.card : ℝ) * ((e'.divisors.card : ℝ) *
            ((PaperP1.DyadicQuadraticBudgets.indices N).card : ℝ)) := by
          simp only [codes, card_product, Nat.cast_mul]
        _ ≤ (N : ℝ) ^ η * ((N : ℝ) ^ (c * Real.log 2 + η) * (N : ℝ) ^ η) :=
          mul_le_mul hp (mul_le_mul hdiv hj (Nat.cast_nonneg _) (Real.rpow_nonneg hn.le _))
            (by positivity) (Real.rpow_nonneg hn.le _)
        _ = _ := by
          rw [← Real.rpow_add hn, ← Real.rpow_add hn]
          congr 1
          ring
    have hcells : ∀ i ∈ codes P e' N,
        ((cell S e' N d β δ η i).card : ℝ) ≤ (N : ℝ) ^ (baseExponent d β δ + η / 4 + η) := by
      intro i hi
      obtain ⟨hBi, hrest⟩ := mem_product.mp hi
      obtain ⟨hdi, _⟩ := mem_product.mp hrest
      exact hNc N (by omega) W e' d β δ η S i hwidth he' (Nat.mem_divisors.mp hdi).1
        (hpairs i.1 hBi) (fun a ha ↦ hA a (hsub i.1 hBi ha))
        (fun n hnS ↦ ⟨(hS n hnS).1, (hS n hnS).2.1⟩)
    have hcount := PaperP1.FiniteCoverCount.cardinal_le S (codes P e' N)
      (cell S e' N d β δ η) ((N : ℝ) ^ (baseExponent d β δ + η / 4 + η)) hcover hcells
    calc
      (S.card : ℝ) ≤ ((codes P e' N).card : ℝ) * (N : ℝ) ^ (baseExponent d β δ + η / 4 + η) := hcount
      _ ≤ (N : ℝ) ^ (c * Real.log 2 + 3 * η) * (N : ℝ) ^ (baseExponent d β δ + η / 4 + η) :=
        mul_le_mul_of_nonneg_right hcodes (Real.rpow_nonneg hn.le _)
      _ ≤ (N : ℝ) ^ (baseExponent A.card β (Real.log e / Real.log N) + c * Real.log 2 + ε) := by
        rw [← Real.rpow_add hn]
        apply Real.rpow_le_rpow_of_exponent_le hn1
        dsimp [d, δ, η]
        linarith
  · rw [not_nonempty_iff_eq_empty.mp hne, card_empty, Nat.cast_zero]
    exact Real.rpow_nonneg hn.le _

theorem cumulative_count (c D A₀ ε : ℝ) (hc : 0 ≤ c) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ W e : ℕ, ∀ A : Finset ℤ, ∀ β : ℝ,
      0 < W → Even A.card → 2 ≤ A.card → (W : ℝ) ≤ D * (Real.log N) ^ A₀ →
      (A.card : ℝ) ≤ c * Real.log (Real.log N) → (∀ a ∈ A, a.natAbs ≤ W) →
      ∀ S : Finset ℕ,
        (∀ n ∈ S, N ≤ n ∧ n ≤ 2 * N ∧ e ∣ kernel A n ∧ (kernel A n : ℝ) ≤ (N : ℝ) ^ β) →
        (S.card : ℝ) ≤ (N : ℝ) ^ (baseExponent A.card β (Real.log e / Real.log N) + c * Real.log 2 + ε) := by
  obtain ⟨N₀, hN₀⟩ := cumulative_count_core c (max 1 D) A₀ ε hc (le_max_left _ _) hε
  refine ⟨max 2 N₀, ?_⟩
  intro N hN W e A β hW heven hcard hwidth hdegree hA S hS
  have hl : 0 ≤ Real.log N := (Real.log_pos (by exact_mod_cast (show 1 < N by omega))).le
  have hwidth' : (W : ℝ) ≤ max 1 D * (Real.log N) ^ A₀ :=
    hwidth.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hl _))
  exact hN₀ N (by omega) W e A β hW heven hcard hwidth' hdegree hA S hS

theorem base_shift_le (d : ℕ) (hd : 1 ≤ d) (β δ t : ℝ) (ht : 0 ≤ t) :
    baseExponent d (β + t) δ ≤ baseExponent d β δ + t := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hden : (0 : ℝ) < 2 * d := by positivity
  have hprod : t ≤ t * (2 * (d : ℝ)) := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (by linarith : (1 : ℝ) ≤ 2 * d) ht
  have hdiv : t / (2 * (d : ℝ)) ≤ t := (div_le_iff₀ hden).mpr hprod
  unfold baseExponent
  rw [add_div]
  linarith

theorem constant_upper_count (c D A₀ F ε : ℝ) (hc : 0 ≤ c) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ W e : ℕ, ∀ A : Finset ℤ, ∀ β : ℝ,
      0 < W → Even A.card → 2 ≤ A.card → (W : ℝ) ≤ D * (Real.log N) ^ A₀ →
      (A.card : ℝ) ≤ c * Real.log (Real.log N) → (∀ a ∈ A, a.natAbs ≤ W) → ∀ S : Finset ℕ,
        (∀ n ∈ S, N ≤ n ∧ n ≤ 2 * N ∧ e ∣ kernel A n ∧
          (kernel A n : ℝ) ≤ F * (N : ℝ) ^ β) →
        (S.card : ℝ) ≤ (N : ℝ) ^ (baseExponent A.card β (Real.log e / Real.log N) + c * Real.log 2 + ε) := by
  obtain ⟨Nf, hNf⟩ := cumulative_count c D A₀ (ε / 2) hc (by positivity)
  obtain ⟨Nc, hNc⟩ := PaperP1.UniformReal.uniformSubpolynomialOn_le_rpow
    (PaperP1.ExpSqrtLog.uniformSubpolynomialOn_const (fun _ _ : ℕ ↦ True) F) (ε / 2) (by positivity)
  refine ⟨max 2 (max Nf Nc), ?_⟩
  intro N hN W e A β hW heven hcard hwidth hdegree hA S hS
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hcN : F ≤ (N : ℝ) ^ (ε / 2) := (le_abs_self _).trans (hNc N (by omega) 0 trivial)
  have hcount := hNf N (by omega) W e A (β + ε / 2) hW heven hcard hwidth hdegree hA S (by
    intro n hnS
    obtain ⟨hnlo, hnhi, hediv, hupper⟩ := hS n hnS
    refine ⟨hnlo, hnhi, hediv, ?_⟩
    calc
      _ ≤ F * (N : ℝ) ^ β := hupper
      _ ≤ (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ β :=
        mul_le_mul_of_nonneg_right hcN (Real.rpow_nonneg hn.le _)
      _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring)
  apply hcount.trans
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ N by omega))
  have hs := base_shift_le A.card (by omega) β (Real.log e / Real.log N) (ε / 2) (by positivity)
  linarith

theorem dyadic_count (c D A₀ ε : ℝ) (hc : 0 ≤ c) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ W e : ℕ, ∀ A : Finset ℤ, ∀ β : ℝ,
      0 < W → Even A.card → 2 ≤ A.card → (W : ℝ) ≤ D * (Real.log N) ^ A₀ →
      (A.card : ℝ) ≤ c * Real.log (Real.log N) → (∀ a ∈ A, a.natAbs ≤ W) → ∀ S : Finset ℕ,
        (∀ n ∈ S, N ≤ n ∧ n ≤ 2 * N ∧ (N : ℝ) ^ β ≤ kernel A n ∧
          (kernel A n : ℝ) < 2 * (N : ℝ) ^ β ∧ e ∣ kernel A n) →
        (S.card : ℝ) ≤ (N : ℝ) ^ (baseExponent A.card β (Real.log e / Real.log N) + c * Real.log 2 + ε) := by
  obtain ⟨N₀, hN₀⟩ := constant_upper_count c D A₀ 2 ε hc hε
  refine ⟨N₀, ?_⟩
  intro N hN W e A β hW heven hcard hwidth hdegree hA S hS
  apply hN₀ N hN W e A β hW heven hcard hwidth hdegree hA S
  intro n hn
  obtain ⟨hnlo, hnhi, _, hqhi, hediv⟩ := hS n hn
  exact ⟨hnlo, hnhi, hediv, hqhi.le⟩

theorem actual_values_count (c D A₀ ε : ℝ) (hc : 0 ≤ c) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ W e : ℕ, ∀ A : Finset ℤ, ∀ β : ℝ,
      0 < W → Even A.card → 2 ≤ A.card → (W : ℝ) ≤ D * (Real.log N) ^ A₀ →
      (A.card : ℝ) ≤ c * Real.log (Real.log N) → (∀ a ∈ A, a.natAbs ≤ W) →
      ((values A N e β).card : ℝ) ≤
        (N : ℝ) ^ (baseExponent A.card β (Real.log e / Real.log N) + c * Real.log 2 + ε) := by
  obtain ⟨N₀, hN₀⟩ := dyadic_count c D A₀ ε hc hε
  refine ⟨N₀, ?_⟩
  intro N hN W e A β hW heven hcard hwidth hdegree hA
  exact hN₀ N hN W e A β hW heven hcard hwidth hdegree hA (values A N e β)
    (by intro n hn; exact (mem_values A N e n β).mp hn)

theorem companion_T5_2 (c D A₀ ε : ℝ) (hc : 0 ≤ c) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ W e : ℕ, ∀ A : Finset ℤ, ∀ β : ℝ,
      0 < W → Even A.card → 2 ≤ A.card → (W : ℝ) ≤ D * (Real.log N) ^ A₀ →
      (A.card : ℝ) ≤ c * Real.log (Real.log N) → (∀ a ∈ A, a.natAbs ≤ W) →
      ((values A N e β).card : ℝ) ≤
        (N : ℝ) ^ (baseExponent A.card β (Real.log e / Real.log N) + c * Real.log 2 + ε) ∧
      ∀ q : ℕ, ((PaperP1.SplitOffsetFixedKernelCount.values A N q).card : ℝ) ≤
        (N : ℝ) ^ (2 * c * Real.log 2 + ε) := by
  obtain ⟨Np, hNp⟩ := actual_values_count c D A₀ ε hc hε
  obtain ⟨Nf, hNf⟩ := PaperP1.SplitOffsetFixedKernelCount.actual_values_fixed_kernel_count
    c (max 1 D) A₀ ε hc (le_max_left _ _) hε
  refine ⟨max 2 (max Np Nf), ?_⟩
  intro N hN W e A β hW heven hcard hwidth hdegree hA
  have hl : 0 ≤ Real.log N := (Real.log_pos (by exact_mod_cast (show 1 < N by omega))).le
  have hwidth' : (W : ℝ) ≤ max 1 D * (Real.log N) ^ A₀ :=
    hwidth.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hl _))
  exact ⟨hNp N (by omega) W e A β hW heven hcard hwidth hdegree hA,
    fun q ↦ hNf N (by omega) W q A hW hcard hwidth' hdegree hA⟩

end PaperP1.PrescribedSplitProductCount
