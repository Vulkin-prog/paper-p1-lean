module

public import PaperP1.Asymptotics.SplitProductPowerForm
public import PaperP1.Asymptotics.ComparableLogBounds
public import PaperP1.Asymptotics.ComparableCoverPower

/-! # Actual split-product counts on arbitrary fixed comparable positive intervals -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ComparableSplitProductCount

open Finset PaperP1.SplitOffsetProducts PaperP1.SplitProductPowerForm
open PaperP1.ComparableDyadicCover PaperP1.ComparableLogBounds

def slack (ε : ℝ) : ℝ := ε / (16 * (Real.log 2 + 1))

theorem slack_pos (ε : ℝ) (hε : 0 < ε) : 0 < slack ε := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  unfold slack
  positivity

theorem slack_log_bound (ε : ℝ) (hε : 0 < ε) : slack ε * Real.log 2 ≤ ε / 16 := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hden : 0 < 16 * (Real.log 2 + 1) := by positivity
  have heq : slack ε * (16 * (Real.log 2 + 1)) = ε := by
    unfold slack
    exact div_mul_cancel₀ _ hden.ne'
  nlinarith only [heq, (slack_pos ε hε).le]

theorem prefactor_budget (K T : ℕ) (α ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, (K : ℝ) * (T : ℝ) ^ α ≤ (N : ℝ) ^ ε := by
  obtain ⟨N₀, hN₀⟩ := PaperP1.UniformReal.uniformSubpolynomialOn_le_rpow
    (PaperP1.ExpSqrtLog.uniformSubpolynomialOn_const (fun _ _ : ℕ ↦ True) ((K : ℝ) * (T : ℝ) ^ α)) ε hε
  exact ⟨N₀, fun N hN ↦ (le_abs_self _).trans (hN₀ N hN 0 trivial)⟩

theorem width_lt_centre (C : ℕ) (D A₀ : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ n W : ℕ, N ≤ C * n →
      (W : ℝ) ≤ D * (Real.log N) ^ A₀ → W < n := by
  obtain ⟨Nw, hNw⟩ := PaperP1.SplitQuadraticCongruenceCount.polylog_le_rpow
    (2 * C * D) A₀ 1 (by norm_num)
  refine ⟨max 2 Nw, ?_⟩
  intro N hN n W hlo hwidth
  have hWNr : (2 * C * W : ℝ) ≤ N := by
    have hw := hNw N (by omega)
    rw [Real.rpow_one] at hw
    have hm := mul_le_mul_of_nonneg_left hwidth (by positivity : (0 : ℝ) ≤ 2 * C)
    nlinarith only [hm, hw]
  have hWN : 2 * C * W ≤ N := by exact_mod_cast hWNr
  by_contra hnot
  have hle : n ≤ W := by omega
  have hm := Nat.mul_le_mul_left C hle
  have hNp : 0 < N := by omega
  nlinarith only [hWN, hlo, hm, hNp]

theorem source_product_values (C : ℕ) (D A₀ : ℝ) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ n W : ℕ, ∀ A : Finset ℤ,
      N ≤ C * n → (W : ℝ) ≤ D * (Real.log N) ^ A₀ → (∀ a ∈ A, a.natAbs ≤ W) →
      0 < product A n ∧ (product A n : ℤ) = ∏ a ∈ A, ((n : ℤ) + a) ∧
        0 < ∏ a ∈ A, ((n : ℤ) + a) := by
  obtain ⟨N₀, hN₀⟩ := width_lt_centre C D A₀
  refine ⟨N₀, ?_⟩
  intro N hN n W A hlo hwidth hA
  have hWn := hN₀ N hN n W hlo hwidth
  have hp := product_pos A n W hWn hA
  have hcast := product_cast A n W hWn hA
  refine ⟨hp, hcast, ?_⟩
  rw [← hcast]
  exact_mod_cast hp

theorem prescribed_power_count (C : ℕ) (hC : 1 ≤ C) (c D A₀ ε : ℝ) (hc : 0 ≤ c) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ W e : ℕ, ∀ A : Finset ℤ, ∀ Q : ℝ,
      0 < W → Even A.card → 2 ≤ A.card → (W : ℝ) ≤ D * (Real.log N) ^ A₀ →
      (A.card : ℝ) ≤ c * Real.log (Real.log N) → (∀ a ∈ A, a.natAbs ≤ W) → 0 < e → 0 < Q →
      ∀ S : Finset ℕ,
        (∀ n ∈ S, N ≤ C * n ∧ n ≤ C * N ∧ e ∣ kernel A n ∧ (kernel A n : ℝ) ≤ Q) →
        (S.card : ℝ) ≤ (N : ℝ) ^ (1 / 2 + c * Real.log 2 + ε) * profile A.card Q e := by
  let η := slack ε
  let ξ := ε / 8
  let c' := c + η
  let D' := widthConstant D A₀
  let T := distortion C
  let α := 1 / 2 + c' * Real.log 2 + ξ
  have hη : 0 < η := slack_pos ε hε
  have hξ : 0 < ξ := by dsimp [ξ]; positivity
  have hc' : 0 ≤ c' := by dsimp [c']; positivity
  have hT : 1 ≤ T := distortion_ge_one C
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hα : 0 ≤ α := by dsimp [α]; positivity
  obtain ⟨M₀, hM₀⟩ := uniform_prescribed_power_count c' D' A₀ ξ hc' hξ
  obtain ⟨Nd, hNd⟩ := degree_transfer c η hc hη T hT
  obtain ⟨Np, hNp⟩ := prefactor_budget (indices C).card T α ξ hξ
  refine ⟨max 3 (max (2 * C) (max (T ^ 2) (max Nd (max (T * max 2 M₀) Np)))), ?_⟩
  intro N hN W e A Q hW heven hcard hwidth hdegree hA he hQ S hS
  have hNthree : 3 ≤ N := by omega
  have hNcover : 2 * C ≤ N := by omega
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hG : 0 ≤ profile A.card Q e := (profile_pos A.card e Q he hQ).le
  let F := fun j ↦ S.filter fun n ↦ base C N j ≤ n ∧ n ≤ 2 * base C N j
  have hcells : ∀ j ∈ indices C, ((F j).card : ℝ) ≤ (base C N j : ℝ) ^ α * profile A.card Q e := by
    intro j hj
    let M := base C N j
    have hcomp := base_comparison C N j hC hNcover hj
    have hMlarge : max 2 M₀ ≤ M := base_large C N j (max 2 M₀) hC hNcover hj (by
      change T * max 2 M₀ ≤ N
      omega)
    have hwidthM : (W : ℝ) ≤ D' * (Real.log M) ^ A₀ :=
      width_transfer D A₀ T N M W hT hNthree (by omega) hcomp.1 hcomp.2 hwidth
    have hdegreeM := hNd N (by omega) M A.card hcomp.1 hcomp.2 hdegree
    exact hM₀ M (by omega) W e A Q hW heven hcard hwidthM hdegreeM hA he hQ (F j) (by
      intro n hnF
      obtain ⟨hnS, hbox⟩ := mem_filter.mp hnF
      exact ⟨hbox.1, hbox.2, (hS n hnS).2.2.1, (hS n hnS).2.2.2⟩)
  have hcount := PaperP1.ComparableCoverPower.power_bound C N hC hNcover S α (profile A.card Q e)
    hα hG (fun n hnS ↦ ⟨(hS n hnS).1, (hS n hnS).2.1⟩) hcells
  have hp := hNp N (by omega)
  have hηL : η * Real.log 2 ≤ ε / 16 := slack_log_bound ε hε
  have hexp : ξ + α ≤ 1 / 2 + c * Real.log 2 + ε := by
    dsimp [α, c', ξ]
    nlinarith only [hηL, hε]
  calc
    (S.card : ℝ) ≤ (((indices C).card : ℝ) * (T : ℝ) ^ α) * ((N : ℝ) ^ α * profile A.card Q e) := by
      simpa only [mul_assoc] using hcount
    _ ≤ (N : ℝ) ^ ξ * ((N : ℝ) ^ α * profile A.card Q e) :=
      mul_le_mul_of_nonneg_right hp (mul_nonneg (Real.rpow_nonneg hn.le _) hG)
    _ = ((N : ℝ) ^ ξ * (N : ℝ) ^ α) * profile A.card Q e := by ring
    _ = (N : ℝ) ^ (ξ + α) * profile A.card Q e := by rw [← Real.rpow_add hn]
    _ ≤ _ := mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hn1 hexp) hG

theorem fixed_kernel_count (C : ℕ) (hC : 1 ≤ C) (c D A₀ ε : ℝ) (hc : 0 ≤ c) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ W q : ℕ, ∀ A : Finset ℤ,
      0 < W → 2 ≤ A.card → (W : ℝ) ≤ D * (Real.log N) ^ A₀ →
      (A.card : ℝ) ≤ c * Real.log (Real.log N) → (∀ a ∈ A, a.natAbs ≤ W) → ∀ S : Finset ℕ,
        (∀ n ∈ S, N ≤ C * n ∧ n ≤ C * N ∧ kernel A n = q) →
        (S.card : ℝ) ≤ (N : ℝ) ^ (2 * c * Real.log 2 + ε) := by
  let η := slack ε
  let ξ := ε / 8
  let c' := c + η
  let D' := widthConstant D A₀
  let T := distortion C
  let α := 2 * c' * Real.log 2 + ξ
  have hη : 0 < η := slack_pos ε hε
  have hξ : 0 < ξ := by dsimp [ξ]; positivity
  have hc' : 0 ≤ c' := by dsimp [c']; positivity
  have hD' : 1 ≤ D' := widthConstant_ge_one D A₀
  have hT : 1 ≤ T := distortion_ge_one C
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hα : 0 ≤ α := by dsimp [α]; positivity
  obtain ⟨M₀, hM₀⟩ := PaperP1.SplitOffsetFixedKernelCount.growing_degree_fixed_kernel_count
    c' D' A₀ ξ hc' hD' hξ
  obtain ⟨Nd, hNd⟩ := degree_transfer c η hc hη T hT
  obtain ⟨Np, hNp⟩ := prefactor_budget (indices C).card T α ξ hξ
  refine ⟨max 3 (max (2 * C) (max (T ^ 2) (max Nd (max (T * max 2 M₀) Np)))), ?_⟩
  intro N hN W q A hW hcard hwidth hdegree hA S hS
  have hNthree : 3 ≤ N := by omega
  have hNcover : 2 * C ≤ N := by omega
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  let F := fun j ↦ S.filter fun n ↦ base C N j ≤ n ∧ n ≤ 2 * base C N j
  have hcells : ∀ j ∈ indices C, ((F j).card : ℝ) ≤ (base C N j : ℝ) ^ α * (1 : ℝ) := by
    intro j hj
    let M := base C N j
    have hcomp := base_comparison C N j hC hNcover hj
    have hMlarge : max 2 M₀ ≤ M := base_large C N j (max 2 M₀) hC hNcover hj (by
      change T * max 2 M₀ ≤ N
      omega)
    have hwidthM : (W : ℝ) ≤ D' * (Real.log M) ^ A₀ :=
      width_transfer D A₀ T N M W hT hNthree (by omega) hcomp.1 hcomp.2 hwidth
    have hdegreeM := hNd N (by omega) M A.card hcomp.1 hcomp.2 hdegree
    simpa only [mul_one] using hM₀ M (by omega) W q A hW hcard hwidthM hdegreeM hA (F j) (by
      intro n hnF
      obtain ⟨hnS, hbox⟩ := mem_filter.mp hnF
      exact ⟨hbox.1, hbox.2, (hS n hnS).2.2⟩)
  have hcount := PaperP1.ComparableCoverPower.power_bound C N hC hNcover S α 1 hα (by norm_num)
    (fun n hnS ↦ ⟨(hS n hnS).1, (hS n hnS).2.1⟩) hcells
  have hp := hNp N (by omega)
  have hηL : η * Real.log 2 ≤ ε / 16 := slack_log_bound ε hε
  have hexp : ξ + α ≤ 2 * c * Real.log 2 + ε := by
    dsimp [α, c', ξ]
    nlinarith only [hηL, hε]
  calc
    (S.card : ℝ) ≤ (((indices C).card : ℝ) * (T : ℝ) ^ α) * (N : ℝ) ^ α := by
      simpa only [mul_one] using hcount
    _ ≤ (N : ℝ) ^ ξ * (N : ℝ) ^ α := mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg hn.le _)
    _ = (N : ℝ) ^ (ξ + α) := by rw [← Real.rpow_add hn]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 hexp

theorem cumulative_count (C : ℕ) (hC : 1 ≤ C) (c D A₀ ε : ℝ) (hc : 0 ≤ c) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ W e : ℕ, ∀ A : Finset ℤ, ∀ β : ℝ,
      0 < W → Even A.card → 2 ≤ A.card → (W : ℝ) ≤ D * (Real.log N) ^ A₀ →
      (A.card : ℝ) ≤ c * Real.log (Real.log N) → (∀ a ∈ A, a.natAbs ≤ W) → ∀ S : Finset ℕ,
        (∀ n ∈ S, N ≤ C * n ∧ n ≤ C * N ∧ e ∣ kernel A n ∧ (kernel A n : ℝ) ≤ (N : ℝ) ^ β) →
        (S.card : ℝ) ≤ (N : ℝ) ^
          (PaperP1.SelectedQuadraticCells.baseExponent A.card β (Real.log e / Real.log N) + c * Real.log 2 + ε) := by
  obtain ⟨Np, hNp⟩ := prescribed_power_count C hC c D A₀ ε hc hε
  refine ⟨max 2 Np, ?_⟩
  intro N hN W e A β hW heven hcard hwidth hdegree hA S hS
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  by_cases he : 0 < e
  · have hQ : 0 < (N : ℝ) ^ β := Real.rpow_pos_of_pos hn β
    have hcount := hNp N (by omega) W e A ((N : ℝ) ^ β) hW heven hcard hwidth hdegree hA he hQ S hS
    have hβ : Real.log ((N : ℝ) ^ β) / Real.log N = β := by
      rw [Real.log_rpow hn]
      field_simp
    have hid := power_identity N A.card e ((N : ℝ) ^ β) (c * Real.log 2 + ε) (by omega) hcard he hQ
    rw [hβ] at hid
    have hcount' : (S.card : ℝ) ≤ (N : ℝ) ^ (1 / 2 + (c * Real.log 2 + ε)) * profile A.card ((N : ℝ) ^ β) e := by
      simpa only [add_assoc] using hcount
    simpa only [add_assoc] using hcount'.trans_eq hid.symm
  · have he0 : e = 0 := by omega
    have hempty : S = ∅ := by
      apply not_nonempty_iff_eq_empty.mp
      rintro ⟨n, hnS⟩
      have hdiv := (hS n hnS).2.2.1
      rw [he0] at hdiv
      have hz : kernel A n = 0 := by simpa using hdiv
      exact (kernel_pos A n).ne' hz
    rw [hempty, card_empty, Nat.cast_zero]
    exact Real.rpow_nonneg hn.le _

theorem constant_upper_count (C : ℕ) (hC : 1 ≤ C) (c D A₀ F ε : ℝ) (hc : 0 ≤ c) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ W e : ℕ, ∀ A : Finset ℤ, ∀ β : ℝ,
      0 < W → Even A.card → 2 ≤ A.card → (W : ℝ) ≤ D * (Real.log N) ^ A₀ →
      (A.card : ℝ) ≤ c * Real.log (Real.log N) → (∀ a ∈ A, a.natAbs ≤ W) → ∀ S : Finset ℕ,
        (∀ n ∈ S, N ≤ C * n ∧ n ≤ C * N ∧ e ∣ kernel A n ∧
          (kernel A n : ℝ) ≤ F * (N : ℝ) ^ β) →
        (S.card : ℝ) ≤ (N : ℝ) ^
          (PaperP1.SelectedQuadraticCells.baseExponent A.card β (Real.log e / Real.log N) + c * Real.log 2 + ε) := by
  obtain ⟨Nf, hNf⟩ := cumulative_count C hC c D A₀ (ε / 2) hc (by positivity)
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
  have hs := PaperP1.PrescribedSplitProductCount.base_shift_le A.card (by omega)
    β (Real.log e / Real.log N) (ε / 2) (by positivity)
  linarith

theorem dyadic_count (C : ℕ) (hC : 1 ≤ C) (c D A₀ ε : ℝ) (hc : 0 ≤ c) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ W e : ℕ, ∀ A : Finset ℤ, ∀ β : ℝ,
      0 < W → Even A.card → 2 ≤ A.card → (W : ℝ) ≤ D * (Real.log N) ^ A₀ →
      (A.card : ℝ) ≤ c * Real.log (Real.log N) → (∀ a ∈ A, a.natAbs ≤ W) → ∀ S : Finset ℕ,
        (∀ n ∈ S, N ≤ C * n ∧ n ≤ C * N ∧ (N : ℝ) ^ β ≤ kernel A n ∧
          (kernel A n : ℝ) < 2 * (N : ℝ) ^ β ∧ e ∣ kernel A n) →
        (S.card : ℝ) ≤ (N : ℝ) ^
          (PaperP1.SelectedQuadraticCells.baseExponent A.card β (Real.log e / Real.log N) + c * Real.log 2 + ε) := by
  obtain ⟨N₀, hN₀⟩ := constant_upper_count C hC c D A₀ 2 ε hc hε
  refine ⟨N₀, ?_⟩
  intro N hN W e A β hW heven hcard hwidth hdegree hA S hS
  apply hN₀ N hN W e A β hW heven hcard hwidth hdegree hA S
  intro n hn
  obtain ⟨hnlo, hnhi, _, hqhi, hediv⟩ := hS n hn
  exact ⟨hnlo, hnhi, hediv, hqhi.le⟩

theorem companion_T5_2 (C : ℕ) (hC : 1 ≤ C) (c D A₀ ε : ℝ) (hc : 0 ≤ c) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ W e : ℕ, ∀ A : Finset ℤ, ∀ β : ℝ,
      0 < W → Even A.card → 2 ≤ A.card → (W : ℝ) ≤ D * (Real.log N) ^ A₀ →
      (A.card : ℝ) ≤ c * Real.log (Real.log N) → (∀ a ∈ A, a.natAbs ≤ W) →
      (∀ S : Finset ℕ,
        (∀ n ∈ S, N ≤ C * n ∧ n ≤ C * N ∧ (N : ℝ) ^ β ≤ kernel A n ∧
          (kernel A n : ℝ) < 2 * (N : ℝ) ^ β ∧ e ∣ kernel A n) →
        (S.card : ℝ) ≤ (N : ℝ) ^
          (PaperP1.SelectedQuadraticCells.baseExponent A.card β (Real.log e / Real.log N) + c * Real.log 2 + ε)) ∧
      ∀ q : ℕ, ∀ S : Finset ℕ,
        (∀ n ∈ S, N ≤ C * n ∧ n ≤ C * N ∧ kernel A n = q) →
        (S.card : ℝ) ≤ (N : ℝ) ^ (2 * c * Real.log 2 + ε) := by
  obtain ⟨Np, hNp⟩ := dyadic_count C hC c D A₀ ε hc hε
  obtain ⟨Nf, hNf⟩ := fixed_kernel_count C hC c D A₀ ε hc hε
  refine ⟨max Np Nf, ?_⟩
  intro N hN W e A β hW heven hcard hwidth hdegree hA
  exact ⟨fun S hS ↦ hNp N (by omega) W e A β hW heven hcard hwidth hdegree hA S hS,
    fun q S hS ↦ hNf N (by omega) W q A hW hcard hwidth hdegree hA S hS⟩

theorem companion_T5_2_real_bounds (a b F : ℝ) (ha : 0 < a)
    (c D A₀ ε : ℝ) (hc : 0 ≤ c) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ W e : ℕ, ∀ A : Finset ℤ, ∀ β : ℝ,
      0 < W → Even A.card → 2 ≤ A.card → (W : ℝ) ≤ D * (Real.log N) ^ A₀ →
      (A.card : ℝ) ≤ c * Real.log (Real.log N) → (∀ a ∈ A, a.natAbs ≤ W) →
      (∀ n : ℕ, a * N ≤ n → (n : ℝ) ≤ b * N →
        0 < product A n ∧ (product A n : ℤ) = ∏ a ∈ A, ((n : ℤ) + a) ∧
          0 < ∏ a ∈ A, ((n : ℤ) + a)) ∧
      (∀ S : Finset ℕ,
        (∀ n ∈ S, a * N ≤ n ∧ (n : ℝ) ≤ b * N ∧ e ∣ kernel A n ∧
          (kernel A n : ℝ) ≤ F * (N : ℝ) ^ β) →
        (S.card : ℝ) ≤ (N : ℝ) ^
          (PaperP1.SelectedQuadraticCells.baseExponent A.card β (Real.log e / Real.log N) + c * Real.log 2 + ε)) ∧
      ∀ q : ℕ, ∀ S : Finset ℕ,
        (∀ n ∈ S, a * N ≤ n ∧ (n : ℝ) ≤ b * N ∧ kernel A n = q) →
        (S.card : ℝ) ≤ (N : ℝ) ^ (2 * c * Real.log 2 + ε) := by
  obtain ⟨C, hC, hcomp⟩ := exists_nat_comparison a b ha
  obtain ⟨Np, hNp⟩ := constant_upper_count C hC c D A₀ F ε hc hε
  obtain ⟨Nf, hNf⟩ := fixed_kernel_count C hC c D A₀ ε hc hε
  obtain ⟨Nv, hNv⟩ := source_product_values C D A₀
  refine ⟨max Np (max Nf Nv), ?_⟩
  intro N hN W e A β hW heven hcard hwidth hdegree hA
  refine ⟨?_, ?_, ?_⟩
  · intro n hnlo hnhi
    exact hNv N (by omega) n W A (hcomp N n hnlo hnhi).1 hwidth hA
  · intro S hS
    apply hNp N (by omega) W e A β hW heven hcard hwidth hdegree hA S
    intro n hnS
    obtain ⟨hnlo, hnhi, hediv, hq⟩ := hS n hnS
    exact ⟨(hcomp N n hnlo hnhi).1, (hcomp N n hnlo hnhi).2, hediv, hq⟩
  · intro q S hS
    apply hNf N (by omega) W q A hW hcard hwidth hdegree hA S
    intro n hnS
    obtain ⟨hnlo, hnhi, hq⟩ := hS n hnS
    exact ⟨(hcomp N n hnlo hnhi).1, (hcomp N n hnlo hnhi).2, hq⟩

end PaperP1.ComparableSplitProductCount
