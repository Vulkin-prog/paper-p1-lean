module

public import PaperP1.Asymptotics.PrescribedQuadraticKernelCount
public import PaperP1.Asymptotics.SplitQuadraticCongruenceCount

/-! # The square-part branch of the actual prescribed quadratic-kernel count -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.QuadraticSquarePartCount

open Finset PaperP1.QuadraticKernelFibres PaperP1.QuadraticKernelRanges

@[reducible] local instance (P : Prop) : Decidable P := Classical.propDecidable P

theorem reciprocal_budget (N s e : ℝ) (hN : 0 < N) (hs : 0 < s) (he : 0 < e) :
    (3 * N / s) * (2 * N / (e * (N / (2 * s)) ^ 2) + 1) ≤
      24 * (s / e + N / s) := by
  have hid : (3 * N / s) * (2 * N / (e * (N / (2 * s)) ^ 2) + 1) =
      24 * s / e + 3 * N / s := by
    field_simp
    ring
  rw [hid]
  have hpos : 0 ≤ N / s := div_nonneg hN.le hs.le
  simp only [mul_add, mul_div_assoc]
  nlinarith

theorem second_branch_count (D A₀ ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ h e : ℕ, ∀ Q : ℝ, 0 < Q → 0 < h → 0 < e →
      (h : ℝ) ≤ D * (Real.log N) ^ A₀ → ∀ S : Finset ℕ,
        (∀ n ∈ S, N ≤ n ∧ n ≤ 2 * N ∧ Q ≤ kernel h n ∧
          (kernel h n : ℝ) < 2 * Q ∧ e ∣ kernel h n) →
        (S.card : ℝ) ≤ (N : ℝ) ^ ε * (Real.sqrt Q / e + N / Real.sqrt Q) := by
  obtain ⟨Nr, hNr⟩ := PaperP1.SplitQuadraticCongruenceCount.uniform_root_count 5 D A₀
    (ε / 2) (by positivity)
  obtain ⟨Nh, hNh⟩ := PaperP1.SplitQuadraticCongruenceCount.polylog_le_rpow D A₀ 1 (by norm_num)
  obtain ⟨Nc, hNc⟩ := PaperP1.UniformReal.uniformSubpolynomialOn_le_rpow
    (PaperP1.ExpSqrtLog.uniformSubpolynomialOn_const (fun _ _ : ℕ ↦ True) 24) (ε / 2) (by positivity)
  refine ⟨max 2 (max Nr (max Nh Nc)), ?_⟩
  intro N hN h e Q hQ hh he hshift S hS
  have hNtwo : 2 ≤ N := by omega
  have hNrpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have her : (0 : ℝ) < e := by exact_mod_cast he
  have hs : 0 < Real.sqrt Q := Real.sqrt_pos.mpr hQ
  have hhN : h ≤ N := by
    have hr := hshift.trans (hNh N (by omega))
    simpa only [Real.rpow_one, Nat.cast_le] using hr
  have hc : (24 : ℝ) ≤ (N : ℝ) ^ (ε / 2) :=
    (le_abs_self _).trans (hNc N (by omega) 0 trivial)
  let r : ℝ := N / (2 * Real.sqrt Q)
  let W : ℝ := 3 * N / Real.sqrt Q
  have hrpos : 0 < r := by dsimp [r]; positivity
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hrange : ∀ n ∈ S, r ≤ part h n ∧ (part h n : ℝ) ≤ W := by
    intro n hn
    obtain ⟨hlo, hhi, hqlo, hqhi, _⟩ := hS n hn
    exact square_part_range N h n (by omega) hlo hhi hhN Q hQ hqlo hqhi.le
  have himage : ((S.image (part h)).card : ℝ) ≤ W := by
    apply positive_card W hW
    intro v hv
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hv
    exact ⟨part_pos h n (by have hlo := (hS n hn).1; omega), (hrange n hn).2⟩
  have hfibre : ∀ v ∈ S.image (part h),
      ((S.filter fun n ↦ part h n = v).card : ℝ) ≤
        (N : ℝ) ^ (ε / 2) * (2 * N / ((e : ℝ) * r ^ 2) + 1) := by
    intro v hv
    obtain ⟨n₀, hn₀, hn₀v⟩ := mem_image.mp hv
    obtain ⟨hlo₀, hhi₀, _, _, he₀⟩ := hS n₀ hn₀
    have hvpos : 0 < v := by rw [← hn₀v]; exact part_pos h n₀ (by omega)
    have hvr : r ≤ (v : ℝ) := by simpa only [hn₀v] using (hrange n₀ hn₀).1
    have hheight : e * v ^ 2 ≤ N ^ 5 := by
      rw [← hn₀v]
      exact modulus_height N h n₀ e hNtwo hlo₀ hhi₀ hhN he₀
    have hbound := hNr N (by omega) (e * v ^ 2) (2 * N) h (by positivity) hh hheight hshift
      (S.filter fun n ↦ part h n = v) (by
        intro n hn
        have hnS := (mem_filter.mp hn).1
        exact ⟨by have hlo := (hS n hnS).1; omega, (hS n hnS).2.1⟩) (by
        intro n hn
        obtain ⟨hnS, hnv⟩ := mem_filter.mp hn
        rw [← hnv]
        exact modulus_divides h n e (by have hlo := (hS n hnS).1; omega) (hS n hnS).2.2.2.2)
    push_cast at hbound
    apply hbound.trans
    apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hNrpos.le _)
    apply add_le_add _ le_rfl
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hrpos.le hvr 2) her.le
  have hsum : (S.card : ℝ) ≤ W * ((N : ℝ) ^ (ε / 2) * (2 * N / ((e : ℝ) * r ^ 2) + 1)) := by
    calc
      (S.card : ℝ) = ∑ v ∈ S.image (part h), ((S.filter fun n ↦ part h n = v).card : ℝ) := by
        have hi := congrArg (fun m : ℕ ↦ (m : ℝ)) (card_eq_sum_card_image (part h) S)
        simpa only [Nat.cast_sum] using hi
      _ ≤ ∑ _v ∈ S.image (part h), ((N : ℝ) ^ (ε / 2) * (2 * N / ((e : ℝ) * r ^ 2) + 1)) :=
        sum_le_sum hfibre
      _ = ((S.image (part h)).card : ℝ) *
          ((N : ℝ) ^ (ε / 2) * (2 * N / ((e : ℝ) * r ^ 2) + 1)) := by simp
      _ ≤ _ := mul_le_mul_of_nonneg_right himage (by positivity)
  calc
    (S.card : ℝ) ≤ W * ((N : ℝ) ^ (ε / 2) * (2 * N / ((e : ℝ) * r ^ 2) + 1)) := hsum
    _ = (N : ℝ) ^ (ε / 2) * (W * (2 * N / ((e : ℝ) * r ^ 2) + 1)) := by ring
    _ ≤ (N : ℝ) ^ (ε / 2) * (24 * (Real.sqrt Q / e + N / Real.sqrt Q)) :=
      mul_le_mul_of_nonneg_left (reciprocal_budget N (Real.sqrt Q) e hNrpos hs her)
        (Real.rpow_nonneg hNrpos.le _)
    _ = (24 * (N : ℝ) ^ (ε / 2)) * (Real.sqrt Q / e + N / Real.sqrt Q) := by ring
    _ ≤ ((N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / 2)) * (Real.sqrt Q / e + N / Real.sqrt Q) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hNrpos.le _)) (by positivity)
    _ = _ := by rw [← Real.rpow_add hNrpos]; congr 2; ring

end PaperP1.QuadraticSquarePartCount
