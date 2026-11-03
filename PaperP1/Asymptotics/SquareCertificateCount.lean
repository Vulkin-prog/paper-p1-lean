module

public import PaperP1.Arithmetic.SmoothModulusHosts
public import PaperP1.Asymptotics.HalfCountSchedule
public import PaperP1.Asymptotics.SplitQuadraticCongruenceCount
public import PaperP1.Arithmetic.DivisorSubpolynomial

/-! # Actual large square modulus certificates cost the number of possible square roots -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SquareCertificateCount

open Finset PaperP1.SmoothModulusHosts

theorem uniform_count {ι : Type*} [Fintype ι] (K : ℕ) (C θ E A₀ ε : ℝ)
    (hC : 0 ≤ C) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ W X : ℕ,
      0 < W → (W : ℝ) ≤ E * (Real.log N) ^ A₀ → ∀ S : Finset ℕ,
      (∀ n ∈ S, W < n ∧ n ≤ X ∧ ∃ r : ℕ, 0 < r ∧ (r : ℝ) ≤ C * (N : ℝ) ^ θ ∧
        r ^ 2 ≤ N ^ K ∧ X ≤ r ^ 2 ∧ HasCertificate (ι := ι) (r ^ 2) W n) →
      (S.card : ℝ) ≤ (N : ℝ) ^ (θ + ε) := by
  classical
  let k := Fintype.card ι
  let η := ε / (4 * ((k : ℝ) + 1))
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨ND, hd⟩ := DivisorSubpolynomial.card_divisors_le_rpow_eventually K η hη
  obtain ⟨NO, ho⟩ := SplitQuadraticCongruenceCount.polylog_le_rpow (3 * E) A₀ η hη
  obtain ⟨NC, hc⟩ := HalfCountSchedule.factor_absorption C θ (ε / 2) (by positivity)
  refine ⟨max 2 (max ND (max NO NC)), by omega, ?_⟩
  intro N hN W X hW hwidth S hS
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  let R := Icc 1 ⌊C * (N : ℝ) ^ θ⌋₊
  let M := (R.image fun r ↦ r ^ 2).filter fun m ↦ X ≤ m ∧ m ≤ N ^ K
  let F := fun m ↦ S.filter fun n ↦ HasCertificate (ι := ι) m W n
  have hM : (M.card : ℝ) ≤ (N : ℝ) ^ (θ + ε / 2) := by
    calc
      _ ≤ (R.card : ℝ) := by exact_mod_cast (card_filter_le _ _).trans card_image_le
      _ = (⌊C * (N : ℝ) ^ θ⌋₊ : ℝ) := by simp only [R, Nat.card_Icc]; congr 1
      _ ≤ C * (N : ℝ) ^ θ := Nat.floor_le (mul_nonneg hC (Real.rpow_nonneg hn.le _))
      _ ≤ _ := hc N (by omega)
  have hoff : (2 * W + 1 : ℝ) ≤ (N : ℝ) ^ η := by
    have hwone : (1 : ℝ) ≤ W := by exact_mod_cast hW
    exact (show (2 * W + 1 : ℝ) ≤ 3 * E * (Real.log N) ^ A₀ by nlinarith only [hwidth, hwone]).trans
      (ho N (by omega))
  have hcover : ∀ n ∈ S, ∃ m ∈ M, n ∈ F m := by
    intro n hnS
    obtain ⟨r, hr, hroot, hheight, hX, hcert⟩ := (hS n hnS).2.2
    exact ⟨r ^ 2, mem_filter.mpr ⟨mem_image.mpr ⟨r, mem_Icc.mpr ⟨hr, Nat.le_floor hroot⟩, rfl⟩,
      hX, hheight⟩, mem_filter.mpr ⟨hnS, hcert⟩⟩
  have hF : ∀ m ∈ M, ((F m).card : ℝ) ≤ (N : ℝ) ^ (ε / 2) := by
    intro m hm
    obtain ⟨hmR, hXm, hheight⟩ := mem_filter.mp hm
    obtain ⟨r, hr, rfl⟩ := mem_image.mp hmR
    have hrpos : 0 < r := (mem_Icc.mp hr).1
    have hdiv := hd N (by omega) (r ^ 2) hheight
    have hfinite := fixed_modulus_count (r ^ 2) W X (pow_pos hrpos _) hXm (F (r ^ 2)) (by
      intro n hnF
      obtain ⟨hnS, hcert⟩ := mem_filter.mp hnF
      exact ⟨(hS n hnS).1, (hS n hnS).2.1, hcert⟩)
    have hcast : ((F (r ^ 2)).card : ℝ) ≤ (2 * W + 1 : ℝ) ^ k * ((r ^ 2).divisors.card : ℝ) ^ k := by
      exact_mod_cast hfinite
    have hηeq : η * (4 * ((k : ℝ) + 1)) = ε := by
      dsimp [η]
      exact div_mul_cancel₀ _ (by positivity)
    have hexp : η * (k : ℝ) + η * (k : ℝ) ≤ ε / 2 := by nlinarith only [hηeq, hη]
    calc
      _ ≤ (2 * W + 1 : ℝ) ^ k * ((r ^ 2).divisors.card : ℝ) ^ k := hcast
      _ ≤ ((N : ℝ) ^ η) ^ k * ((N : ℝ) ^ η) ^ k := by gcongr
      _ = (N : ℝ) ^ (η * (k : ℝ) + η * (k : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le, ← Real.rpow_add hn]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 hexp
  calc
    _ ≤ (M.card : ℝ) * (N : ℝ) ^ (ε / 2) := FiniteCoverCount.cardinal_le S M F _ hcover hF
    _ ≤ (N : ℝ) ^ (θ + ε / 2) * (N : ℝ) ^ (ε / 2) :=
      mul_le_mul_of_nonneg_right hM (Real.rpow_nonneg hn.le _)
    _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring

end PaperP1.SquareCertificateCount
