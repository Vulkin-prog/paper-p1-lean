module

public import PaperP1.Arithmetic.SmoothModulusHosts
public import PaperP1.Asymptotics.PolylogSmoothModuli

/-! # Summing actual large smooth modulus certificates over centres -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SmoothCertificateCount

open Finset PaperP1.SmallKernelCount PaperP1.SmoothModulusHosts

theorem uniform_count {ι : Type*} [Fintype ι] (A C E A₀ ε : ℝ)
    (hA : 2 ≤ A) (hC : 0 ≤ C) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ Y W X : ℕ,
      (Y : ℝ) ≤ (Real.log N) ^ A → 0 < W → (W : ℝ) ≤ E * (Real.log N) ^ A₀ →
      ∀ S : Finset ℕ,
      (∀ n ∈ S, W < n ∧ n ≤ X ∧ ∃ m : ℕ, X ≤ m ∧ (m : ℝ) ≤ C * N * (Real.log N) ^ A ∧
        PaperP1.LargeOddKernel.largeOddKernel Y m = 1 ∧ HasCertificate (ι := ι) m W n) →
      (S.card : ℝ) ≤ (N : ℝ) ^ (1 - 1 / A + ε) := by
  classical
  let k := Fintype.card ι
  let η := ε / (4 * ((k : ℝ) + 1))
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨Nm, hNm⟩ := PaperP1.PolylogSmoothModuli.odd_smooth_count A C (ε / 2) hA hC (by positivity)
  obtain ⟨Nd, hNd⟩ := PaperP1.DivisorSubpolynomial.card_divisors_le_rpow_eventually 2 η hη
  obtain ⟨No, hNo⟩ := PaperP1.SplitQuadraticCongruenceCount.polylog_le_rpow (3 * E) A₀ η hη
  obtain ⟨Nh, hNh⟩ := PaperP1.SplitQuadraticCongruenceCount.polylog_le_rpow C A 1 (by norm_num)
  refine ⟨max 2 (max Nm (max Nd (max No Nh))), ?_⟩
  intro N hN Y W X hY hW hwidth S hS
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hl : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  let Z := ⌊C * N * (Real.log N) ^ A⌋₊
  let M := smallKernelValues Y 1 Z
  let I := M.filter fun m ↦ X ≤ m
  let F := fun m ↦ S.filter fun n ↦ HasCertificate (ι := ι) m W n
  have hZ : (Z : ℝ) ≤ C * N * (Real.log N) ^ A := Nat.floor_le (by positivity)
  have hZheight : Z ≤ N ^ 2 := by
    have hp := hNh N (by omega)
    rw [Real.rpow_one] at hp
    have hmul := mul_le_mul_of_nonneg_right hp hn.le
    have hbound : (Z : ℝ) ≤ (N : ℝ) ^ 2 := by nlinarith only [hZ, hmul]
    exact_mod_cast hbound
  have hM : (M.card : ℝ) ≤ (N : ℝ) ^ (1 - 1 / A + ε / 2) := by
    apply hNm N (by omega) Y Z hY hZ M
    intro m hm
    obtain ⟨hpos, hupper, hkernel⟩ := mem_smallKernelValues.mp hm
    have heq : PaperP1.LargeOddKernel.largeOddKernel Y m = 1 := by
      have hp := PaperP1.SmallPrimeBudget.largeOddKernel_pos Y m
      omega
    exact ⟨hpos, hupper, heq⟩
  have hoff : (2 * W + 1 : ℝ) ≤ (N : ℝ) ^ η := by
    have hwone : (1 : ℝ) ≤ W := by exact_mod_cast hW
    exact (show (2 * W + 1 : ℝ) ≤ 3 * E * (Real.log N) ^ A₀ by nlinarith only [hwidth, hwone]).trans
      (hNo N (by omega))
  have hcover : ∀ n ∈ S, ∃ m ∈ I, n ∈ F m := by
    intro n hnS
    obtain ⟨m, hXm, hheight, hkernel, hcert⟩ := (hS n hnS).2.2
    have hmpos : 0 < m := by
      have hnlo := (hS n hnS).1
      have hnhi := (hS n hnS).2.1
      omega
    have hmM : m ∈ M := mem_smallKernelValues.mpr ⟨hmpos, Nat.le_floor hheight, hkernel.le⟩
    exact ⟨m, mem_filter.mpr ⟨hmM, hXm⟩, mem_filter.mpr ⟨hnS, hcert⟩⟩
  have hF : ∀ m ∈ I, ((F m).card : ℝ) ≤ (N : ℝ) ^ (ε / 2) := by
    intro m hmI
    obtain ⟨hmM, hXm⟩ := mem_filter.mp hmI
    have hmd := mem_smallKernelValues.mp hmM
    have hd := hNd N (by omega) m (hmd.2.1.trans hZheight)
    have hc := fixed_modulus_count m W X hmd.1 hXm (F m) (by
      intro n hnF
      obtain ⟨hnS, hcert⟩ := mem_filter.mp hnF
      exact ⟨(hS n hnS).1, (hS n hnS).2.1, hcert⟩)
    have hcast : ((F m).card : ℝ) ≤ (2 * W + 1 : ℝ) ^ k * (m.divisors.card : ℝ) ^ k := by
      exact_mod_cast hc
    have hηeq : η * (4 * ((k : ℝ) + 1)) = ε := by
      dsimp [η]
      exact div_mul_cancel₀ _ (by positivity)
    have hexp : η * (k : ℝ) + η * (k : ℝ) ≤ ε / 2 := by nlinarith only [hηeq, hη]
    calc
      _ ≤ (2 * W + 1 : ℝ) ^ k * (m.divisors.card : ℝ) ^ k := hcast
      _ ≤ ((N : ℝ) ^ η) ^ k * ((N : ℝ) ^ η) ^ k := by gcongr
      _ = (N : ℝ) ^ (η * (k : ℝ) + η * (k : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hn.le, ← Real.rpow_add hn]
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn1 hexp
  have hI : (I.card : ℝ) ≤ (N : ℝ) ^ (1 - 1 / A + ε / 2) :=
    (show (I.card : ℝ) ≤ M.card by exact_mod_cast (card_filter_le M (fun m ↦ X ≤ m))).trans hM
  calc
    _ ≤ (I.card : ℝ) * (N : ℝ) ^ (ε / 2) :=
      PaperP1.FiniteCoverCount.cardinal_le S I F _ hcover hF
    _ ≤ (N : ℝ) ^ (1 - 1 / A + ε / 2) * (N : ℝ) ^ (ε / 2) :=
      mul_le_mul_of_nonneg_right hI (Real.rpow_nonneg hn.le _)
    _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring

end PaperP1.SmoothCertificateCount
