module

public import PaperP1.Arithmetic.SmallKernelCrossingCertificates
public import PaperP1.Asymptotics.SmallKernelLcmGrowth
public import PaperP1.Asymptotics.SquareCertificateCount
public import PaperP1.Asymptotics.SmoothCertificateCount

/-! # Counting actual centres with several small cutoff kernels and bounded large square parts -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SeveralSmallKernelCount

open Finset PaperP1.LinearKernelFibres PaperP1.CutoffSquareParts PaperP1.LargeOddKernel
  PaperP1.SmoothModulusHosts

theorem square_crossing_bounds {N r : ℕ} {u : ℝ} (hN : 2 ≤ N) (hu : u ≤ 1)
    (hr : ((r ^ 2 : ℕ) : ℝ) ≤ 2 * N * (N : ℝ) ^ u) :
    (r : ℝ) ≤ 2 * (N : ℝ) ^ ((1 + u) / 2) ∧ r ^ 2 ≤ N ^ 3 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hr2 : (r : ℝ) ^ 2 ≤ 2 * (N : ℝ) ^ (1 + u) := by
    simpa only [Real.rpow_add hn 1 u, Real.rpow_one, Nat.cast_pow, mul_assoc] using hr
  have hp : ((N : ℝ) ^ ((1 + u) / 2)) ^ 2 = (N : ℝ) ^ (1 + u) := by
    rw [← Real.rpow_mul_natCast hn.le]
    congr 1
    ring
  have hroot : (r : ℝ) ≤ 2 * (N : ℝ) ^ ((1 + u) / 2) := by
    have hpos := Real.rpow_pos_of_pos hn ((1 + u) / 2)
    nlinarith only [hr2, hp, hpos, (show (0 : ℝ) ≤ r from Nat.cast_nonneg r)]
  have hpow : (N : ℝ) ^ (1 + u) ≤ (N : ℝ) ^ 2 := by
    simpa only [Real.rpow_two] using
      Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ) ≤ N by linarith only [hn2])
        (show 1 + u ≤ (2 : ℝ) by linarith only [hu])
  have hheight : (r : ℝ) ^ 2 ≤ (N : ℝ) ^ 3 := by
    calc
      _ ≤ 2 * (N : ℝ) ^ 2 := hr2.trans (mul_le_mul_of_nonneg_left hpow (by norm_num))
      _ ≤ _ := by nlinarith only [mul_nonneg (sq_nonneg (N : ℝ)) (sub_nonneg.mpr hn2)]
  exact ⟨hroot, by exact_mod_cast hheight⟩

theorem uniform_count (m : ℕ) (A β u E A₀ ε : ℝ) (hA : 2 ≤ A) (hu : u ≤ 1)
    (hgap : 1 < (m : ℝ) * (1 - β)) (hε : 0 < ε) :
    ∃ N₀ : ℕ, 2 ≤ N₀ ∧ ∀ N ≥ N₀, ∀ Y W : ℕ,
      (Y : ℝ) ≤ (Real.log N) ^ A → 0 < W → 2 * W ≤ Y →
      (W : ℝ) ≤ E * (Real.log N) ^ A₀ → ∀ S : Finset ℕ,
      (∀ n ∈ S, N ≤ n ∧ n ≤ 2 * N ∧ ∃ a : Fin m → ℤ,
        (∀ i, (a i).natAbs ≤ W) ∧ Function.Injective a ∧
        (∀ i, (largeOddKernel Y (value n (a i)) : ℝ) ≤ (N : ℝ) ^ β) ∧
        (∀ i, ((largeSquarePart Y (value n (a i)) ^ 2 : ℕ) : ℝ) ≤ (N : ℝ) ^ u)) →
      (S.card : ℝ) ≤ (N : ℝ) ^ (max (1 - 1 / A) ((1 + u) / 2) + ε) := by
  classical
  have hm : 0 < m := by
    by_contra h
    have hm0 : m = 0 := by omega
    simp only [hm0, Nat.cast_zero, zero_mul] at hgap
    linarith only [hgap]
  let : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  let θ := max (1 - 1 / A) ((1 + u) / 2)
  obtain ⟨NL, _hNL, hl⟩ := SmallKernelLcmGrowth.uniform_large_lcm m β 2 E A₀ (by norm_num) hgap
  obtain ⟨NS, _hNS, hs⟩ := SquareCertificateCount.uniform_count (ι := Fin m) 3 2 ((1 + u) / 2)
    E A₀ (ε / 2) (by norm_num) (by positivity)
  obtain ⟨ND, hd⟩ := SmoothCertificateCount.uniform_count (ι := Fin m) A 2 E A₀ (ε / 2)
    hA (by norm_num) (by positivity)
  obtain ⟨NA, habs⟩ := HalfCountSchedule.factor_absorption 2 (θ + ε / 2) (ε / 2) (by positivity)
  refine ⟨max 2 (max NL (max NS (max ND NA))), by omega, ?_⟩
  intro N hN Y W hY hW hWY hwidth S hS
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hn1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  let P := fun n ↦ ∃ r : ℕ, 0 < r ∧ (r : ℝ) ≤ 2 * (N : ℝ) ^ ((1 + u) / 2) ∧
    r ^ 2 ≤ N ^ 3 ∧ 2 * N ≤ r ^ 2 ∧ HasCertificate (ι := Fin m) (r ^ 2) W n
  let Q := fun n ↦ ∃ d : ℕ, 2 * N ≤ d ∧ (d : ℝ) ≤ 2 * N * (Real.log N) ^ A ∧
    largeOddKernel Y d = 1 ∧ HasCertificate (ι := Fin m) d W n
  have hactual : ∀ n ∈ S, W < n ∧ (P n ∨ Q n) := by
    intro n hnS
    obtain ⟨hnlo, hnhi, a, ha, hinj, hk, hsquare⟩ := hS n hnS
    obtain ⟨hWn, hlarge⟩ := hl N (by omega) Y W n a hW hwidth hnlo hnhi ha hinj hk
    refine ⟨hWn, ?_⟩
    obtain h | h := SmallKernelCrossingCertificates.finite_alternative Y n W a (2 * N)
      ((N : ℝ) ^ u) hWn ha hinj hWY (by linarith only [hn1]) hsquare hlarge
    · obtain ⟨r, hr, hlo, hhi, hcert⟩ := h
      obtain ⟨hroot, hheight⟩ := square_crossing_bounds (by omega) hu hhi
      have hX : 2 * N ≤ r ^ 2 := by exact_mod_cast hlo.le
      exact Or.inl ⟨r, hr, hroot, hheight, hX, hcert⟩
    · obtain ⟨d, _hdpos, hlo, hhi, hkernel, hcert⟩ := h
      have hX : 2 * N ≤ d := by exact_mod_cast hlo.le
      have hheight : (d : ℝ) ≤ 2 * N * (Real.log N) ^ A :=
        hhi.trans (mul_le_mul_of_nonneg_left hY (by positivity))
      exact Or.inr ⟨d, hX, hheight, hkernel, hcert⟩
  have hP : ((S.filter P).card : ℝ) ≤ (N : ℝ) ^ (((1 + u) / 2) + ε / 2) := by
    apply hs N (by omega) W (2 * N) hW hwidth
    intro n hnP
    obtain ⟨hnS, hp⟩ := mem_filter.mp hnP
    exact ⟨(hactual n hnS).1, (hS n hnS).2.1, hp⟩
  have hQ : ((S.filter Q).card : ℝ) ≤ (N : ℝ) ^ (1 - 1 / A + ε / 2) := by
    apply hd N (by omega) Y W (2 * N) hY hW hwidth
    intro n hnQ
    obtain ⟨hnS, hq⟩ := mem_filter.mp hnQ
    exact ⟨(hactual n hnS).1, (hS n hnS).2.1, hq⟩
  have hcover : S ⊆ (S.filter P) ∪ (S.filter Q) := by
    intro n hnS
    rcases (hactual n hnS).2 with hp | hq
    · exact mem_union.mpr (Or.inl (mem_filter.mpr ⟨hnS, hp⟩))
    · exact mem_union.mpr (Or.inr (mem_filter.mpr ⟨hnS, hq⟩))
  have hcard : S.card ≤ (S.filter P).card + (S.filter Q).card :=
    (card_le_card hcover).trans (card_union_le _ _)
  have hP' : ((S.filter P).card : ℝ) ≤ (N : ℝ) ^ (θ + ε / 2) :=
    hP.trans (Real.rpow_le_rpow_of_exponent_le hn1 (by
      dsimp [θ]; linarith only [le_max_right (1 - 1 / A) ((1 + u) / 2)]))
  have hQ' : ((S.filter Q).card : ℝ) ≤ (N : ℝ) ^ (θ + ε / 2) :=
    hQ.trans (Real.rpow_le_rpow_of_exponent_le hn1 (by
      dsimp [θ]; linarith only [le_max_left (1 - 1 / A) ((1 + u) / 2)]))
  calc
    _ ≤ ((S.filter P).card : ℝ) + ((S.filter Q).card : ℝ) := by exact_mod_cast hcard
    _ ≤ 2 * (N : ℝ) ^ (θ + ε / 2) := by linarith only [hP', hQ']
    _ ≤ (N : ℝ) ^ ((θ + ε / 2) + ε / 2) := habs N (by omega)
    _ = _ := by congr 1; dsimp [θ]; ring

end PaperP1.SeveralSmallKernelCount
