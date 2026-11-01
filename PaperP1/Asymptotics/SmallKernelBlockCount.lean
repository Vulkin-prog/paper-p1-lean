module

public import PaperP1.Arithmetic.SmallKernelBlocks
public import PaperP1.Asymptotics.ExpSqrtLog
public import PaperP1.Asymptotics.UniformReal

/-! # The one-small-kernel assertion of T1.13 for arbitrary translated blocks -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SmallKernelBlockCount

open PaperP1 PaperP1.SmallKernelBlocks PaperP1.ExpSqrtLog

theorem logarithmic_blocks (K D E ε : ℝ) (hK : 0 ≤ K) (hD : 0 ≤ D) (hE : 0 ≤ E) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ G O : Finset ℤ, ∀ H X : ℕ,
      (O.card : ℝ) ≤ D * Real.log N → (H : ℝ) ≤ E * Real.log N → (X : ℝ) ≤ K * N →
      (∀ x ∈ G, ∀ u ∈ O, x + u ≤ (X : ℤ)) → ∀ T : ℝ, 0 ≤ T →
        ((starts G O H T).card : ℝ) ≤ (N : ℝ) ^ (1 / 2 + ε) * Real.sqrt T := by
  have hlin := uniformSubpolynomialOn_linear_log_add_one
    (fun N R ↦ (R : ℝ) ≤ D * Real.log N) (fun _ R ↦ R) D hD (fun _ _ h ↦ h)
  have hlin' := uniformSubpolynomialOn_const_mul (2 * Real.sqrt K) hlin
  have hexp := uniformSubpolynomialOn_exp_sqrt_of_le_log
    (fun N H ↦ (H : ℝ) ≤ E * Real.log N) (fun _ H ↦ H) 2 E (by norm_num) hE (fun _ _ h ↦ h)
  obtain ⟨Nlin, hNlin⟩ := UniformReal.uniformSubpolynomialOn_le_rpow hlin' (ε / 2) (by positivity)
  obtain ⟨Nexp, hNexp⟩ := UniformReal.uniformSubpolynomialOn_le_rpow hexp (ε / 2) (by positivity)
  refine ⟨max 1 (max Nlin Nexp), ?_⟩
  intro N hN G O H X hO hH hX hheight T hT
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hfactor : 2 * Real.sqrt K * (O.card : ℝ) ≤ (N : ℝ) ^ (ε / 2) := by
    calc
      _ ≤ 2 * Real.sqrt K * ((O.card : ℝ) + 1) := by gcongr; linarith
      _ ≤ |2 * Real.sqrt K * ((O.card : ℝ) + 1)| := le_abs_self _
      _ ≤ _ := hNlin N (by omega) O.card hO
  have hexpN : Real.exp (2 * Real.sqrt H) ≤ (N : ℝ) ^ (ε / 2) :=
    (le_abs_self _).trans (hNexp N (by omega) H hH)
  have hsqrt : Real.sqrt (X : ℝ) ≤ Real.sqrt K * Real.sqrt (N : ℝ) := by
    exact (Real.sqrt_le_sqrt hX).trans_eq (Real.sqrt_mul hK _)
  calc
    _ ≤ 2 * O.card * Real.sqrt X * Real.sqrt T * Real.exp (2 * Real.sqrt H) := finite_exp_bound T hT hheight
    _ ≤ 2 * O.card * (Real.sqrt K * Real.sqrt N) * Real.sqrt T * Real.exp (2 * Real.sqrt H) := by gcongr
    _ = Real.sqrt N * ((2 * Real.sqrt K * O.card) * Real.exp (2 * Real.sqrt H)) * Real.sqrt T := by ring
    _ ≤ Real.sqrt N * ((N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / 2)) * Real.sqrt T := by gcongr
    _ = _ := by rw [Real.sqrt_eq_rpow, ← Real.rpow_add hn, ← Real.rpow_add hn]; congr 2; ring

theorem arbitrary_selected_blocks (K D E ε : ℝ) (hK : 0 ≤ K) (hD : 0 ≤ D) (hE : 0 ≤ E) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ G O : Finset ℤ, ∀ H X : ℕ,
      (O.card : ℝ) ≤ D * Real.log N → (H : ℝ) ≤ E * Real.log N → (X : ℝ) ≤ K * N →
      (∀ x ∈ G, ∀ u ∈ O, x + u ≤ (X : ℤ)) → ∀ V : ℤ → Finset ℕ,
        (∀ x ∈ G, ∀ n ∈ V x, 0 < n ∧ (n : ℤ) - x ∈ O) → ∀ T : ℝ, 0 ≤ T →
          ((selectedStarts G V H T).card : ℝ) ≤ (N : ℝ) ^ (1 / 2 + ε) * Real.sqrt T := by
  obtain ⟨N₀, hN₀⟩ := logarithmic_blocks K D E ε hK hD hE hε
  refine ⟨N₀, ?_⟩
  intro N hN G O H X hO hH hX hheight V hV T hT
  have hcard : (selectedStarts G V H T).card ≤ (starts G O H T).card :=
    Finset.card_le_card (selected_subset hV)
  exact (by exact_mod_cast hcard : ((selectedStarts G V H T).card : ℝ) ≤
    (starts G O H T).card).trans (hN₀ N hN G O H X hO hH hX hheight T hT)

end PaperP1.SmallKernelBlockCount
