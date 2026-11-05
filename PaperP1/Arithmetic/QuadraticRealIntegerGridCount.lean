module

public import PaperP1.Algebra.UniformPolynomialDilation
public import PaperP1.Analysis.QuadraticNormalizedGridBudget

/-! # Exact rescaling of the original closed integer box into the open unit box -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.QuadraticRealIntegerGridCount

open MvPolynomial

def normalize (N : ℕ) (z : Fin 2 → ℤ) : Fin 2 → ℝ :=
  fun i ↦ (z i : ℝ) / ((2 * N : ℕ) : ℝ)

theorem normalize_injective (N : ℕ) (hN : 0 < N) : Function.Injective (normalize N) := by
  have hden : (((2 * N : ℕ) : ℝ)) ≠ 0 := by positivity
  intro z w he
  funext i
  exact Int.cast_injective ((div_left_inj' hden).mp (congrFun he i))

theorem high_degree_count (P : MvPolynomial (Fin 2) ℝ) (hP : Irreducible P)
    (k : ℕ) (hk : 1 ≤ k) (hkD : k < P.totalDegree)
    (N : ℕ) (hN : 0 < N) (hlog : Real.log (((2 * N : ℕ) : ℝ)) ≤ k)
    (S : Finset (Fin 2 → ℤ))
    (hcurve : ∀ z ∈ S, eval (fun i ↦ (z i : ℝ)) P = 0)
    (hbox : ∀ z ∈ S, ∀ i, (z i).natAbs ≤ N) :
    (S.card : ℝ) ≤ 300000 * Real.exp 4 * (P.totalDegree : ℝ) ^ 2 *
      ((Nat.log2 (4 * N) + 1 : ℕ) : ℝ) * ((k + 1 : ℕ) : ℝ) ^ 16 := by
  classical
  let c : ℝ := ((2 * N : ℕ) : ℝ)
  have hc : 0 < c := by dsimp [c]; positivity
  let Q := UniformPolynomialDilation.substitute c P
  have hQ : Irreducible Q := UniformPolynomialDilation.irreducible c hc.ne' P hP
  have hdegree : Q.totalDegree = P.totalDegree := UniformPolynomialDilation.degree c hc.ne' P
  let T := S.image (normalize N)
  have hcard : T.card = S.card := Finset.card_image_of_injective _ (normalize_injective N hN)
  have hnorm (z : Fin 2 → ℤ) : (fun i ↦ c * normalize N z i) = fun i ↦ (z i : ℝ) := by
    funext i
    change c * ((z i : ℝ) / c) = (z i : ℝ)
    field_simp
  have hzero : ∀ w ∈ T, eval w Q = 0 := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
    rw [UniformPolynomialDilation.evaluation, hnorm]
    exact hcurve z hz
  have hunit : ∀ w ∈ T, w ∈ JointExceptionalComponentGridCount.unitBox := by
    intro w hw
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
    intro i
    have hab : |(z i : ℝ)| ≤ (N : ℝ) := by
      have hn : ((z i).natAbs : ℝ) ≤ N := by exact_mod_cast hbox z hz i
      simpa only [Nat.cast_natAbs, Int.cast_abs] using hn
    have hNc : (N : ℝ) < c := by dsimp [c]; push_cast; exact_mod_cast (by omega : N < 2 * N)
    change |(z i : ℝ) / c| < 1
    rw [abs_div, abs_of_pos hc]
    exact (div_lt_one hc).mpr (hab.trans_lt hNc)
  have hgrid : ∀ w ∈ T, ∃ z : Fin 2 → ℤ, ∀ i, w i = (z i : ℝ) / ((2 * N : ℕ) : ℝ) := by
    intro w hw
    obtain ⟨z, _hz, rfl⟩ := Finset.mem_image.mp hw
    exact ⟨z, fun _ ↦ rfl⟩
  have hb := QuadraticNormalizedGridBudget.point_count Q hQ k hk (by rw [hdegree]; exact hkD)
    (2 * N) (by omega) hlog T hzero hunit hgrid
  rw [hcard, hdegree, show 2 * (2 * N) = 4 * N by omega] at hb
  exact hb

end PaperP1.QuadraticRealIntegerGridCount
