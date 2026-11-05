module

public import PaperP1.Diophantine.QuadraticIdealDivisors
public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.Algebra.QuadraticAlgebra.NormDeterminant
public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.RingTheory.Trace.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! # The actual imaginary quadratic field and integral norm coordinates

The coefficient D is positive and arbitrary. No squarefree reduction or
conductor-comparison statement is used in this construction.
-/

/-
The basis trace/norm calculations are adapted from the existing
PaperP1/Diophantine/QuadraticOrderConductor.lean. Its Paper C source is
Vulkin-prog, Apache-2.0, commit b9fa9ba490f201b408a302a86f1594ee620b228b,
Git blob 6b970b5d96de14a796c4f0ec8fcd30cf3ebe2d11.
Here the defining coefficient is -D; the trace calculation is unchanged and
the norm is the positive form x^2+D*y^2. See LICENSE for the project licence.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.ImaginaryQuadraticOrder

open scoped NumberField QuadraticAlgebra

abbrev QD (D : ℕ) := QuadraticAlgebra ℚ (-(D : ℚ)) 0

theorem negative_not_square (D : ℕ) (hD : 0 < D) (r : ℚ) :
    r ^ 2 ≠ -(D : ℚ) + 0 * r := by
  have hDR : (0 : ℚ) < D := by exact_mod_cast hD
  nlinarith [sq_nonneg r]

instance negativeRootFact (D : ℕ) [Fact (0 < D)] :
    Fact (∀ r : ℚ, r ^ 2 ≠ -(D : ℚ) + 0 * r) := ⟨negative_not_square D Fact.out⟩

instance numberField (D : ℕ) [Fact (0 < D)] : NumberField (QD D) :=
  NumberField.of_module_finite ℚ (QD D)

instance quadraticExtension (D : ℕ) [Fact (0 < D)] : Algebra.IsQuadraticExtension ℚ (QD D) where
  finrank_eq_two' := QuadraticAlgebra.finrank_eq_two _ _

variable (D : ℕ) [Fact (0 < D)]

abbrev OK := NumberField.RingOfIntegers (QD D)

theorem omega_sq : (⟨0, 1⟩ : QD D) ^ 2 = -(D : QD D) := by
  ext <;> simp [pow_two]

theorem omega_integral : IsIntegral ℤ (⟨0, 1⟩ : QD D) := by
  apply IsIntegral.of_pow (n := 2) (by omega)
  rw [omega_sq]
  exact (isIntegral_natCast D).neg

def root : OK D := ⟨⟨0, 1⟩, omega_integral D⟩

theorem root_sq : root D * root D = -(D : OK D) := by
  apply NumberField.RingOfIntegers.ext
  change (⟨0, 1⟩ : QD D) * ⟨0, 1⟩ = -(D : QD D)
  simpa only [pow_two] using omega_sq D

theorem trace_eq (x : QD D) : Algebra.trace ℚ (QD D) x = 2 * x.re := by
  let b := QuadraticAlgebra.basis (-(D : ℚ)) 0
  have hb0 : b 0 = (1 : QD D) := by
    apply b.repr.injective
    ext i
    fin_cases i <;> simp [b, QuadraticAlgebra.basis_repr_apply]
  have hb1 : b 1 = (⟨0, 1⟩ : QD D) := by
    apply b.repr.injective
    ext i
    fin_cases i <;> simp [b, QuadraticAlgebra.basis_repr_apply]
  rw [Algebra.trace_eq_matrix_trace b, Matrix.trace_fin_two]
  simp [Algebra.leftMulMatrix_apply, LinearMap.toMatrix_apply,
    b, QuadraticAlgebra.basis_repr_apply, hb0, hb1]
  ring

theorem norm_eq (x : QD D) : Algebra.norm ℚ x = x.re ^ 2 + (D : ℚ) * x.im ^ 2 := by
  rw [Algebra.norm_apply]
  change LinearMap.det (DistribSMul.toLinearMap ℚ (QD D) x) = _
  rw [QuadraticAlgebra.det_toLinearMap_eq_norm]
  simp [QuadraticAlgebra.norm_def]
  ring

def alpha (z : ℤ × ℤ) : OK D := (z.1 : OK D) + (z.2 : OK D) * root D

def beta (z : ℤ × ℤ) : OK D := (z.1 : OK D) - (z.2 : OK D) * root D

theorem alpha_field_eq (z : ℤ × ℤ) :
    (alpha D z : QD D) = ⟨(z.1 : ℚ), (z.2 : ℚ)⟩ := by
  change (z.1 : QD D) + (z.2 : QD D) * ⟨0, 1⟩ = _
  ext <;> simp

theorem alpha_injective : Function.Injective (alpha D) := by
  intro z w he
  have hf := congrArg (fun u : OK D ↦ (u : QD D)) he
  have hx : (z.1 : ℚ) = (w.1 : ℚ) := by
    simpa only [alpha_field_eq] using congrArg QuadraticAlgebra.re hf
  have hy : (z.2 : ℚ) = (w.2 : ℚ) := by
    simpa only [alpha_field_eq] using congrArg QuadraticAlgebra.im hf
  exact Prod.ext (Int.cast_injective hx) (Int.cast_injective hy)

theorem norm_alpha (z : ℤ × ℤ) :
    Algebra.norm ℚ (alpha D z : QD D) = ((z.1 ^ 2 + (D : ℤ) * z.2 ^ 2 : ℤ) : ℚ) := by
  simp [norm_eq, alpha_field_eq]

theorem alpha_mul_beta {m : ℤ} {z : ℤ × ℤ}
    (hz : z.1 ^ 2 + (D : ℤ) * z.2 ^ 2 = m) : alpha D z * beta D z = (m : OK D) := by
  have hroot : root D ^ 2 = -(D : OK D) := by simpa only [pow_two] using root_sq D
  calc
    _ = (z.1 : OK D) ^ 2 - (z.2 : OK D) ^ 2 * root D ^ 2 := by
      dsimp only [alpha, beta]
      ring
    _ = (z.1 : OK D) ^ 2 + (D : OK D) * (z.2 : OK D) ^ 2 := by rw [hroot]; ring
    _ = _ := by exact_mod_cast hz

theorem exists_trace_integer (z : OK D) :
    ∃ k : ℤ, (k : ℚ) = Algebra.trace ℚ (QD D) (z : QD D) :=
  IsIntegrallyClosed.isIntegral_iff.mp (Algebra.isIntegral_trace z.property)

def traceInteger (z : OK D) : ℤ := Classical.choose (exists_trace_integer D z)

theorem traceInteger_cast (z : OK D) : (traceInteger D z : ℚ) = 2 * (z : QD D).re :=
  (Classical.choose_spec (exists_trace_integer D z)).trans (trace_eq D (z : QD D))

end PaperP1.ImaginaryQuadraticOrder
