module

public import PaperP1.Algebra.FiniteBivariateScalarDecomposition
public import PaperP1.Algebra.PowerSeriesScalarIndependence
public import PaperP1.Algebra.SmoothAffineFormalBranch
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! # Exact branch-kernel descent over every field extension -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.FormalBranchScalarDescent

open Polynomial Finset Module PaperP1.PolynomialScalarProjection
  PaperP1.FiniteBivariateScalarDecomposition PaperP1.SmoothAffineFormalBranch

variable {K L ι : Type*} [Field K] [Field L] [Algebra K L]

theorem evaluation_constant (x : L) (y : PowerSeries L) (c : L) :
    evaluation x y (C (C c)) = PowerSeries.C c := by
  simp [evaluation, coefficientLift]

theorem evaluation_naturality (x : K) (y : PowerSeries K) (P : K[X][X]) :
    evaluation (algebraMap K L x) (PowerSeries.map (algebraMap K L) y) (extend P) =
      PowerSeries.map (algebraMap K L) (evaluation x y P) := by
  have he : (evaluation (algebraMap K L x) (PowerSeries.map (algebraMap K L) y)).comp
      (Polynomial.mapRingHom (Polynomial.mapRingHom (algebraMap K L))) =
        (PowerSeries.map (algebraMap K L)).comp (evaluation x y) := by
    ext <;> simp [evaluation, coefficientLift, xSeries]
  exact congrArg (fun f : K[X][X] →+* PowerSeries L ↦ f P) he

theorem components_vanish (b : Basis ι K L) (x : K) (y : PowerSeries K)
    (A : L[X][X])
    (hA : evaluation (algebraMap K L x) (PowerSeries.map (algebraMap K L) y) A = 0) :
    ∀ i ∈ componentIndices b A, evaluation x y (component (coordinate b i) A) = 0 := by
  classical
  have he := congrArg (evaluation (algebraMap K L x) (PowerSeries.map (algebraMap K L) y))
    (reconstruction b A)
  simp only [map_sum, map_mul, evaluation_constant, evaluation_naturality, hA] at he
  exact (PaperP1.PowerSeriesScalarIndependence.finite_sum_eq_zero_iff
    b b.linearIndependent (componentIndices b A)
      (fun i ↦ evaluation x y (component (coordinate b i) A))).mp he

theorem extension_kernel_with_basis (b : Basis ι K L) (P : K[X][X])
    (hP : Irreducible P) (hdeg : 0 < P.natDegree) (x : K) (y : PowerSeries K)
    (hy : evaluation x y P = 0) (A : L[X][X]) :
    evaluation (algebraMap K L x) (PowerSeries.map (algebraMap K L) y) A = 0 ↔
      extend P ∣ A := by
  classical
  constructor
  · intro hA
    have hc := components_vanish b x y A hA
    rw [← reconstruction b A]
    apply Finset.dvd_sum
    intro i hi
    have hd := (evaluation_zero_iff P hP hdeg x y hy (component (coordinate b i) A)).mp
      (hc i hi)
    obtain ⟨B, hB⟩ := hd
    have hmapped : (extend P : L[X][X]) ∣ extend (component (coordinate b i) A) := by
      refine ⟨extend B, ?_⟩
      change (component (coordinate b i) A).map (Polynomial.mapRingHom (algebraMap K L)) =
        P.map (Polynomial.mapRingHom (algebraMap K L)) *
          B.map (Polynomial.mapRingHom (algebraMap K L))
      rw [hB, Polynomial.map_mul]
    exact dvd_mul_of_dvd_right hmapped _
  · rintro ⟨B, rfl⟩
    rw [map_mul, evaluation_naturality, hy, map_zero, zero_mul]

theorem extension_kernel (P : K[X][X]) (hP : Irreducible P)
    (hdeg : 0 < P.natDegree) (x : K) (y : PowerSeries K) (hy : evaluation x y P = 0)
    (A : L[X][X]) :
    evaluation (algebraMap K L x) (PowerSeries.map (algebraMap K L) y) A = 0 ↔
      extend P ∣ A :=
  extension_kernel_with_basis (Module.Free.chooseBasis K L) P hP hdeg x y hy A

end PaperP1.FormalBranchScalarDescent
