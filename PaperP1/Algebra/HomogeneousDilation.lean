module

public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.Tactic.Ring

/-! # Actual homogeneous dilation in an arbitrary graded commutative coefficient algebra -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HomogeneousDilation

open DirectSum

variable {F A : Type*} [CommRing F] [CommRing A] [Algebra F A]
  (G : ℕ → Submodule F A) [GradedAlgebra G] (b : A) (k : ℕ)

def component (n : ℕ) : G n →ₗ[F] A where
  toFun x := b ^ (k * n) * (x : A)
  map_add' x y := by simp only [Submodule.coe_add, mul_add]
  map_smul' r x := by simp only [Submodule.coe_smul, mul_smul_comm, RingHom.id_apply]

theorem component_one : (component G b k 0).toAddMonoidHom
    (GradedMonoid.GOne.one (A := fun n ↦ G n)) = 1 := by
  change b ^ (k * 0) * 1 = 1
  simp

theorem component_mul {n m : ℕ} (x : G n) (y : G m) :
    (component G b k (n + m)).toAddMonoidHom (GradedMonoid.GMul.mul (A := fun n ↦ G n) x y) =
      (component G b k n).toAddMonoidHom x * (component G b k m).toAddMonoidHom y := by
  change b ^ (k * (n + m)) * ((x : A) * (y : A)) =
    (b ^ (k * n) * (x : A)) * (b ^ (k * m) * (y : A))
  rw [Nat.mul_add, pow_add]
  ring

def map : A →ₐ[F] A :=
  (DirectSum.toAlgebra F (fun n ↦ G n) (component G b k) (component_one G b k) (component_mul G b k)).comp
    (DirectSum.decomposeAlgEquiv G).toAlgHom

theorem map_homogeneous (n : ℕ) (x : A) (hx : x ∈ G n) : map G b k x = b ^ (k * n) * x := by
  change (DirectSum.toAlgebra F (fun n ↦ G n) (component G b k) (component_one G b k)
    (component_mul G b k)) (decompose G x) = _
  rw [DirectSum.decompose_of_mem G hx]
  change DirectSum.toSemiring (fun n ↦ (component G b k n).toAddMonoidHom)
    (component_one G b k) (component_mul G b k) (DirectSum.of (fun n ↦ G n) n ⟨x, hx⟩) = _
  rw [DirectSum.toSemiring_of]
  rfl

end PaperP1.HomogeneousDilation
