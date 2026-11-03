module

public import PaperP1.Algebra.FiniteQuadraticTower
public import PaperP1.Algebra.QuadraticUniversalMap

/-! # The literal tower represents exactly the simultaneous radical equations over every base algebra -/

set_option autoImplicit false

@[expose] public noncomputable section

universe u v

namespace PaperP1.QuadraticTowerPoints

open PaperP1.FiniteQuadraticTower

def lift (R : Type u) [CommRing R] (A : Type v) [CommRing A] [Algebra R A] :
    (s : List R) → (x : Fin s.length → A) → (∀ i, x i ^ 2 = algebraMap R A (s.get i)) → Tower R s →ₐ[R] A
  | [], _x, _hx => Algebra.ofId R A
  | a :: s, x, hx =>
    let φ := lift R A s (fun i ↦ x i.succ) (fun i ↦ hx i.succ)
    let hroot : x 0 ^ 2 = φ.toRingHom (algebraMap R (Tower R s) a) := by
      change x 0 ^ 2 = φ (algebraMap R (Tower R s) a)
      rw [φ.commutes]
      exact hx 0
    { toRingHom := QuadraticUniversalMap.liftRing φ.toRingHom (algebraMap R (Tower R s) a) (x 0) hroot
      commutes' := by
        intro r
        change QuadraticUniversalMap.liftRing _ _ _ _
          (algebraMap (Tower R s) (Tower R (a :: s)) (algebraMap R (Tower R s) r)) = _
        rw [QuadraticUniversalMap.liftRing_base]
        exact φ.commutes r }

theorem lift_cons_apply (R : Type u) [CommRing R] (A : Type v) [CommRing A] [Algebra R A]
    (a : R) (s : List R) (x : Fin (a :: s).length → A)
    (hx : ∀ i, x i ^ 2 = algebraMap R A ((a :: s).get i)) (z : Tower R (a :: s)) :
    lift R A (a :: s) x hx z =
      lift R A s (fun i ↦ x i.succ) (fun i ↦ hx i.succ) z.re +
        lift R A s (fun i ↦ x i.succ) (fun i ↦ hx i.succ) z.im * x 0 := rfl

theorem lift_cons_base (R : Type u) [CommRing R] (A : Type v) [CommRing A] [Algebra R A]
    (a : R) (s : List R) (x : Fin (a :: s).length → A)
    (hx : ∀ i, x i ^ 2 = algebraMap R A ((a :: s).get i)) (z : Tower R s) :
    lift R A (a :: s) x hx (algebraMap (Tower R s) (Tower R (a :: s)) z) =
      lift R A s (fun i ↦ x i.succ) (fun i ↦ hx i.succ) z := by
  rw [lift_cons_apply, QuadraticAlgebra.algebraMap_re, QuadraticAlgebra.algebraMap_im, map_zero, zero_mul, add_zero]

theorem lift_root (R : Type u) [CommRing R] (A : Type v) [CommRing A] [Algebra R A] (s : List R) :
    ∀ (x : Fin s.length → A) (hx : ∀ i, x i ^ 2 = algebraMap R A (s.get i)) (i : Fin s.length),
      lift R A s x hx (root R s i) = x i := by
  induction s with
  | nil => intro _x _hx i; exact Fin.elim0 i
  | cons a s ih =>
    intro x hx i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · rw [root_zero, lift_cons_apply, QuadraticAlgebra.re_omega, QuadraticAlgebra.im_omega,
        map_zero, map_one, one_mul, zero_add]
    · rw [root_succ, lift_cons_base]
      exact ih _ _ j

theorem hom_ext (R : Type u) [CommRing R] (A : Type v) [CommRing A] [Algebra R A] (s : List R)
    (φ ψ : Tower R s →ₐ[R] A) (hroot : ∀ i, φ (root R s i) = ψ (root R s i)) : φ = ψ := by
  apply AlgHom.ext
  intro z
  exact induction_on R s (fun w ↦ φ w = ψ w)
    (fun r ↦ by rw [φ.commutes, ψ.commutes]) hroot
    (fun x y hx hy ↦ by rw [map_add, map_add, hx, hy])
    (fun x y hx hy ↦ by rw [map_mul, map_mul, hx, hy]) z

def Solutions (R : Type u) [CommRing R] (A : Type v) [CommRing A] [Algebra R A] (s : List R) :=
  {x : Fin s.length → A // ∀ i, x i ^ 2 = algebraMap R A (s.get i)}

def pointsEquiv (R : Type u) [CommRing R] (A : Type v) [CommRing A] [Algebra R A] (s : List R) :
    (Tower R s →ₐ[R] A) ≃ Solutions R A s where
  toFun φ := ⟨fun i ↦ φ (root R s i), by
    intro i
    rw [← map_pow, root_square, φ.commutes]⟩
  invFun x := lift R A s x.val x.property
  left_inv φ := hom_ext R A s _ φ (fun i ↦ lift_root R A s _ _ i)
  right_inv x := Subtype.ext (funext fun i ↦ lift_root R A s x.val x.property i)

theorem unique_lift (R : Type u) [CommRing R] (A : Type v) [CommRing A] [Algebra R A] (s : List R)
    (x : Fin s.length → A) (hx : ∀ i, x i ^ 2 = algebraMap R A (s.get i)) :
    ∃! φ : Tower R s →ₐ[R] A, ∀ i, φ (root R s i) = x i := by
  let e := pointsEquiv R A s
  have hroot : ∀ i, e.symm ⟨x, hx⟩ (root R s i) = x i := by
    intro i
    exact congrFun (congrArg Subtype.val (e.apply_symm_apply ⟨x, hx⟩)) i
  exact ⟨e.symm ⟨x, hx⟩, hroot, fun ψ hψ ↦ hom_ext R A s ψ _ (fun i ↦ (hψ i).trans (hroot i).symm)⟩

theorem unique_ringHom (R : Type u) [CommRing R] (A : Type v) [CommRing A]
    (φ : R →+* A) (s : List R) (x : Fin s.length → A) (hx : ∀ i, x i ^ 2 = φ (s.get i)) :
    ∃! ψ : Tower R s →+* A, (∀ r, ψ (algebraMap R (Tower R s) r) = φ r) ∧
      ∀ i, ψ (root R s i) = x i := by
  let : Algebra R A := φ.toAlgebra
  obtain ⟨ψ, hψ, huniq⟩ := unique_lift R A s x hx
  refine ⟨ψ.toRingHom, ⟨fun r ↦ ψ.commutes r, hψ⟩, ?_⟩
  intro θ hθ
  let θA : Tower R s →ₐ[R] A := { toRingHom := θ, commutes' := hθ.1 }
  exact congrArg AlgHom.toRingHom (huniq θA hθ.2)

end PaperP1.QuadraticTowerPoints
