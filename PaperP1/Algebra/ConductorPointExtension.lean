module

public import PaperP1.Algebra.ConductorFiberInjectivity
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring
public import Mathlib.Data.Fintype.Card

/-! # Explicit unique point extension outside the actual conductor and finite point-count transfer

The extension evaluates delta*a and divides by the nonzero value of delta.
Its existence, ring operations, scalar compatibility and uniqueness are proved.
The conductor property is explicit and must hold in the actual coefficient ring.
-/

set_option autoImplicit false
@[expose] public noncomputable section
namespace PaperP1.ConductorPointExtension
variable {F A Ω : Type*} [CommRing F] [CommRing A] [Field Ω]
  [Algebra F A] [Algebra F Ω]

def denominator (S : Subalgebra F A) (δ : A) (h : ∀ a : A, δ*a ∈ S) : S :=
  ⟨δ, by simpa only [mul_one] using h 1⟩
def cleared (S : Subalgebra F A) (δ : A) (h : ∀ a : A, δ*a ∈ S) (a : A) : S := ⟨δ*a, h a⟩

theorem cleared_one (S : Subalgebra F A) (δ : A) (h : ∀ a : A, δ*a ∈ S) :
    cleared S δ h 1 = denominator S δ h := by apply Subtype.ext; exact mul_one δ

theorem cleared_add (S : Subalgebra F A) (δ : A) (h : ∀ a : A, δ*a ∈ S) (a b : A) :
    cleared S δ h (a+b) = cleared S δ h a + cleared S δ h b := by
  apply Subtype.ext
  exact mul_add δ a b

theorem cleared_mul (S : Subalgebra F A) (δ : A) (h : ∀ a : A, δ*a ∈ S) (a b : A) :
    cleared S δ h a * cleared S δ h b = denominator S δ h * cleared S δ h (a*b) := by
  apply Subtype.ext
  change (δ*a)*(δ*b) = δ*(δ*(a*b))
  ring

theorem cleared_mem (S : Subalgebra F A) (δ : A) (h : ∀ a : A, δ*a ∈ S) (s : S) :
    cleared S δ h (s : A) = denominator S δ h * s := rfl

def extension (S : Subalgebra F A) (δ : A) (h : ∀ a : A, δ*a ∈ S)
    (ψ : S →ₐ[F] Ω) (hδ : ψ (denominator S δ h) ≠ 0) : A →ₐ[F] Ω where
  toFun a := ψ (cleared S δ h a) / ψ (denominator S δ h)
  map_one' := by rw [cleared_one, div_self hδ]
  map_zero' := by
    have hz : cleared S δ h 0 = 0 := by apply Subtype.ext; exact mul_zero δ
    rw [hz, map_zero, zero_div]
  map_add' a b := by rw [cleared_add, map_add, add_div]
  map_mul' a b := by
    have hm := congrArg ψ (cleared_mul S δ h a b)
    simp only [map_mul] at hm
    field_simp
    linear_combination -hm
  commutes' r := by
    have he : cleared S δ h (algebraMap F A r) = denominator S δ h * algebraMap F S r := rfl
    rw [he, map_mul, ψ.commutes]
    exact mul_div_cancel_left₀ _ hδ

theorem extension_restrict (S : Subalgebra F A) (δ : A) (h : ∀ a : A, δ*a ∈ S)
    (ψ : S →ₐ[F] Ω) (hδ : ψ (denominator S δ h) ≠ 0) (s : S) :
    extension S δ h ψ hδ (s : A) = ψ s := by
  change ψ (cleared S δ h (s : A)) / ψ (denominator S δ h) = ψ s
  rw [cleared_mem, map_mul]
  exact mul_div_cancel_left₀ _ hδ

theorem extension_denominator (S : Subalgebra F A) (δ : A) (h : ∀ a : A, δ*a ∈ S)
    (ψ : S →ₐ[F] Ω) (hδ : ψ (denominator S δ h) ≠ 0) :
    extension S δ h ψ hδ δ = ψ (denominator S δ h) :=
  extension_restrict S δ h ψ hδ (denominator S δ h)

theorem extension_unique (S : Subalgebra F A) (δ : A) (h : ∀ a : A, δ*a ∈ S)
    (ψ : S →ₐ[F] Ω) (hδ : ψ (denominator S δ h) ≠ 0)
    (φ : A →ₐ[F] Ω) (hφ : ∀ s : S, φ s = ψ s) :
    φ = extension S δ h ψ hδ := by
  apply PaperP1.ConductorFiberInjectivity.evaluations_equal S δ h φ (extension S δ h ψ hδ)
  · intro a ha
    exact (hφ ⟨a, ha⟩).trans (extension_restrict S δ h ψ hδ ⟨a, ha⟩).symm
  · change φ ((denominator S δ h : S) : A) ≠ 0
    rw [hφ (denominator S δ h)]
    exact hδ

theorem extension_exists_unique (S : Subalgebra F A) (δ : A) (h : ∀ a : A, δ*a ∈ S)
    (ψ : S →ₐ[F] Ω) (hδ : ψ (denominator S δ h) ≠ 0) :
    ∃! φ : A →ₐ[F] Ω, ∀ s : S, φ s = ψ s := by
  refine ⟨extension S δ h ψ hδ, extension_restrict S δ h ψ hδ, ?_⟩
  intro φ hφ
  exact extension_unique S δ h ψ hδ φ hφ

def goodPointEquiv (S : Subalgebra F A) (δ : A) (h : ∀ a : A, δ*a ∈ S) :
    {ψ : S →ₐ[F] Ω // ψ (denominator S δ h) ≠ 0} ≃
      {φ : A →ₐ[F] Ω // φ δ ≠ 0} where
  toFun ψ := ⟨extension S δ h ψ.val ψ.property, by
    rw [extension_denominator]
    exact ψ.property⟩
  invFun φ := ⟨φ.val.comp S.val, φ.property⟩
  left_inv ψ := by
    apply Subtype.ext
    apply AlgHom.ext
    intro s
    exact extension_restrict S δ h ψ.val ψ.property s
  right_inv φ := by
    apply Subtype.ext
    exact (extension_unique S δ h (φ.val.comp S.val) φ.property φ.val (fun _ ↦ rfl)).symm

theorem good_cardinality (S : Subalgebra F A) (δ : A) (h : ∀ a : A, δ*a ∈ S)
    [Fintype {ψ : S →ₐ[F] Ω // ψ (denominator S δ h) ≠ 0}]
    [Fintype {φ : A →ₐ[F] Ω // φ δ ≠ 0}] :
    Fintype.card {ψ : S →ₐ[F] Ω // ψ (denominator S δ h) ≠ 0} =
      Fintype.card {φ : A →ₐ[F] Ω // φ δ ≠ 0} :=
  Fintype.card_congr (goodPointEquiv S δ h)

open scoped Classical

theorem good_cardinality_le (S : Subalgebra F A) (δ : A) (h : ∀ a : A, δ*a ∈ S)
    [Fintype (S →ₐ[F] Ω)] [Fintype (A →ₐ[F] Ω)] :
    Fintype.card {ψ : S →ₐ[F] Ω // ψ (denominator S δ h) ≠ 0} ≤
      Fintype.card (A →ₐ[F] Ω) := by
  rw [good_cardinality S δ h]
  exact Fintype.card_subtype_le _

theorem total_cardinality_le (S : Subalgebra F A) (δ : A) (h : ∀ a : A, δ*a ∈ S)
    [Fintype (S →ₐ[F] Ω)] [Fintype (A →ₐ[F] Ω)] :
    Fintype.card (S →ₐ[F] Ω) ≤ Fintype.card (A →ₐ[F] Ω) +
      Fintype.card {ψ : S →ₐ[F] Ω // ψ (denominator S δ h) = 0} := by
  have hsplit := Fintype.card_subtype_compl (fun ψ : S →ₐ[F] Ω ↦ ψ (denominator S δ h) = 0)
  have hgood := good_cardinality_le (Ω := Ω) S δ h
  have hzero := Fintype.card_subtype_le (fun ψ : S →ₐ[F] Ω ↦ ψ (denominator S δ h) = 0)
  change Fintype.card {ψ : S →ₐ[F] Ω // ψ (denominator S δ h) ≠ 0} = _ at hsplit
  omega

end PaperP1.ConductorPointExtension
