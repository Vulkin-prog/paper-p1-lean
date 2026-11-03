module

public import PaperP1.Algebra.GradedModulePieceMap

/-! # A common module denominator has a nonzero homogeneous component with the required bounds -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.HomogeneousDenominator

open Finset DirectSum

variable {F A B ι : Type*} [Field F] [CommRing A] [CommRing B]
  [Algebra F A] [Algebra F B] [Fintype ι]
  {G : ℕ → Submodule F A} {H : ℕ → Submodule F B}
  [GradedAlgebra G] [GradedAlgebra H]
  (f : G →+*ᵍ H) (hscalar : ∀ a : F, f (algebraMap F A a) = algebraMap F B a)
  (v : ι → B) (w : ι → ℕ) (hv : ∀ i, v i ∈ H (w i))

omit [Fintype ι] [GradedAlgebra H] in
theorem exists_component_ne_zero {q : A} (hq : q ≠ 0) :
    ∃ m : ℕ, (decompose G q m : A) ≠ 0 := by
  classical
  by_contra h
  have hz : ∀ m, (decompose G q m : A) = 0 := by simpa only [not_exists, not_not] using h
  apply hq
  apply (decompose G).injective
  apply DFinsupp.ext
  intro m
  apply Subtype.ext
  simpa only [decompose_zero, DFinsupp.zero_apply, Submodule.coe_zero] using hz m

include hv in
theorem component_representation (q : A)
    (hclear : ∀ b : B, ∃ a : ι → A, ∑ i, f (a i) * v i = f q * b)
    (m n : ℕ) (hn : ∀ i, w i ≤ n + m) {b : B} (hb : b ∈ H n) :
    ∃ a : ∀ i, G (n + m - w i),
      ∑ i, f (a i) * v i = f (decompose G q m) * b := by
  obtain ⟨a, ha⟩ := hclear b
  refine ⟨fun i ↦ decompose G (a i) (n + m - w i), ?_⟩
  have he := congrArg (fun x ↦ GradedAlgebra.proj H (n + m) x) ha
  rw [map_sum] at he
  have hterm (i : ι) : GradedAlgebra.proj H (n + m) (f (a i) * v i) =
      f (decompose G (a i) (n + m - w i)) * v i := by
    rw [GradedAlgebra.proj_apply, coe_decompose_mul_of_right_mem_of_le H (hv i) (hn i),
      ← f.map_directSumDecompose]
  simp only [hterm] at he
  have hright : GradedAlgebra.proj H (n + m) (f q * b) = f (decompose G q m) * b := by
    rw [GradedAlgebra.proj_apply, Nat.add_comm n m, coe_decompose_mul_add_of_right_mem H hb,
      ← f.map_directSumDecompose]
  exact he.trans hright

def mulMap {m : ℕ} (q : A) (hq : q ∈ G m) (n : ℕ) : H n →ₗ[F] H (n + m) where
  toFun b := ⟨f q * b, by
    have hm : f q * (b : B) ∈ H (m + n) := SetLike.mul_mem_graded (f.map_mem hq) b.property
    simpa only [Nat.add_comm m n] using hm⟩
  map_add' a b := Subtype.ext (mul_add (f q) (a : B) (b : B))
  map_smul' a b := Subtype.ext (Algebra.mul_smul_comm a (f q) (b : B))

omit [Fintype ι] [GradedAlgebra G] in
theorem mulMap_injective [IsDomain B] (hinj : Function.Injective f)
    {m : ℕ} (q : A) (hq : q ∈ G m) (hq0 : q ≠ 0) (n : ℕ) :
    Function.Injective (mulMap f q hq n) := by
  intro a b hab
  apply Subtype.ext
  have hfq : f q ≠ 0 := fun h ↦ hq0 (hinj (h.trans (map_zero f).symm))
  exact mul_left_cancel₀ hfq (congrArg Subtype.val hab)

include hv in
theorem range_le (q : A)
    (hclear : ∀ b : B, ∃ a : ι → A, ∑ i, f (a i) * v i = f q * b)
    (m n : ℕ) (hn : ∀ i, w i ≤ n + m) :
    LinearMap.range (mulMap f (decompose G q m) (decompose G q m).property n) ≤
      LinearMap.range (GradedModulePieceMap.map f hscalar v w hv (n + m) hn) := by
  rintro _ ⟨b, rfl⟩
  obtain ⟨a, ha⟩ := component_representation f v w hv q hclear m n hn b.property
  exact ⟨a, Subtype.ext ha⟩

include hscalar hv in
theorem piece_finite [IsDomain B] (hinj : Function.Injective f) (q : A)
    (hclear : ∀ b : B, ∃ a : ι → A, ∑ i, f (a i) * v i = f q * b)
    (m : ℕ) (hm : (decompose G q m : A) ≠ 0) (n : ℕ) (hn : ∀ i, w i ≤ n + m)
    [∀ i, Module.Finite F (G (n + m - w i))] : Module.Finite F (H n) := by
  let t := GradedModulePieceMap.map f hscalar v w hv (n + m) hn
  let u := mulMap f (decompose G q m) (decompose G q m).property n
  have : Module.Finite F (LinearMap.range t) := Module.Finite.range t
  let u' : H n →ₗ[F] LinearMap.range t := u.codRestrict (LinearMap.range t)
    (fun b ↦ range_le f hscalar v w hv q hclear m n hn ⟨b, rfl⟩)
  exact Module.Finite.of_injective u' (fun a b hab ↦
    mulMap_injective f hinj _ _ hm n (congrArg Subtype.val hab))

include hscalar hv in
theorem finrank_le_of_component [IsDomain B] (hinj : Function.Injective f) (q : A)
    (hclear : ∀ b : B, ∃ a : ι → A, ∑ i, f (a i) * v i = f q * b)
    (m : ℕ) (hm : (decompose G q m : A) ≠ 0) (n : ℕ) (hn : ∀ i, w i ≤ n + m)
    [∀ i, Module.Finite F (G (n + m - w i))] :
    Module.finrank F (H n) ≤ ∑ i, Module.finrank F (G (n + m - w i)) := by
  let t := GradedModulePieceMap.map f hscalar v w hv (n + m) hn
  let u := mulMap f (decompose G q m) (decompose G q m).property n
  have : Module.Finite F (LinearMap.range t) := Module.Finite.range t
  calc
    Module.finrank F (H n) = Module.finrank F (LinearMap.range u) :=
      (LinearMap.finrank_range_of_inj (mulMap_injective f hinj _ _ hm n)).symm
    _ ≤ Module.finrank F (LinearMap.range t) :=
      Submodule.finrank_mono (range_le f hscalar v w hv q hclear m n hn)
    _ ≤ Module.finrank F (∀ i, G (n + m - w i)) := LinearMap.finrank_range_le t
    _ = ∑ i, Module.finrank F (G (n + m - w i)) := Module.finrank_pi_fintype _

include hscalar hv in
theorem finrank_le [IsDomain B] (hinj : Function.Injective f) (q : A) (hq : q ≠ 0)
    (hclear : ∀ b : B, ∃ a : ι → A, ∑ i, f (a i) * v i = f q * b) :
    ∃ m : ℕ, ∀ n : ℕ, (∀ i, w i ≤ n + m) →
      (∀ i, Module.Finite F (G (n + m - w i))) →
      Module.finrank F (H n) ≤ ∑ i, Module.finrank F (G (n + m - w i)) := by
  obtain ⟨m, hm⟩ := exists_component_ne_zero (G := G) hq
  refine ⟨m, fun n hn hfin ↦ ?_⟩
  let := hfin
  exact finrank_le_of_component f hscalar v w hv hinj q hclear m hm n hn

end PaperP1.HomogeneousDenominator
