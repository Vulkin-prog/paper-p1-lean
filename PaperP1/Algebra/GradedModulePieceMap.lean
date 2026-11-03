module

public import Mathlib.RingTheory.GradedAlgebra.RingHom
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.Dimension.DivisionRing
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # Actual graded component maps associated to a finite homogeneous module family -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GradedModulePieceMap

open Finset DirectSum

variable {F A B ι : Type*} [Field F] [CommRing A] [CommRing B]
  [Algebra F A] [Algebra F B] [Fintype ι]
  {G : ℕ → Submodule F A} {H : ℕ → Submodule F B}
  [GradedAlgebra G] [GradedAlgebra H]
  (f : G →+*ᵍ H) (hscalar : ∀ a : F, f (algebraMap F A a) = algebraMap F B a)
  (v : ι → B) (w : ι → ℕ) (hv : ∀ i, v i ∈ H (w i))

def algHom : A →ₐ[F] B where
  __ := f.toRingHom
  commutes' := hscalar

def map (n : ℕ) (hn : ∀ i, w i ≤ n) : (∀ i, G (n - w i)) →ₗ[F] H n where
  toFun a := ⟨∑ i, f (a i) * v i, (H n).sum_mem fun i _ ↦ by
    have hm : f (a i) * v i ∈ H ((n - w i) + w i) :=
      SetLike.mul_mem_graded (f.map_mem (a i).property) (hv i)
    simpa only [Nat.sub_add_cancel (hn i)] using hm⟩
  map_add' a b := by
    apply Subtype.ext
    simp only [Pi.add_apply, Submodule.coe_add, map_add, add_mul, Finset.sum_add_distrib]
  map_smul' r a := by
    apply Subtype.ext
    change (∑ i, f (r • (a i : A)) * v i) = r • ∑ i, f (a i) * v i
    have hs (x : A) : f (r • x) = r • f x := (algHom f hscalar).toLinearMap.map_smul r x
    simp only [hs, Algebra.smul_mul_assoc, Finset.smul_sum]

omit [GradedAlgebra G] in
theorem map_val (n : ℕ) (hn : ∀ i, w i ≤ n) (a : ∀ i, G (n - w i)) :
    (map f hscalar v w hv n hn a : B) = ∑ i, f (a i) * v i := rfl

include hv in
theorem homogeneous_representation (n : ℕ) (hn : ∀ i, w i ≤ n) {b : B} (hb : b ∈ H n)
    (a : ι → A) (ha : ∑ i, f (a i) * v i = b) :
    ∑ i, f (decompose G (a i) (n - w i)) * v i = b := by
  have he := congrArg (fun x ↦ GradedAlgebra.proj H n x) ha
  rw [map_sum] at he
  have hterm (i : ι) : GradedAlgebra.proj H n (f (a i) * v i) =
      f (decompose G (a i) (n - w i)) * v i := by
    rw [GradedAlgebra.proj_apply, coe_decompose_mul_of_right_mem_of_le H (hv i) (hn i),
      ← f.map_directSumDecompose]
  simp only [hterm, GradedAlgebra.proj_apply, decompose_of_mem_same H hb] at he
  exact he

include hv in
theorem map_surjective (hgen : ∀ b : B, ∃ a : ι → A, ∑ i, f (a i) * v i = b)
    (n : ℕ) (hn : ∀ i, w i ≤ n) : Function.Surjective (map f hscalar v w hv n hn) := by
  intro b
  obtain ⟨a, ha⟩ := hgen b
  refine ⟨fun i ↦ decompose G (a i) (n - w i), Subtype.ext ?_⟩
  exact homogeneous_representation f v w hv n hn b.property a ha

omit [GradedAlgebra G] [GradedAlgebra H] in
theorem generators_of_span
    (hgen : letI : Algebra A B := f.toRingHom.toAlgebra
      Submodule.span A (Set.range v) = ⊤) :
    ∀ b : B, ∃ a : ι → A, ∑ i, f (a i) * v i = b := by
  let : Algebra A B := f.toRingHom.toAlgebra
  intro b
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun A).mp
    (hgen.symm ▸ (show b ∈ (⊤ : Submodule A B) from trivial))
  exact ⟨a, ha⟩

include hscalar hv in
theorem finrank_le (hgen : ∀ b : B, ∃ a : ι → A, ∑ i, f (a i) * v i = b)
    (n : ℕ) (hn : ∀ i, w i ≤ n) [∀ i, Module.Finite F (G (n - w i))] :
    Module.finrank F (H n) ≤ ∑ i, Module.finrank F (G (n - w i)) := by
  have h := LinearMap.finrank_le_finrank_of_surjective (map_surjective f hscalar v w hv hgen n hn)
  rwa [Module.finrank_pi_fintype] at h

omit [GradedAlgebra G] in
theorem map_injective
    (hli : letI : Algebra A B := f.toRingHom.toAlgebra
      LinearIndependent A v) (n : ℕ) (hn : ∀ i, w i ≤ n) :
    Function.Injective (map f hscalar v w hv n hn) := by
  let : Algebra A B := f.toRingHom.toAlgebra
  intro a b hab
  have hsum : ∑ i, (a i : A) • v i = ∑ i, (b i : A) • v i := congrArg Subtype.val hab
  have he := (Fintype.linearIndependent_iffₛ.mp hli) _ _ hsum
  funext i
  exact Subtype.ext (he i)

include hscalar hv in
omit [GradedAlgebra G] in
theorem finrank_ge
    (hli : letI : Algebra A B := f.toRingHom.toAlgebra
      LinearIndependent A v) (n : ℕ) (hn : ∀ i, w i ≤ n) [Module.Finite F (H n)] :
    (∑ i, Module.finrank F (G (n - w i))) ≤ Module.finrank F (H n) := by
  have : Module.Finite F (∀ i, G (n - w i)) :=
    Module.Finite.of_injective (map f hscalar v w hv n hn) (map_injective f hscalar v w hv hli n hn)
  have : ∀ i, Module.Finite F (G (n - w i)) := fun i ↦ Module.Finite.of_pi (fun i ↦ G (n - w i)) i
  have h := LinearMap.finrank_le_finrank_of_injective (map_injective f hscalar v w hv hli n hn)
  rwa [Module.finrank_pi_fintype] at h

end PaperP1.GradedModulePieceMap
