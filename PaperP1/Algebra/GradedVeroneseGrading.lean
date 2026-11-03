module

public import PaperP1.Algebra.GradedVeroneseAlgebra

/-! # The actual Veronese algebra has the grading obtained by dividing its degrees by D -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GradedVeroneseGrading

open DirectSum

variable {F A : Type*} [CommRing F] [CommRing A] [Algebra F A]
variable (G : ℕ → Submodule F A) [GradedAlgebra G] (D : ℕ)

attribute [local instance] GradedVeroneseAlgebra.multipleGradedMonoid

def piece (n : ℕ) : Submodule F (GradedVeroneseAlgebra.veronese G D) :=
  (G (n * D)).comap (GradedVeroneseAlgebra.veronese G D).val.toLinearMap

def component (n : ℕ) : GradedVeroneseAlgebra.veronese G D →ₗ[F] GradedVeroneseAlgebra.veronese G D where
  toFun x := ⟨GradedAlgebra.proj G (n * D) (x : A), GradedVeroneseAlgebra.piece_mem G D n (by
    rw [GradedAlgebra.proj_apply]
    exact (decompose G (x : A) (n * D)).property)⟩
  map_add' x y := by apply Subtype.ext; exact (GradedAlgebra.proj G (n * D)).map_add _ _
  map_smul' r x := by apply Subtype.ext; exact (GradedAlgebra.proj G (n * D)).map_smul r _

theorem component_val (n : ℕ) (x : GradedVeroneseAlgebra.veronese G D) :
    (component G D n x : A) = GradedAlgebra.proj G (n * D) (x : A) := rfl

theorem component_mem (n : ℕ) (x : GradedVeroneseAlgebra.veronese G D) :
    component G D n x ∈ piece G D n := by
  change GradedAlgebra.proj G (n * D) (x : A) ∈ G (n * D)
  rw [GradedAlgebra.proj_apply]
  exact (decompose G (x : A) (n * D)).property

theorem component_of_mem (hD : 0 < D) (n m : ℕ) {x : GradedVeroneseAlgebra.veronese G D}
    (hx : x ∈ piece G D m) : component G D n x = if n = m then x else 0 := by
  change (x : A) ∈ G (m * D) at hx
  by_cases hnm : n = m
  · subst n
    rw [ite_eq_left rfl]
    apply Subtype.ext
    change (decompose G (x : A) (m * D) : A) = (x : A)
    exact decompose_of_mem_same G hx
  · rw [ite_eq_right hnm]
    apply Subtype.ext
    change (decompose G (x : A) (n * D) : A) = 0
    exact decompose_of_mem_ne G hx (fun h ↦ hnm (mul_right_cancel₀ (Nat.ne_of_gt hD) h.symm))

theorem component_recompose (hD : 0 < D) (n : ℕ) (a : ⨁ m, piece G D m) :
    component G D n (DirectSum.coeAddMonoidHom (piece G D) a) = (a n : GradedVeroneseAlgebra.veronese G D) := by
  induction a using DirectSum.induction_on with
  | zero => simp only [map_zero, DFinsupp.zero_apply, Submodule.coe_zero]
  | of m x =>
    rw [DirectSum.coeAddMonoidHom_of, component_of_mem G D hD n m x.property, DirectSum.coe_of_apply]
    by_cases hnm : n = m <;> simp only [hnm, eq_comm, ite_true, ite_false]; rfl
  | add a b ha hb =>
    rw [map_add, map_add, ha, hb]
    rfl

theorem recompose_injective (hD : 0 < D) : Function.Injective (DirectSum.coeAddMonoidHom (piece G D)) := by
  intro a b hab
  apply DFinsupp.ext
  intro n
  apply Subtype.ext
  rw [← component_recompose G D hD n a, ← component_recompose G D hD n b, hab]

theorem recompose_surjective : Function.Surjective (DirectSum.coeAddMonoidHom (piece G D)) := by
  intro x
  have hlift : ∀ a : ⨁ n, G (n * D), ∃ b : ⨁ n, piece G D n,
      (DirectSum.coeAddMonoidHom (piece G D) b : A) = DirectSum.coeAlgHom (fun n ↦ G (n * D)) a := by
    intro a
    induction a using DirectSum.induction_on with
    | zero => exact ⟨0, by simp only [map_zero, ZeroMemClass.coe_zero]⟩
    | of n y =>
      let z : GradedVeroneseAlgebra.veronese G D := ⟨y, GradedVeroneseAlgebra.piece_mem G D n y.property⟩
      refine ⟨DirectSum.of (fun n ↦ piece G D n) n ⟨z, y.property⟩, ?_⟩
      rw [DirectSum.coeAddMonoidHom_of]
      exact (DirectSum.coeAlgHom_of (fun n ↦ G (n * D)) n y).symm
    | add a b ha hb =>
      obtain ⟨u, hu⟩ := ha
      obtain ⟨v, hv⟩ := hb
      refine ⟨u + v, ?_⟩
      rw [map_add]
      change (DirectSum.coeAddMonoidHom (piece G D) u : A) +
        (DirectSum.coeAddMonoidHom (piece G D) v : A) = _
      rw [hu, hv, map_add]
  obtain ⟨a, ha⟩ := x.property
  obtain ⟨b, hb⟩ := hlift a
  exact ⟨b, Subtype.ext (hb.trans ha)⟩

theorem isInternal (hD : 0 < D) : DirectSum.IsInternal (piece G D) :=
  ⟨recompose_injective G D hD, recompose_surjective G D⟩

theorem gradedMonoid : SetLike.GradedMonoid (piece G D) where
  one_mem := by
    change (1 : A) ∈ G (0 * D)
    simpa only [zero_mul] using SetLike.one_mem_graded G
  mul_mem := by
    intro n m x y hx hy
    change (x : A) ∈ G (n * D) at hx
    change (y : A) ∈ G (m * D) at hy
    change (x : A) * (y : A) ∈ G ((n + m) * D)
    simpa only [add_mul] using SetLike.mul_mem_graded hx hy

@[instance_reducible] def grading (hD : 0 < D) : GradedAlgebra (piece G D) where
  toDecomposition := (isInternal G D hD).chooseDecomposition
  toGradedMonoid := gradedMonoid G D

theorem decompose_eq_component (hD : 0 < D) (x : GradedVeroneseAlgebra.veronese G D) (n : ℕ) :
    letI := grading G D hD
    (decompose (piece G D) x n : GradedVeroneseAlgebra.veronese G D) = component G D n x := by
  let := grading G D hD
  have hh := component_recompose G D hD n (decompose (piece G D) x)
  change component G D n ((decompose (piece G D)).symm (decompose (piece G D) x)) = _ at hh
  rw [Equiv.symm_apply_apply] at hh
  exact hh.symm

theorem adjoin_piece_one_eq_top
    (hgen : GradedVeroneseAlgebra.veronese G D = Algebra.adjoin F (G D : Set A)) :
    Algebra.adjoin F (piece G D 1 : Set (GradedVeroneseAlgebra.veronese G D)) = ⊤ := by
  let S := GradedVeroneseAlgebra.veronese G D
  let T := Algebra.adjoin F (piece G D 1 : Set S)
  have hST : S ≤ T.map S.val := by
    apply hgen.le.trans
    apply Algebra.adjoin_le
    intro p hp
    change p ∈ G D at hp
    have hpn : p ∈ G (1 * D) := by simpa only [one_mul] using hp
    let y : S := ⟨p, GradedVeroneseAlgebra.piece_mem G D 1 hpn⟩
    have hy : y ∈ piece G D 1 := hpn
    exact ⟨y, Algebra.subset_adjoin hy, rfl⟩
  change T = ⊤
  apply top_unique
  intro x _hx
  obtain ⟨y, hy, hxy⟩ := hST x.property
  exact (show y = x from Subtype.ext hxy) ▸ hy

end PaperP1.GradedVeroneseGrading
