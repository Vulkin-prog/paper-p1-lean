module

public import PaperP1.Algebra.HomogeneousDilation
public import PaperP1.Algebra.GradedVeroneseChart

/-! # The actual graded dilation map into any positive Veronese algebra -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.GradedVeroneseDilation

open DirectSum

variable {F A : Type*} [CommRing F] [CommRing A] [Algebra F A]
  (G : ℕ → Submodule F A) [GradedAlgebra G] (D : ℕ) (hD : 0 < D)
  {b : A} (hb : b ∈ G 1)

include hD hb

theorem map_mem (n : ℕ) (x : A) (hx : x ∈ G n) :
    HomogeneousDilation.map G b (D - 1) x ∈ G (n * D) := by
  rw [HomogeneousDilation.map_homogeneous G b (D - 1) n x hx]
  have hm := SetLike.mul_mem_graded (SetLike.pow_mem_graded ((D - 1) * n) hb) hx
  have he : (D - 1) * n + n = n * D := by
    calc
      (D - 1) * n + n = (D - 1 + 1) * n := by ring
      _ = n * D := by rw [Nat.sub_add_cancel hD, Nat.mul_comm]
  simpa only [smul_eq_mul, mul_one, he] using hm

theorem mem_veronese (x : A) :
    HomogeneousDilation.map G b (D - 1) x ∈ GradedVeroneseAlgebra.veronese G D := by
  classical
  rw [← sum_support_decompose G x, map_sum]
  apply (GradedVeroneseAlgebra.veronese G D).sum_mem
  intro n _
  exact GradedVeroneseAlgebra.piece_mem G D n
    (map_mem G D hD hb n _ (decompose G x n).property)

def map : A →ₐ[F] GradedVeroneseAlgebra.veronese G D :=
  (HomogeneousDilation.map G b (D - 1)).codRestrict _ (mem_veronese G D hD hb)

theorem map_val (x : A) : (map G D hD hb x : A) = HomogeneousDilation.map G b (D - 1) x := rfl

theorem map_homogeneous (n : ℕ) (x : A) (hx : x ∈ G n) :
    (map G D hD hb x : A) = b ^ ((D - 1) * n) * x :=
  HomogeneousDilation.map_homogeneous G b (D - 1) n x hx

def gradedMap : G →+*ᵍ GradedVeroneseGrading.piece G D where
  __ := (map G D hD hb).toRingHom
  map_mem hx := map_mem G D hD hb _ _ hx

theorem map_coordinate : map G D hD hb b = GradedVeroneseChart.coordinate G D hb := by
  apply Subtype.ext
  rw [map_homogeneous G D hD hb 1 b hb]
  change b ^ ((D - 1) * 1) * b = b ^ D
  rw [Nat.mul_one, ← pow_succ, Nat.sub_add_cancel hD]

end PaperP1.GradedVeroneseDilation
