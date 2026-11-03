module

public import PaperP1.Arithmetic.SourceIntegerLift
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Fintype.Pi

/-! # Actual bounded normalized integer points of the chosen source embedding -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.SourceIntegerPoints

open Finset PaperP1.SourceProjectiveEmbedding

variable {ι : Type}

def normalizer (D : ℕ) : GeneratorIndex ℚ ι D :=
  SplitWeightedGeneratorIndex.indexEquiv ℚ ι D (Sum.inl ⟨Finsupp.single (2 : Fin 3) D, by
    rw [Finsupp.degree_single]⟩)

def affineIndex (D : ℕ) (hD : 0 < D) (j : Fin 3) : GeneratorIndex ℚ ι D :=
  SplitWeightedGeneratorIndex.indexEquiv ℚ ι D (Sum.inl
    ⟨Finsupp.single j 1 + Finsupp.single (2 : Fin 3) (D - 1), by
      rw [map_add, Finsupp.degree_single, Finsupp.degree_single]
      omega⟩)

def host (D : ℕ) (hD : 0 < D) (v : GeneratorIndex ℚ ι D → ℤ) : ℤ × ℤ :=
  (v (affineIndex D hD 1), v (affineIndex D hD 0))

theorem point_normalizer (D : ℕ) (x y : ℤ) (w : ι → ℤ) :
    SourceIntegerLift.point D x y w (normalizer D) = 1 := by
  rw [normalizer, SourceIntegerLift.point_base]
  norm_num [Finsupp.single_apply]

theorem host_point (D : ℕ) (hD : 0 < D) (x y : ℤ) (w : ι → ℤ) :
    host D hD (SourceIntegerLift.point D x y w) = (x, y) := by
  simp [host, affineIndex, SourceIntegerLift.point_base]

local instance indexFinite (D : ℕ) [Finite ι] : Finite (GeneratorIndex ℚ ι D) := index_finite ℚ ι D
local instance indexFintype (D : ℕ) [Finite ι] : Fintype (GeneratorIndex ℚ ι D) := Fintype.ofFinite _

variable [Finite ι]

def box (D H : ℕ) : Finset (GeneratorIndex ℚ ι D → ℤ) := by
  classical
  exact (Fintype.piFinset fun _ ↦ Icc (-(H : ℤ)) H).filter fun v ↦ v (normalizer D) = 1

def curvePoints (D : ℕ) (Q : Ideal (MvPolynomial (GeneratorIndex ℚ ι D) ℚ)) (H : ℕ) :
    Finset (GeneratorIndex ℚ ι D → ℤ) := by
  classical
  exact (box D H).filter fun v ↦ Q ≤ RingHom.ker (SourceIntegerLift.evaluation D v).toRingHom

theorem mem_box (D H : ℕ) (v : GeneratorIndex ℚ ι D → ℤ) :
    v ∈ box D H ↔ (∀ i, |v i| ≤ (H : ℤ)) ∧ v (normalizer D) = 1 := by
  classical
  simp only [box, mem_filter, Fintype.mem_piFinset, mem_Icc, ← abs_le]

theorem mem_curvePoints (D : ℕ) (Q : Ideal (MvPolynomial (GeneratorIndex ℚ ι D) ℚ)) (H : ℕ)
    (v : GeneratorIndex ℚ ι D → ℤ) :
    v ∈ curvePoints D Q H ↔ ((∀ i, |v i| ≤ (H : ℤ)) ∧ v (normalizer D) = 1) ∧
      Q ≤ RingHom.ker (SourceIntegerLift.evaluation D v).toRingHom := by
  classical
  simp only [curvePoints, mem_filter, mem_box]

end PaperP1.SourceIntegerPoints
