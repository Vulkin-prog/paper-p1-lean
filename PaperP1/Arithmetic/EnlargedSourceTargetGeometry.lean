module

public import PaperP1.Arithmetic.EnlargedPairGeometry
public import PaperP1.Arithmetic.TargetUnionGeometry
public import PaperP1.Arithmetic.ActualDyadicInterior

/-! # A single actual source vertex suffices above an enlarged geometric source pair -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.EnlargedSourceTargetGeometry

open Finset PaperP1.Arithmetic PaperP1.Affine PaperP1.Model PaperP1.NormalizedWindowSets
  PaperP1.NormalizedUnitCount PaperP1.ScaledTargetValues

def sourceScale (a b : ℕ) : ℕ := a + 2 * b

theorem exists_source_vertex {a x L : ℕ} (ha : 0 < a) (hx : 0 < x) (hB : a < L + 1) :
    ∃ t : ℕ, ∃ i : Fin (L + 1), startCompleteVertexLabel x L i = a * t := by
  let t := (x - 1) / a + 1
  have hmod := Nat.mod_lt (x - 1) ha
  have heq := Nat.mod_add_div (x - 1) a
  have hmul : a * t = a * ((x - 1) / a) + a := by dsimp [t]; ring
  have hm : a * t ∈ values x L := by
    rw [values_eq_interval hx]
    exact mem_Ico.mpr ⟨by omega, by omega⟩
  obtain ⟨i, hi⟩ := mem_values.mp hm
  exact ⟨t, i, hi⟩

theorem virtual_y_bound {a b x y L t : ℕ} (ha : 0 < a) (hx : 0 < x)
    (hgeom : EnlargedPairGeometry.Geometric a b x y L) (i : Fin (L + 1))
    (hbase : startCompleteVertexLabel x L i = a * t) :
    |(b : ℤ) * t - y| ≤ (sourceScale a b : ℕ) * ((L + 1 : ℕ) : ℤ) := by
  have hlabel := congrArg (fun n : ℕ ↦ (n : ℤ)) hbase
  rw [label_cast hx] at hlabel
  push_cast at hlabel
  have heq : (a : ℤ) * ((b : ℤ) * t - y) =
      (b : ℤ) * offset i + ((b : ℤ) * x - (a : ℤ) * y) := by
    have hh := congrArg (fun z : ℤ ↦ (b : ℤ) * z) hlabel
    nlinarith only [hh]
  have habs : (a : ℤ) * |(b : ℤ) * t - y| ≤ (sourceScale a b : ℕ) * ((L + 1 : ℕ) : ℤ) := by
    calc
      _ = |(a : ℤ) * ((b : ℤ) * t - y)| := by
        simp only [abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℤ) a)]
      _ = |(b : ℤ) * offset i + ((b : ℤ) * x - (a : ℤ) * y)| := congrArg abs heq
      _ ≤ |(b : ℤ) * offset i| + |(b : ℤ) * x - (a : ℤ) * y| := abs_add_le _ _
      _ = (b : ℤ) * |offset i| + |(b : ℤ) * x - (a : ℤ) * y| := by
        rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg b)]
      _ ≤ (b : ℤ) * ((L + 1 : ℕ) : ℤ) + ((a + b : ℕ) : ℤ) * ((L + 1 : ℕ) : ℤ) :=
        add_le_add (mul_le_mul_of_nonneg_left (EnlargedPairGeometry.offset_abs i) (Nat.cast_nonneg b)) hgeom
      _ = _ := by unfold sourceScale; push_cast; ring
  have hmono := mul_le_mul_of_nonneg_right (show (1 : ℤ) ≤ a by exact_mod_cast ha) (abs_nonneg ((b : ℤ) * t - y))
  simpa only [one_mul] using hmono.trans habs

theorem anchored_representation {a b x y L : ℕ} (ha : 0 < a) (hx : 0 < x)
    (hB : a < L + 1) (hgeom : EnlargedPairGeometry.Geometric a b x y L) :
    ∃ t : ℕ, ∃ i : Fin (L + 1), startCompleteVertexLabel x L i = a * t ∧
      |(b : ℤ) * t - y| ≤ (sourceScale a b : ℕ) * ((L + 1 : ℕ) : ℤ) := by
  obtain ⟨t, i, hbase⟩ := exists_source_vertex ha hx hB
  exact ⟨t, i, hbase, virtual_y_bound ha hx hgeom i hbase⟩

theorem source_parameter_bounds {N a b x y L t : ℕ} (hN : 0 < N) (ha : 0 < a)
    (hx : x ∈ dyadicBlock N) (hy : y ∈ dyadicBlock N)
    (hgeom : EnlargedPairGeometry.Geometric a b x y L) (i : Fin (L + 1))
    (hbase : startCompleteVertexLabel x L i = a * t) :
    (N : ℤ) - (sourceScale a b : ℕ) * ((L + 1 : ℕ) : ℤ) ≤ (a : ℤ) * t ∧
      (b : ℤ) * t ≤ 2 * N + (sourceScale a b : ℕ) * ((L + 1 : ℕ) : ℤ) := by
  have hsrc := (ActualDyadicInterior.source_parameter_bounds hN hx i hbase).1
  have hD : (1 : ℤ) ≤ sourceScale a b := by exact_mod_cast (show 1 ≤ sourceScale a b by unfold sourceScale; omega)
  have hwide := mul_le_mul_of_nonneg_right hD (Nat.cast_nonneg (α := ℤ) (L + 1))
  have hyHi : (y : ℤ) ≤ 2 * N := by exact_mod_cast (mem_Ico.mp hy).2.le
  have hybound := (abs_le.mp (virtual_y_bound ha (hN.trans_le (mem_Ico.mp hx).1) hgeom i hbase)).2
  constructor <;> linarith only [hsrc, hwide, hyHi, hybound]

theorem parameter_large {N a b x L t H : ℕ} (hN : 0 < N) (ha : 0 < a)
    (hx : x ∈ dyadicBlock N) (i : Fin (L + 1)) (hbase : startCompleteVertexLabel x L i = a * t)
    (hsize : (a * sourceScale a b) * (2 * H * ((L + 1) + 1)) + (L + 1) < N) :
    2 * H * (sourceScale a b * (L + 1) + 1) < t := by
  have hsrc := (ActualDyadicInterior.source_parameter_bounds hN hx i hbase).1
  have hsrcN : N ≤ a * t + (L + 1) := by
    have hh : (N : ℤ) ≤ (a : ℤ) * t + ((L + 1 : ℕ) : ℤ) := by linarith only [hsrc]
    exact_mod_cast hh
  have hD : 1 ≤ sourceScale a b := by unfold sourceScale; omega
  by_contra hh
  have ht : t ≤ 2 * H * (sourceScale a b * (L + 1) + 1) := by omega
  have hinner : sourceScale a b * (L + 1) + 1 ≤ sourceScale a b * ((L + 1) + 1) := by
    simp only [Nat.mul_add, Nat.mul_one]
    omega
  have ht' : t ≤ sourceScale a b * (2 * H * ((L + 1) + 1)) := by
    have hmul := (Nat.mul_le_mul_left (2 * H) hinner)
    have heq : 2 * H * (sourceScale a b * ((L + 1) + 1)) =
        sourceScale a b * (2 * H * ((L + 1) + 1)) := by ring
    omega
  have hmul := Nat.mul_le_mul_left a ht'
  have heq : a * (sourceScale a b * (2 * H * ((L + 1) + 1))) =
      (a * sourceScale a b) * (2 * H * ((L + 1) + 1)) := by ring
  omega

theorem numerator_bound {N a b c d x y z L t H : ℕ} {h : ℤ} (hN : 0 < N) (ha : 0 < a)
    (hx : x ∈ dyadicBlock N) (hy : y ∈ dyadicBlock N) (hz : z ∈ dyadicBlock N)
    (hgeom : EnlargedPairGeometry.Geometric a b x y L) (i : Fin (L + 1))
    (hbase : startCompleteVertexLabel x L i = a * t) (hdH : d ≤ H) (hh : |h| ≤ H)
    (htarget : (d : ℤ) * z = (c : ℤ) * t + h)
    (hsize : (a * sourceScale a b) * (2 * H * ((L + 1) + 1)) + (L + 1) < N) : c ≤ 2 * a * H := by
  have hsrc := source_parameter_bounds hN ha hx hy hgeom i hbase
  have ht := parameter_large hN ha hx i hbase hsize
  have hr := DyadicTargetInterior.weak_ratio_bounds hsrc.1 hsrc.2 (mem_Ico.mp hz).1
    (mem_Ico.mp hz).2.le hdH hh htarget ht
  exact hr.2.trans (Nat.mul_le_mul_left (2 * a) hdH)

theorem two_progressions {a b c d x y z L : ℕ} (hab : a ≤ b) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hgeom : EnlargedPairGeometry.Geometric a b x y L) (hbase : EnlargedPairGeometry.radius b L ≤ b * x) :
    allValues a b c d x y z L ⊆
      TwoProgressionPrimeRows.progression c (EnlargedPairGeometry.base b x L) (2 * EnlargedPairGeometry.radius b L) ∪
      TwoProgressionPrimeRows.progression (a * b * d) (z - 1) L := by
  intro n hn
  rcases mem_union.mp hn with hn | hn
  · obtain ⟨m, hm, rfl⟩ := mem_image.mp hn
    exact mem_union_left _ (mem_image.mpr ⟨m,
      mem_Icc.mpr (EnlargedPairGeometry.interval_bounds hab hx hy hgeom hbase m hm), rfl⟩)
  · apply mem_union_right
    rwa [newValues, NormalizedPairGeometry.normalized_progression hz] at hn

theorem vertex_shift {b x L : ℕ} (hx : 0 < x) (i : Fin (L + 1)) :
    |((b * x : ℕ) : ℤ) - ((b * startCompleteVertexLabel x L i : ℕ) : ℤ)| ≤
      ((b * (L + 1) : ℕ) : ℤ) := by
  have heq : ((b * x : ℕ) : ℤ) - ((b * startCompleteVertexLabel x L i : ℕ) : ℤ) =
      -((b : ℤ) * offset i) := by
    push_cast
    rw [label_cast hx]
    ring
  rw [heq, abs_neg, abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℤ) b)]
  exact_mod_cast mul_le_mul_of_nonneg_left (EnlargedPairGeometry.offset_abs i)
    (Nat.cast_nonneg (α := ℤ) b)

theorem old_abs_bound {a b c H x y L : ℕ} (hab : a ≤ b) (hx : 0 < x) (hy : 0 < y)
    (hcH : c ≤ 2 * a * H) (hgeom : EnlargedPairGeometry.Geometric a b x y L)
    (i : Fin (L + 1)) (m : ℕ) (hm : m ∈ NormalizedWindowSets.union a b x y L) :
    |((c * m : ℕ) : ℤ) - (TargetUnionGeometry.anchor b c x L i : ℕ)| ≤
      (TargetUnionGeometry.radius (2 * a) b H L : ℕ) := by
  have hdist : |(m : ℤ) - ((b * startCompleteVertexLabel x L i : ℕ) : ℤ)| ≤
      ((EnlargedPairGeometry.radius b L + b * (L + 1) : ℕ) : ℤ) := by
    calc
      _ = |((m : ℤ) - ((b * x : ℕ) : ℤ)) +
          (((b * x : ℕ) : ℤ) - ((b * startCompleteVertexLabel x L i : ℕ) : ℤ))| := by congr 1; ring
      _ ≤ |(m : ℤ) - ((b * x : ℕ) : ℤ)| +
          |((b * x : ℕ) : ℤ) - ((b * startCompleteVertexLabel x L i : ℕ) : ℤ)| := abs_add_le _ _
      _ ≤ _ := by
        exact_mod_cast add_le_add (EnlargedPairGeometry.union_abs_bound hab hx hy hgeom m hm)
          (vertex_shift hx i)
  have hrad : c * (EnlargedPairGeometry.radius b L + b * (L + 1)) ≤
      TargetUnionGeometry.radius (2 * a) b H L := by
    calc
      _ ≤ (2 * a * H) * (EnlargedPairGeometry.radius b L + b * (L + 1)) :=
        Nat.mul_le_mul_right _ hcH
      _ = _ := by unfold EnlargedPairGeometry.radius TargetUnionGeometry.radius; ring
  have heq : ((c * m : ℕ) : ℤ) - (TargetUnionGeometry.anchor b c x L i : ℕ) =
      (c : ℤ) * ((m : ℤ) - ((b * startCompleteVertexLabel x L i : ℕ) : ℤ)) := by
    dsimp [TargetUnionGeometry.anchor]
    ring
  rw [heq, abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℤ) c)]
  have hmul := mul_le_mul_of_nonneg_left hdist (Nat.cast_nonneg (α := ℤ) c)
  exact hmul.trans (by exact_mod_cast hrad)

theorem all_abs_bound {a b c d H x y z L t : ℕ} (hab : a ≤ b)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hcH : c ≤ 2 * a * H) (hdH : d ≤ H)
    (hgeom : EnlargedPairGeometry.Geometric a b x y L) (i : Fin (L + 1))
    (h : ℤ) (hh : |h| ≤ H) (hbaseX : startCompleteVertexLabel x L i = a * t)
    (htarget : (d : ℤ) * z = (c : ℤ) * t + h)
    (n : ℕ) (hn : n ∈ allValues a b c d x y z L) :
    |(n : ℤ) - (TargetUnionGeometry.anchor b c x L i : ℕ)| ≤
      (TargetUnionGeometry.radius (2 * a) b H L : ℕ) := by
  rcases mem_union.mp hn with hn | hn
  · obtain ⟨m, hm, rfl⟩ := mem_image.mp hn
    exact old_abs_bound hab hx hy hcH hgeom i m hm
  · obtain ⟨v, hv, rfl⟩ := mem_image.mp hn
    obtain ⟨k, rfl⟩ := mem_values.mp hv
    have hbaseXZ : (startCompleteVertexLabel x L i : ℤ) = (a : ℤ) * t := by exact_mod_cast hbaseX
    have heq : ((a * b * d * startCompleteVertexLabel z L k : ℕ) : ℤ) -
        (TargetUnionGeometry.anchor b c x L i : ℕ) =
        (a : ℤ) * b * h + (a : ℤ) * b * d * offset k := by
      dsimp [TargetUnionGeometry.anchor]
      rw [hbaseXZ, label_cast hz]
      have hmul := congrArg (fun w : ℤ ↦ (a : ℤ) * b * w) htarget
      nlinarith only [hmul]
    rw [heq]
    calc
      _ ≤ |(a : ℤ) * b * h| + |(a : ℤ) * b * d * offset k| := abs_add_le _ _
      _ = (a : ℤ) * b * |h| + (a : ℤ) * b * d * |offset k| := by
        simp only [abs_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℤ) a),
          abs_of_nonneg (Nat.cast_nonneg (α := ℤ) b), abs_of_nonneg (Nat.cast_nonneg (α := ℤ) d)]
      _ ≤ (a : ℤ) * b * H + (a : ℤ) * b * d * ((L + 1 : ℕ) : ℤ) :=
        add_le_add (mul_le_mul_of_nonneg_left hh (by positivity))
          (mul_le_mul_of_nonneg_left (EnlargedPairGeometry.offset_abs k) (by positivity))
      _ ≤ (TargetUnionGeometry.radius a b H L : ℕ) := by
        exact_mod_cast TargetUnionGeometry.new_radius (a := a) (b := b) (L := L) hdH
      _ ≤ (TargetUnionGeometry.radius (2 * a) b H L : ℕ) := by
        have hnonneg : (0 : ℤ) ≤ TargetUnionGeometry.radius a b H L := Nat.cast_nonneg _
        have heq : TargetUnionGeometry.radius (2 * a) b H L = 2 * TargetUnionGeometry.radius a b H L := by
          unfold TargetUnionGeometry.radius
          ring
        rw [heq]
        push_cast
        omega

theorem interval_bounds {a b c d H x y z L t : ℕ} (hab : a ≤ b)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hcH : c ≤ 2 * a * H) (hdH : d ≤ H)
    (hgeom : EnlargedPairGeometry.Geometric a b x y L) (i : Fin (L + 1))
    (h : ℤ) (hh : |h| ≤ H) (hbaseX : startCompleteVertexLabel x L i = a * t)
    (htarget : (d : ℤ) * z = (c : ℤ) * t + h)
    (hrad : TargetUnionGeometry.radius (2 * a) b H L ≤ TargetUnionGeometry.anchor b c x L i)
    (n : ℕ) (hn : n ∈ allValues a b c d x y z L) :
    TargetUnionGeometry.base (2 * a) b c H x L i ≤ n ∧
      n ≤ TargetUnionGeometry.base (2 * a) b c H x L i + 2 * TargetUnionGeometry.radius (2 * a) b H L := by
  obtain ⟨hlo, hhi⟩ := abs_le.mp (all_abs_bound hab hx hy hz hcH hdH hgeom i h hh hbaseX htarget n hn)
  have hloN : TargetUnionGeometry.anchor b c x L i ≤ n + TargetUnionGeometry.radius (2 * a) b H L := by
    have hh : ((TargetUnionGeometry.anchor b c x L i : ℕ) : ℤ) ≤
        (n : ℤ) + TargetUnionGeometry.radius (2 * a) b H L := by linarith only [hlo]
    exact_mod_cast hh
  have hhiN : n ≤ TargetUnionGeometry.anchor b c x L i + TargetUnionGeometry.radius (2 * a) b H L := by
    have hh : (n : ℤ) ≤ ((TargetUnionGeometry.anchor b c x L i : ℕ) : ℤ) +
        TargetUnionGeometry.radius (2 * a) b H L := by linarith only [hhi]
    exact_mod_cast hh
  have hcancel := Nat.sub_add_cancel hrad
  unfold TargetUnionGeometry.base
  omega

end PaperP1.EnlargedSourceTargetGeometry
