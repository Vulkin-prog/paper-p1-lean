module

public import PaperP1.Arithmetic.LatePrimeStarts
public import PaperP1.Model.OneNegativePrime
public import PaperP1.Arithmetic.GoodEdgeCompression

/-! # Actual compatibility and exclusion of every leading good pair

The late population is witnessed by one concrete prime-sign sample. Its
location excludes both leading rational ratios, independently of the
private-prime threshold used to define a good edge.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.LatePrimeWindows

open Finset PaperP1.Arithmetic PaperP1.Model PaperP1.Affine
  PaperP1.Model.InfiniteStarts PaperP1.LatePrimeStarts PaperP1.GoodEdgeCompression
  PaperP1.NormalizedUnitCount

def pivot (N q : ℕ) (hq : Nat.Prime q) : PrimeUpTo (2 * N + q) :=
  ⟨⟨q, by omega⟩, hq⟩

def sample (N q : ℕ) (hq : Nat.Prime q) : SampleSpace (2 * N + q) :=
  OneNegativePrime.sample (pivot N q hq)

theorem common_start_event {N q : ℕ} (hq : Nat.Prime q) {x : ℕ} (hx : x ∈ starts N q) :
    StartEvent (valueBit (sample N q hq)) x (q - 1) := by
  obtain ⟨u, _, hu, hu1, rfl⟩ := (mem_starts N q x).mp hx
  exact (OneNegativePrime.positive_exact_run (pivot N q hq) u hu hu1).1

theorem family_compatible {N q : ℕ} (hq : Nat.Prime q) {A : Finset ℕ} (hA : A ⊆ starts N q) :
    Compatible (familyStartSystem (2 * N + q) (q - 1) (fun x : A ↦ x.val)) (familyStartRhs (q - 1)) := by
  refine ⟨sample N q hq, ?_⟩
  apply (familyStartSystem_eq_iff _ _ _ (by have h := hq.two_le; omega) _).mpr
  intro x
  exact common_start_event hq (hA x.property)

theorem joint_positive {N q : ℕ} (hq : Nat.Prime q) {A : Finset ℕ} (hA : A ⊆ starts N q) :
    0 < infiniteJointMoment (q - 1) A := by
  have hq2 := hq.two_le
  apply (infiniteJointMoment_pos_iff_jointCompatible (2 * N + q) (q - 1) A (by omega) ?_).mpr
  · exact family_compatible hq hA
  · intro x hx
    have hxb := mem_Ico.mp (starts_subset hq2 (hA hx))
    omega

theorem label_bounds {x L : ℕ} (v : Fin (L + 1)) :
    x - 1 ≤ startCompleteVertexLabel x L v ∧ startCompleteVertexLabel x L v ≤ x + L := by
  have hv := v.isLt
  unfold startCompleteVertexLabel
  split_ifs <;> omega

theorem no_leading_unit {N q x y a b : ℕ} (hq : 2 ≤ q)
    (hx : x ∈ starts N q) (hy : y ∈ dyadicBlock N) (hlead : Leading a b) :
    units a b x y (q - 1) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro u hu
  have heq := mem_units.mp hu
  have hxlate := starts_late hq hx
  have hyhi := (mem_Ico.mp hy).2
  have hleft := (label_bounds (x := x) u.1).1
  have hright := (label_bounds (x := y) u.2).2
  rcases hlead with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega

theorem no_good_edge {H : ℝ} {N q x y : ℕ} (hq : 2 ≤ q)
    (hx : x ∈ starts N q) : ¬GoodEdge H N (q - 1) x y := by
  intro hgood
  obtain ⟨_, hy, _, _, hdep, a, b, hlead, hprivate⟩ := hgood
  obtain ⟨ha, hb, _, _, _⟩ := leading_properties hlead
  have hxlate := starts_late hq hx
  have hx2 : 2 ≤ x := by omega
  have hy2 : 2 ≤ y := by
    have hylo := (mem_Ico.mp hy).1
    have hxhi := (mem_Ico.mp (starts_subset hq hx)).2
    omega
  have htwo := CompressionRank.dependent_two_units ha hb hx2 hy2 hprivate.private hdep
  rw [no_leading_unit hq hx hy hlead, card_empty] at htwo
  omega

theorem no_good_pair {H : ℝ} {N q : ℕ} (hq : 2 ≤ q) {e : Finset ℕ}
    (he : e ∈ goodEdges H N (q - 1)) : ¬e ⊆ starts N q := by
  classical
  intro hsub
  obtain ⟨xy, hxy, rfl⟩ := mem_image.mp he
  have hgood := (mem_filter.mp hxy).2
  exact no_good_edge hq (hsub (mem_insert_self _ _)) hgood

end PaperP1.LatePrimeWindows
