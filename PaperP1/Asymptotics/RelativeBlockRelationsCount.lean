module

public import PaperP1.Arithmetic.RelativeBlockRelations
public import PaperP1.Arithmetic.FiniteBlockAppend
public import PaperP1.Asymptotics.ValueHeightHalfCount

/-! # A half power for every block participating in a relative relation

The support of one actual relation is exposed first. Every remaining block
still participates relative to the enlarged old full value span. Strong
induction supplies every actual extension count for fewer new blocks.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.RelativeBlockRelationsCount

open Finset PaperP1.EffectiveExposure PaperP1.RelativeBlockRelations PaperP1.FiniteBlockAppend

def UniformCount (r s : ℕ) (a b E ε : ℝ) : Prop :=
  ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ old : Fin s → ℕ, ∀ oldBlocks : Fin s → Finset ℕ,
    ∀ G : Finset ℕ, ∀ blocks : Fin r → ℕ → Finset ℕ,
    (∀ i, ∀ x ∈ G, ∀ v ∈ blocks i x, a * N ≤ v ∧ (v : ℝ) ≤ b * N) →
    (∀ k, ∀ v ∈ oldBlocks k, a * N ≤ v ∧ (v : ℝ) ≤ b * N) →
    (∀ i, ∀ x ∈ G, ∀ v ∈ blocks i x, (((v : ℤ) - x).natAbs : ℝ) ≤ E * Real.log N) →
    (∀ k, ∀ v ∈ oldBlocks k, (((v : ℤ) - old k).natAbs : ℝ) ≤ E * Real.log N) →
    ((PaperP1.RelativeBlockRelations.population G blocks (univ.biUnion oldBlocks)).card : ℝ) ≤
      (N : ℝ) ^ ((r : ℝ) / 2 + ε)

theorem zero_count (s : ℕ) (a b E ε : ℝ) (hε : 0 < ε) : UniformCount 0 s a b E ε := by
  refine ⟨2, ?_⟩
  intro N hN old oldBlocks G blocks _ _ _ _
  have hc : ((PaperP1.RelativeBlockRelations.population G blocks (univ.biUnion oldBlocks)).card : ℝ) ≤ 1 := by
    exact_mod_cast PaperP1.RelativeBlockRelations.zero_card G blocks (univ.biUnion oldBlocks)
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  exact hc.trans (by simpa only [Nat.cast_zero, zero_div, zero_add] using Real.one_le_rpow hn hε.le)

theorem induction_step (r : ℕ) (a b E : ℝ) (ha : 0 < a) (hE : 0 ≤ E)
    (hIH : ∀ k < r + 1, ∀ s : ℕ, ∀ ε : ℝ, 0 < ε → UniformCount k s a b E ε) :
    ∀ s : ℕ, ∀ ε : ℝ, 0 < ε → UniformCount (r + 1) s a b E ε := by
  classical
  intro s ε hε
  let η := ε / 4
  have hη : 0 < η := by dsimp [η]; positivity
  have hi := fun k : Fin (r + 1) ↦ hIH k.val k.isLt (s + (r + 1 - k.val)) η hη
  choose NI hNI using hi
  have he := fun k : Fin (r + 1) ↦ PaperP1.ValueHeightHalfCount.uniform_logarithmic_count
    (r + 1 - k.val) s a b E η ha hE hη
  choose NE hNE using he
  let p := ((r + 1 : ℕ) : ℝ) / 2
  obtain ⟨NF, hNF⟩ := PaperP1.HalfCountSchedule.factor_absorption
    (Fintype.card (Code (r + 1))) (p + ε / 2) (ε / 2) (by positivity)
  refine ⟨2 + NF + univ.sup NI + univ.sup NE, ?_⟩
  intro N hN old oldBlocks G blocks hvalues holdValues hdist holdDist
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hIn : ∀ k : Fin (r + 1), NI k ≤ N := by
    intro k
    have hk : NI k ≤ univ.sup NI := le_sup (f := NI) (mem_univ k)
    omega
  have hEn : ∀ k : Fin (r + 1), NE k ≤ N := by
    intro k
    have hk : NE k ≤ univ.sup NE := le_sup (f := NE) (mem_univ k)
    omega
  let O := univ.biUnion oldBlocks
  have hcell : ∀ c : Code (r + 1),
      ((PaperP1.RelativeBlockRelations.cell G blocks O c).card : ℝ) ≤ (N : ℝ) ^ (p + ε / 2) := by
    intro c
    have hB : ∀ q ∈ PaperP1.EffectiveWindowLists.lists G (rightBlocks c blocks) O,
        ((PaperP1.RelativeBlockRelations.population G (leftBlocks c blocks) (O ∪ groupValues c blocks q)).card : ℝ) ≤
          (N : ℝ) ^ ((c.1.val : ℝ) / 2 + η) := by
      intro q hq
      have hqG := ((PaperP1.EffectiveWindowLists.mem_lists G _ _ q).mp hq).1
      let Q := fun i ↦ rightBlocks c blocks i (q i)
      have hmerged := hNI c.1 N (hIn c.1) (Fin.append old q) (Fin.append oldBlocks Q)
        G (leftBlocks c blocks)
        (fun i x hx v hv ↦ hvalues _ x hx v hv)
        (append_all old q oldBlocks Q (fun _ v ↦ a * N ≤ v ∧ (v : ℝ) ≤ b * N) holdValues
          (fun i v hv ↦ hvalues _ (q i) (hqG i) v hv))
        (fun i x hx v hv ↦ hdist _ x hx v hv)
        (append_all old q oldBlocks Q (fun x v ↦ (((v : ℤ) - x).natAbs : ℝ) ≤ E * Real.log N) holdDist
          (fun i v hv ↦ hdist _ (q i) (hqG i) v hv))
      simpa only [biUnion_append, O, Q, groupValues] using hmerged
    have hgroup := hNE c.1 N (hEn c.1) old G (rightBlocks c blocks) oldBlocks
      (fun i x hx v hv ↦ hvalues _ x hx v hv) holdValues
      (fun i x hx v hv ↦ hdist _ x hx v hv) holdDist
    have hraw := PaperP1.RelativeBlockRelations.cell_count G blocks O c _ hB
    have hsum : (c.1.val : ℝ) + ((r + 1 - c.1.val : ℕ) : ℝ) = ((r + 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.add_sub_of_le c.1.isLt.le
    calc
      _ ≤ (N : ℝ) ^ (((r + 1 - c.1.val : ℕ) : ℝ) / 2 + η) * (N : ℝ) ^ ((c.1.val : ℝ) / 2 + η) :=
        hraw.trans (mul_le_mul_of_nonneg_right hgroup (Real.rpow_nonneg hn.le _))
      _ = _ := by
        rw [← Real.rpow_add hn]
        congr 1
        dsimp [p, η]
        nlinarith only [hsum]
  have hcover := PaperP1.FiniteCoverCount.cardinal_le
    (PaperP1.RelativeBlockRelations.population G blocks O) (univ : Finset (Code (r + 1)))
    (PaperP1.RelativeBlockRelations.cell G blocks O) ((N : ℝ) ^ (p + ε / 2))
    (PaperP1.RelativeBlockRelations.population_cover G blocks O) (fun c _ ↦ hcell c)
  calc
    _ ≤ (Fintype.card (Code (r + 1)) : ℝ) * (N : ℝ) ^ (p + ε / 2) := by simpa only [card_univ] using hcover
    _ ≤ (N : ℝ) ^ ((p + ε / 2) + ε / 2) := hNF N (by omega)
    _ = _ := by congr 1; dsimp [p]; ring

theorem uniform_count (r s : ℕ) (a b E ε : ℝ) (ha : 0 < a) (hE : 0 ≤ E) (hε : 0 < ε) :
    UniformCount r s a b E ε := by
  have hall : ∀ r : ℕ, ∀ s : ℕ, ∀ ε : ℝ, 0 < ε → UniformCount r s a b E ε := by
    intro r
    induction r using Nat.strong_induction_on with
    | h r ih =>
      cases r with
      | zero => exact fun s ε hε ↦ zero_count s a b E ε hε
      | succ r => exact induction_step r a b E ha hE ih
  exact hall r s ε hε

end PaperP1.RelativeBlockRelationsCount
