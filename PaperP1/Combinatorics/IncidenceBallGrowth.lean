module

public import PaperP1.Algebra.ShortIncidenceRoutes

/-! # Actual incidence balls expand until they force a short kernel vector -/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.IncidenceBallGrowth

open Finset PaperP1.GreedyShortKernel PaperP1.LabelledEdgeCore PaperP1.ShortIncidenceRoutes

local instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

variable {V E : Type*}
local instance : DecidableEq V := Classical.decEq _
local instance : DecidableEq E := Classical.decEq _

def ball (f : (E →₀ ZMod 2) →ₗ[ZMod 2] (V → ZMod 2)) (S : Finset E)
    (U : Finset V) (root : V) (r : ℕ) : Finset V := by
  classical
  exact U.filter (fun v ↦ Route f S root v r)

theorem mem_ball (f : (E →₀ ZMod 2) →ₗ[ZMod 2] (V → ZMod 2)) (S : Finset E)
    (U : Finset V) (root v : V) (r : ℕ) :
    v ∈ ball f S U root r ↔ v ∈ U ∧ Route f S root v r := by
  classical
  exact mem_filter

theorem ball_subset (f : (E →₀ ZMod 2) →ₗ[ZMod 2] (V → ZMod 2)) (S : Finset E)
    (U : Finset V) (root : V) (r : ℕ) : ball f S U root r ⊆ U := by
  classical
  exact filter_subset _ _

theorem root_mem_ball (f : (E →₀ ZMod 2) →ₗ[ZMod 2] (V → ZMod 2)) (S : Finset E)
    (U : Finset V) (root : V) (r : ℕ) (hr : root ∈ U) : root ∈ ball f S U root r :=
  (mem_ball f S U root root r).mpr ⟨hr, route_self f S root r⟩

theorem no_short_mono (f : (E →₀ ZMod 2) →ₗ[ZMod 2] (V → ZMod 2))
    {S T : Finset E} {k ℓ : ℕ} (h : ¬ HasShortVector f T ℓ) (hST : S ⊆ T) (hk : k ≤ ℓ) :
    ¬ HasShortVector f S k := fun hs ↦ h (GreedyShortKernel.mono f hs hST hk)

theorem touching_subset_next_inside (f : (E →₀ ZMod 2) →ₗ[ZMod 2] (V → ZMod 2))
    (left right : E → V) (S : Finset E) (U : Finset V) (root : V) (r : ℕ)
    (hcol : ∀ e ∈ S, f (Finsupp.single e 1) = point (left e) + point (right e))
    (hends : ∀ e ∈ S, left e ∈ U ∧ right e ∈ U) :
    touching left right S (ball f S U root r) ⊆ inside left right S (ball f S U root (r + 1)) := by
  intro e he
  obtain ⟨heS, heB⟩ := (mem_touching left right S _ e).mp he
  obtain ⟨hel, her⟩ := hends e heS
  apply (mem_inside left right S _ e).mpr
  refine ⟨heS, ?_, ?_⟩
  · apply (mem_ball f S U root _ (r + 1)).mpr
    refine ⟨hel, ?_⟩
    rcases heB with hl | hr
    · exact route_mono f ((mem_ball f S U root _ r).mp hl).2 (subset_refl S) (by omega)
    · have hswap : f (Finsupp.single e 1) = point (right e) + point (left e) := by
        rw [hcol e heS, add_comm]
      exact route_step f S root (right e) (left e) r e heS hswap
        ((mem_ball f S U root _ r).mp hr).2
  · apply (mem_ball f S U root _ (r + 1)).mpr
    refine ⟨her, ?_⟩
    rcases heB with hl | hr
    · exact route_step f S root (left e) (right e) r e heS (hcol e heS)
        ((mem_ball f S U root _ r).mp hl).2
    · exact route_mono f ((mem_ball f S U root _ r).mp hr).2 (subset_refl S) (by omega)

theorem ball_growth (f : (E →₀ ZMod 2) →ₗ[ZMod 2] (V → ZMod 2))
    (left right : E → V) (S : Finset E) (U : Finset V) (root : V) (r t : ℕ)
    (hcol : ∀ e ∈ S, f (Finsupp.single e 1) = point (left e) + point (right e))
    (hends : ∀ e ∈ S, left e ∈ U ∧ right e ∈ U)
    (hmin : ∀ v ∈ U, t ≤ (incident left right S v).card)
    (hno : ¬ HasShortVector f S (2 * (r + 1) + 1)) :
    t * (ball f S U root r).card ≤ 2 * (ball f S U root (r + 1)).card := by
  have hsum : t * (ball f S U root r).card ≤
      ∑ v ∈ ball f S U root r, (incident left right S v).card := by
    calc
      t * (ball f S U root r).card = ∑ _v ∈ ball f S U root r, t := by simp [Nat.mul_comm]
      _ ≤ _ := sum_le_sum (fun v hv ↦ hmin v (ball_subset f S U root r hv))
  have htouch := incident_sum_le left right S (ball f S U root r)
  have hsubset := touching_subset_next_inside f left right S U root r hcol hends
  have hrank := inside_card_le_routes f left right S (ball f S U root (r + 1)) root
    (r + 1) hcol hno (fun v hv ↦ ((mem_ball f S U root v (r + 1)).mp hv).2)
  exact hsum.trans (htouch.trans (Nat.mul_le_mul_left 2 ((card_le_card hsubset).trans hrank)))

theorem ball_geometric (f : (E →₀ ZMod 2) →ₗ[ZMod 2] (V → ZMod 2))
    (left right : E → V) (S : Finset E) (U : Finset V) (root : V) (r d : ℕ)
    (hroot : root ∈ U)
    (hcol : ∀ e ∈ S, f (Finsupp.single e 1) = point (left e) + point (right e))
    (hends : ∀ e ∈ S, left e ∈ U ∧ right e ∈ U)
    (hmin : ∀ v ∈ U, 2 * d ≤ (incident left right S v).card)
    (hno : ¬ HasShortVector f S (2 * r + 1)) : d ^ r ≤ (ball f S U root r).card := by
  induction r with
  | zero =>
    have hc := card_pos.mpr ⟨root, root_mem_ball f S U root 0 hroot⟩
    simp only [pow_zero]
    omega
  | succ r ih =>
    have hi := ih (no_short_mono f hno (subset_refl S) (by omega))
    have hg := ball_growth f left right S U root r (2 * d) hcol hends hmin hno
    have hg' : d * (ball f S U root r).card ≤ (ball f S U root (r + 1)).card := by
      rw [Nat.mul_assoc] at hg
      omega
    rw [pow_succ, Nat.mul_comm]
    exact (Nat.mul_le_mul_left d hi).trans hg'

theorem core_short_vector (f : (E →₀ ZMod 2) →ₗ[ZMod 2] (V → ZMod 2))
    (left right : E → V) (S : Finset E) (U : Finset V) (r d : ℕ) (hU : U.Nonempty)
    (hcol : ∀ e ∈ S, f (Finsupp.single e 1) = point (left e) + point (right e))
    (hends : ∀ e ∈ S, left e ∈ U ∧ right e ∈ U)
    (hmin : ∀ v ∈ U, 2 * d ≤ (incident left right S v).card)
    (hpow : U.card < d ^ r) : HasShortVector f S (2 * r + 1) := by
  by_contra hno
  obtain ⟨root, hr⟩ := hU
  have hg := ball_geometric f left right S U root r d hr hcol hends hmin hno
  have hc := card_le_card (ball_subset f S U root r)
  omega

theorem dense_short_vector [Fintype V] (f : (E →₀ ZMod 2) →ₗ[ZMod 2] (V → ZMod 2))
    (left right : E → V) (S : Finset E) (r d : ℕ)
    (hcol : ∀ e ∈ S, f (Finsupp.single e 1) = point (left e) + point (right e))
    (hdense : (2 * d) * Fintype.card V < S.card) (hpow : Fintype.card V < d ^ r) :
    HasShortVector f S (2 * r + 1) := by
  obtain ⟨U, hU, _he, hmin⟩ := finite_dense_core left right S (2 * d) hdense
  have hsub := inside_subset left right S U
  have hc : U.card ≤ Fintype.card V := card_le_univ U
  have hs := core_short_vector f left right (inside left right S U) U r d hU
    (fun e he ↦ hcol e (hsub he))
    (fun e he ↦ ((mem_inside left right S U e).mp he).2) hmin (hc.trans_lt hpow)
  exact GreedyShortKernel.mono f hs hsub (le_refl _)

end PaperP1.IncidenceBallGrowth
