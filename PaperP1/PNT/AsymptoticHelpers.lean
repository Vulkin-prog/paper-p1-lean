module

public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Topology.Order.Compact
public import Mathlib.Analysis.Normed.Group.Bounded

/-!
Adapted from AlexKontorovich/PrimeNumberTheoremAnd, PrimeNumberTheoremAnd/Mathlib/Analysis/Asymptotics/Asymptotics.lean,
commit 127b50e33f6033e2147921167a117af96d9ba4ea, Git blob dc51688f7332e0caf3bd4d1b50c1d0052d304103,
Apache-2.0. Scope: the three constant-versus-identity estimates; obsolete cast helpers omitted.
Changes: P1 namespaces and Lean 4.36 module/public declarations.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace PaperP1.PNT.AsymptoticHelpers

open Filter Topology Asymptotics

variable {α : Type*} {β : Type*} {E : Type*} {F : Type*} {G : Type*} {E' : Type*}
  {F' : Type*} {G' : Type*} {E'' : Type*} {F'' : Type*} {G'' : Type*} {R : Type*}
  {R' : Type*} {𝕜 : Type*} {𝕜' : Type*}

variable [Norm E] [Norm F] [Norm G]

variable [SeminormedAddCommGroup E'] [SeminormedAddCommGroup F'] [SeminormedAddCommGroup G']
  [NormedAddCommGroup E''] [NormedAddCommGroup F''] [NormedAddCommGroup G''] [SeminormedRing R]
  [SeminormedRing R']


theorem isLittleO_const_id_cocompact [ProperSpace F'']
    (c : E'') : (fun _x : F'' => c) =o[cocompact F''] id :=
  isLittleO_const_left.2 <| Or.inr tendsto_norm_cocompact_atTop

-- to replace existing `isLittleO_const_id_atTop`
theorem isLittleO_const_id_atTop2 [LinearOrder F''] [NoMaxOrder F''] [ClosedIciTopology F'']
    [ProperSpace F''] (c : E'') : (fun _x : F'' => c) =o[atTop] id :=
 (isLittleO_const_id_cocompact c).mono atTop_le_cocompact

-- to replace existing `isLittleO_const_id_atBot`
theorem isLittleO_const_id_atBot2 [LinearOrder F''] [NoMinOrder F''] [ClosedIicTopology F'']
    [ProperSpace F''] (c : E'') : (fun _x : F'' => c) =o[atBot] id :=
  (isLittleO_const_id_cocompact c).mono atBot_le_cocompact

end PaperP1.PNT.AsymptoticHelpers
