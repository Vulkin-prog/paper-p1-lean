module

public import PaperP1.Diophantine.QuadraticOrderConductor

@[expose] public section

namespace PaperP1.PellInput

/-- Concrete discharge of the finite-colour conductor interface, using the
proved maximal-order embedding and residue descent. -/
theorem quadraticOrderConductorFiberBound :
    QuadraticOrderConductorFiberBoundStatement :=
  QuadraticOrderConductor.quadraticOrderConductorFiberBoundInternal

end PaperP1.PellInput

