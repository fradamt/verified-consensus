module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.GradePersistence

@[expose] public section

/-!
# Common-grade tree persistence to a later read

`NamedGradeFormsAt` gives filtered-tree membership at the G2-domain read. This
leaf removes the filter and carries the resulting processed-tree membership
to any later strict pre-time read.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]

/-- A block supplied by `NamedGradeFormsAt` remains processed at every later
strict pre-time read of an honest reader. -/
theorem gradeFormsAt_processedAtRead_of_action_le
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q : Round} {P : Block V}
    (hforms : NamedGradeFormsAt S rho q P)
    {reader : V} (hreader : reader ∈ rho.honest) {read : Time}
    (hle : S.a q ≤ read) :
    P ∈ (rho.storeBeforeTime S reader read).T := by
  exact namedGradeFormsAt_processedAtRead_of_action_le
    S adm hforms hreader hle


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
