module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.WeakVoteContinuationPreparedV4
public import DecoupledConsensusProofs.Execution.VoteSafetyPreparedV4Adapter

@[expose] public section

/-! # Public vote safety from the prepared V4 continuation -/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Statements

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The prepared V4 continuation closes the public vote-safety field without
proof-layer pins. -/
theorem voteSafety (S : Setup V) : VoteSafetyAfterRecovery S :=
  voteSafety_of_weakContinuation_of_pins S
    (fun extra hdelay gap =>
      ⟨progressLag' gap extra, progressLag'_pos gap,
        fun rho rGST adm hcom hbelow hpost hrec =>
          weakVoteContinuation_preparedV4
            S (rho := rho) adm hcom hbelow (rGST := rGST) (gap := gap)
              (delayExtra := extra) hdelay hpost hrec⟩)

#print axioms voteSafety

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
