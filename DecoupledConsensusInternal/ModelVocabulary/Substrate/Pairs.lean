module
public import DecoupledConsensusModel

@[expose] public section

/-!
# §4 Height and finality pairs

The two derived pairs of a combined attestation (PROTOCOL.md `sec:state-machine`). They
live in the substrate because `Block` carries attestations and must be defined
once, with all of its fields.

The height pair has three wire cases, so an empty pair cannot be confused with a
timeout at height zero. Copied and trimmed from `decoupled-consensus-full`'s
`Protocol/Messages/Model.lean`; targets are `BlockId` and there is no signature
wrapper. E1, E2 and the equivocation predicates are **not** here — they belong
to the §4 module.
-/

namespace DecoupledConsensusModel

namespace HeightPair

/-- §4 `a.height`, `⊥` for the empty pair (PROTOCOL.md `sec:state-machine`). -/
def height? : HeightPair → Option Height
  | .empty => none
  | .timeout height => some height
  | .target height _ => some height

end HeightPair

end DecoupledConsensusModel

end
