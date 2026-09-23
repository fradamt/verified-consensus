module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.CanonicalSuffix
public import DecoupledConsensusInternal.Safety
public import DecoupledConsensusInternal.Definitions.NamedEvidence

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Finality from one finite honest-proposer window

The witness records the honest proposal, its finalized checkpoint, the source
and deadline times, and the common honest-store result. The window condition
gives one advance per occurrence. It does not assert recurring opportunities.
-/

namespace DecoupledConsensusModel
namespace Internal

open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- An honest proposal supplies a common finalized checkpoint at or above H.
The source and deadline bounds retain the exact proposal provenance. The
proposal is the named duty's block (its existence is concluded), the
checkpoint is a named run block, and both heights are read through the
named derivation. -/
def CommonFinalizedWitnessAt
    (S : Setup V) (rho : Run V)
    (q source endRound : Round) (H : Height) : Prop :=
  ∃ (slot : Slot) (B checkpoint : NamedBlock V) (height : Height),
    0 < slot ∧
      healingBoundaryTime S q < Protocol.proposal_time S.E slot ∧
      S.E.proposer slot ∈ rho.honest ∧
      Statements.Instantiation.proposedBlockAt S rho slot = some B ∧
      NamedRun.blockInRun S rho checkpoint ∧
      NamedFinalizedAt S.E S.cfg B checkpoint.erase height ∧
      H ≤ height ∧
      (Protocol.derive_named S.E S.cfg checkpoint).h = height ∧
      checkpoint.erase ≠ Block.genesis ∧
      S.a source ≤ Protocol.proposal_time S.E slot ∧
      S.a source ≤ Protocol.confirmation_time S.E slot ∧
      Protocol.confirmation_time S.E slot ≤ S.a endRound ∧
      ∀ v ∈ rho.honest,
        Block.Preceq checkpoint.erase
            (rho.storeAt S v (Protocol.confirmation_time S.E slot)).F ∧
          height ≤ (rho.storeAt S v
            (Protocol.confirmation_time S.E slot)).core.finalized_height

/-- One finite honest-slot interval gives one strict common finality advance.
The configuration and horizon guards are internal. The recovery round q and
progress lag L come from the surrounding statement, not a second seed choice.
This is one advance per occurrence, not a recurring-finality assertion. -/
def HonestWindowFinalityFrom
    (S : Setup V) (rho : Run V) (q L : Round) : Prop :=
  3 ≤ S.cfg.K →
    ∀ start : Round, q + 2 ≤ start →
      (∀ s : Slot, S.hc.opening_slot start ≤ s →
        s ≤ S.hc.opening_slot (start + 4 * L + 9) + 2 →
        S.E.proposer s ∈ rho.honest) →
      S.a (start + (4 * L + 11)) ≤ rho.horizon →
      ∃ H : Height, honestHMaxAt S rho (S.a start) < H ∧
        CommonFinalizedWitnessAt S rho q start (start + (4 * L + 11)) H

end Internal
end DecoupledConsensusModel

end
