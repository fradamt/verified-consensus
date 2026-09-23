module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusModel.Protocol.Grades
public import DecoupledConsensusInternal.Legacy.Assumptions.AwakeWindow

@[expose] public section

/-! Pure core-store and arithmetic helpers retained in the default library.
the prior runtime statements and proofs are in the compatibility layer. -/


namespace DecoupledConsensusModel
namespace Internal.OutageResilience
open Execution
variable {V : Type} [DecidableEq V] [Fintype V]

/-- Addendum A: the shifted G2 early cutoff. -/
def earlyG2 (S : Setup V) (r : Round) : Time :=
  DecoupledConsensusModel.Protocol.early S.E S.hc r .g2

/-- Spec §6: concrete head lookup and prefix relation at entry. -/
def InputCovers (st : Protocol.Store V) (u : Protocol.SGVote V) (P : Block V) : Prop :=
  ∃ B ∈ st.T, u.confirmed = some B.root ∧ Block.Preceq P B


/-- 1142: best processed state height on the P-descendant side.
The finite supremum is zero if there is no processed P descendant. -/
def bestPrefixHeight (st : Protocol.Store V) (P : Block V) : Height :=
  (st.T.filter (fun B => Block.preceq P B = true)).sup (fun B => (st.σ B).h)


/-- 1142: elapsed time since entry at the rival's current height.
The entry block T_h determines its slot. Age is measured at the outage cut. -/
def rivalEntryAge (S : Setup V) (st : Protocol.Store V) (b0 : Time) (B : Block V) : Time :=
  max 0 (b0 - slotStart S.E.Δ (st.σ B).T_h.slot)


/-- 1142 supersedes 1135: concrete stage-1c candidate, in time units.
timeoutDelay is in slots and one slot is 4Δ. Sufficiency is UNPROVED: stage
1c must prove this candidate or replace it with another concrete definition. -/
def timeoutEnvelopeCandidate (S : Setup V) (b0 A : Time) : Time :=
  b0 + (S.cfg.timeoutDelay : Time) * (4 * S.E.Δ) - A - S.E.Δ

end Internal.OutageResilience
end DecoupledConsensusModel

end
