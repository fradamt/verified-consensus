module
public import DecoupledConsensusInternal.ModelVocabulary
public import DecoupledConsensusInternal.Legacy.Definitions.NamedHeadReads
public import DecoupledConsensusInternal.Definitions.NamedDutyReads

@[expose] public section

/-!
# Named proposal-pivot views and suffix transfer 

Named twins of `proposalWalkSourceTree/Score/Eligible`,
`proposalWalkTargetTree/Score/Eligible` and `ProposalPivotSuffixTransfer`
(Availability/ProposalPivotRun.lean:462-540). The source views read the
proposer's prepared duty read; the target views read the voter's prepared
duty read; the target tree removes the bound named proposal `P`, never a
recomputed total block. The score and eligibility functions are the
profile-independent Goldfish functions on the read's core store; only the
reads and the removed block change. The parent is `proposedParent` (the
shared input's parent field on the proposer's read).
-/


namespace DecoupledConsensusModel.Proofs.HealingSurface
open DecoupledConsensusModel.Internal DecoupledConsensusModel.Execution
  DecoupledConsensusModel.Internal.NamedRecoveryRead
variable {V : Type} [DecidableEq V] [Fintype V]

/-- Source tree: the proposer's filtered tree at its prepared read. -/
def namedWalkSourceTree (S : Setup V) (rho : Run V) (s : Slot) : Finset (Block V) :=
  Protocol.get_filtered_block_tree (proposalDutyRead S rho s).st.core.toHealing.toFG

def namedWalkSourceScore (S : Setup V) (rho : Run V) (s : Slot) : Block V → Nat :=
  let duty := (proposalDutyRead S rho s).st.core
  Protocol.goldfish_score S.E duty.T
    (Protocol.proposer_view duty.toHealing.toFG.toSG.toGoldfishStore duty.s).toFinset
    (Protocol.proposer_support_view duty.toHealing.toFG.toSG.toGoldfishStore duty.s).toFinset
    (duty.s - 1)

def namedWalkSourceEligible (S : Setup V) (rho : Run V) (s : Slot) : Block V → Bool :=
  let duty := (proposalDutyRead S rho s).st.core
  Protocol.goldfish_eligible S.E duty.σ duty.h_max duty.T duty.s
    (Protocol.proposer_view duty.toHealing.toFG.toSG.toGoldfishStore duty.s).toFinset
    (Protocol.proposer_support_view duty.toHealing.toFG.toSG.toGoldfishStore duty.s).toFinset
    (duty.s - 1)

/-- Target tree: the voter's frozen candidate tree at its prepared read,
with the bound proposal removed. -/
def namedWalkTargetTree (S : Setup V) (rho : Run V) (s : Slot) (v : V) (P : NamedBlock V) :
    Finset (Block V) :=
  let st := (voteDutyRead S rho v s).st.core
  (Protocol.voter_filtered_block_tree S.E st st.s).erase P.erase

def namedWalkTargetScore (S : Setup V) (rho : Run V) (s : Slot) (v : V) : Block V → Nat :=
  let duty := (voteDutyRead S rho v s).st.core
  Protocol.goldfish_score S.E duty.T
    (Protocol.voter_view S.E duty.toHealing.toFG.toSG.toGoldfishStore duty.s)
    (Protocol.voter_support_view S.E duty.toHealing.toFG.toSG.toGoldfishStore duty.s)
    (duty.s - 1)

def namedWalkTargetEligible (S : Setup V) (rho : Run V) (s : Slot) (v : V) : Block V → Bool :=
  let duty := (voteDutyRead S rho v s).st.core
  Protocol.goldfish_eligible S.E duty.σ duty.h_max duty.T duty.s
    (Protocol.voter_view S.E duty.toHealing.toFG.toSG.toGoldfishStore duty.s)
    (Protocol.voter_support_view S.E duty.toHealing.toFG.toSG.toGoldfishStore duty.s)
    (duty.s - 1)

/-- Replaces `ProposalPivotSuffixTransfer`, with the bound proposal `P`. -/
structure NamedProposalPivotSuffixTransfer (S : Setup V) (rho : Run V) (s : Slot) (E : Block V)
    (v : V) (P : NamedBlock V) : Prop where
  persist : ∀ X C : Block V,
    Block.Preceq E X →
    Block.Preceq X (proposedParent S rho s) →
    X ≠ proposedParent S rho s →
    Protocol.ghost_step (namedWalkSourceTree S rho s) (namedWalkSourceScore S rho s)
      (namedWalkSourceEligible S rho s) X = some C →
    Block.Preceq C (proposedParent S rho s) →
    C ∈ namedWalkTargetTree S rho s v P ∧ namedWalkTargetEligible S rho s v C = true
  reflect : ∀ X C : Block V,
    Block.Preceq E X →
    Block.Preceq X (proposedParent S rho s) →
    C ∈ namedWalkTargetTree S rho s v P →
    C.parent? = some X →
    namedWalkTargetEligible S rho s v C = true →
    C ∈ namedWalkSourceTree S rho s ∧ namedWalkSourceEligible S rho s C = true

end DecoupledConsensusModel.Proofs.HealingSurface

end
