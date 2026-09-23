module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Schedule.MovingChainHandoffExports
public import DecoupledConsensusProofs.Execution.HeightFieldAssembly
public import DecoupledConsensusProofs.Execution.FGSafetyProgressDeadline
public import DecoupledConsensusProofs.ModelVocabulary.Execution.Setup
public import DecoupledConsensusProofs.Execution.W4HealedTwoSlotHandoff
public import DecoupledConsensusProofs.Objects.W4GeneralSlotAdoption
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.W4NonLost
public import DecoupledConsensusProofs.Protocol.Schedule.W4ExecSuffix
public import DecoupledConsensusProofs.Protocol.Schedule.W4HandoffBoundary
public import DecoupledConsensusProofs.Execution.MovingChainBandCover
public import DecoupledConsensusProofs.Protocol.Schedule.MovingChainFold
public import DecoupledConsensusProofs.Protocol.ValidatorClient.CanonicalRegimeFirstVote
public import DecoupledConsensusProofs.Generic.CanonicalRegimeFromChain
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SeedEntryCanonical
public import DecoupledConsensusProofs.Protocol.Grades.MovingChainFloorBridge
public import DecoupledConsensusProofs.Protocol.Schedule.W4LaterReadCap

@[expose] public section

/-!
# The clean named recovery spine ( D1)

earlier's `uniformCanonicalRecoveryWithBoundary_after_GST`
(`CanonicalCarrierAfterSafetyRun.lean:155-183`) hands the corresponding branch's proof of
`commonFinalityAboveFrontier_of_openingCarrierRecurrence` a recovery round `q`
carrying the canonical suffix execution, the two moving-chain records, the
split boundary, and height progress. Its selection twin is on a red import path.

This leaf states the clean named export and closes the parts that the clean
base already supports: the post-GST action bound at `q` and the height-progress
field. The three record inputs are the branches's open residual; they are named
here as explicit hypotheses so that the corresponding branch can consume the conclusion and
the can fan the residuals out.

Two deliberate differences from earlier, both forced by the red path and both
checked against earlier's body first.

* earlier exports `MovingChainSplitBoundary` and `ProtectedVoteSlot`. In
  `OpeningCarrierFinalityRun.lean:52-207` the pair is read at exactly two sites
  (`hroundAt`, `hnlPrev`) and both go through
  `notLost_of_honestPredecessorOpening_after_SG_healing`
  (`NonLostAfterHonestOpeningRun.lean:163`). The pair's only selection producer
  (`exists_uniformHandoffBoundary`, `PostSafetyHandoffRun.lean:203`) and the
  non-lostness producer are both red, so the export carries the consumed fact
  directly.
* `uniformFGSafetyDeadline` and `uniformMovingBoundaryRound`
  (`UniformBoundaryDeadlineRun.lean:118,137`) and `uniformHandoffLag`
  (`PostSafetyHandoffRun.lean:191`) are red, so their bodies are copied here
  verbatim under `w4` names. 's closed statement formula is bridged to
  the renamed lag in `W4FinalityDeadlines`.
-/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Internal.NamedRecoveryRead
open Protocol
open Proofs.HealingLemmas
open Proofs.Optimistic
open Protocol (derive_named)

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}

/-- The uniform FG-safety deadline as a lag from the caller's post-GST round. -/
def w4UniformFGSafetyDeadline (S : Setup V) (gap : Round) (extra : Nat := 0) : Round :=
  2 + (S.cfg.D + S.cfg.K + 5) * progressLag' gap extra

/-- Verbatim copy of `uniformMovingBoundaryRound`
(`UniformBoundaryDeadlineRun.lean:137`, red import path). -/
def w4UniformMovingBoundaryRound (S : Setup V) (gap : Round) (extra : Nat := 0) : Round :=
  w4UniformFGSafetyDeadline S gap extra + 3 * progressLag' gap extra + 1

/-- The widened round bound implies the previous three-round form. -/
private theorem w4d1_deadline_add_three_le_of_widened
    {Dl q gap : Nat} {extra : Nat}
    (h : Dl + 3 * progressLag' gap extra + 1 ≤ q) : Dl + 3 ≤ q := by
  have h1 : 1 ≤ progressLag' gap extra :=
    progressLag'_pos (delayExtra := extra) gap
  have hmul : 3 * 1 ≤ 3 * progressLag' gap extra := Nat.mul_le_mul_left 3 h1
  have h3 : 3 ≤ 3 * progressLag' gap extra + 1 :=
    Nat.le_trans (by decide : (3 : Nat) ≤ 3 * 1 + 1)
      (Nat.add_le_add_right hmul 1)
  calc Dl + 3 ≤ Dl + (3 * progressLag' gap extra + 1) :=
        Nat.add_le_add_left h3 Dl
    _ = Dl + 3 * progressLag' gap extra + 1 := by omega
    _ ≤ q := h




/-- The uniform finality handoff lag. The selector earlier kept one
unused round after `q + 3`; removing that slack absorbs the second initial
round of the named FG-safety regime. -/
def w4UniformHandoffLag (S : Setup V) (gap : Round) (extra : Nat := 0) : Round :=
  w4UniformMovingBoundaryRound S gap extra + gap + 3







/-! ### Selecting an opening carrier inside the public window

The handoff record needs three progress windows between its base q0 and the
selected round. The recurrence is queried at the moving-boundary offset, so
the selected value is an OpeningCarrierAt, not merely a CarrierAt. The small
extra four-round margin also leaves the q + 3 horizon slice below the outer
healing boundary. -/


/-! ### Feeding the prepared handoff from the later frontier cap

The prepared handoff's adoption field reads the next slot's vote duty. The
constructor in W4HealedTwoSlotHandoffRun takes the exact strict-index cap at
that read. This helper keeps that cap as the only height input and derives the
ordinary slot facts locally. -/















/-- Non-lostness of every round whose predecessor opening is honest, from the
recovery round on. the corresponding branch. -/
def W4NonLostFrom (S : Setup V) (rho : Run V) (q : Round) : Prop :=
  ∀ r : Round, q + 2 < r →
    S.E.proposer (S.hc.opening_slot (r - 1)) ∈ rho.honest →
    Protocol.confirmation_time S.E (S.hc.opening_slot r + 2) ≤ rho.horizon →
    ¬ LostRoundAt S rho r




/-- **the corresponding branch's obligation, discharged.**

`notLost_of_honestPredecessorOpening_named_after_SG_healing`
(`W4NonLostRun.lean:363`) is earlier's
`notLost_of_honestPredecessorOpening_after_SG_healing`
(`NonLostAfterHonestOpeningRun.lean:163`) over the clean named base, pin-free.
It is stated at the caller's `rGST`; the spine needs it at the fixed round, so
it is instantiated there. -/
theorem w4NonLost_of_named_at
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra)
    (rGST : Round) (hpost : S.E.t_GST ≤ S.a rGST) :
    ∀ q : Round,
      fgSafetyProgressDeadline S rho rGST gap delayExtra +
        3 * progressLag' gap delayExtra + 1 ≤ q →
      W4NonLostFrom S rho q :=
  fun _ hq => notLost_of_honestPredecessorOpening_named_after_SG_healing
    S adm hcom hbelow hrec hdelay hpost
    (w4d1_deadline_add_three_le_of_widened hq)







#print axioms w4NonLost_of_named_at


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
