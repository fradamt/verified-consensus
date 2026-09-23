module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.RoundZero
public import DecoupledConsensusProofs.Protocol.Grades.Ladder
public import DecoupledConsensusProofs.Generic.PrefixFGSelectorWitness
public import DecoupledConsensusProofs.Protocol.Grades.RecoveryGenuineClearNextVote
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.HeightRegimeFrameBase
public import DecoupledConsensusProofs.Protocol.Grades.VoterAnchorSourceInputs
public import DecoupledConsensusProofs.Protocol.Grades.WeakGenesis

@[expose] public section

/-!
# Exact finite-prefix FG-selector cone seed

This module carries the selector witness in the named runtime. The two
constructors that need the genuine-clear next-vote producer remain blocked in
`RecoveryGenuineClearNextVoteRun`.
-/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Internal.PhaseGrades
open Internal.NamedRecoveryRead
open DecoupledConsensusModel.Protocol
open Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

theorem strictEventIndex_le_tickIndex
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    {i : Nat} {v : V} {t : Time}
    (hi : rho.events[i]? = some (Event.tick v t)) :
    strictEventIndex rho t ≤ i := by
  by_contra hnot
  have hlt : i < strictEventIndex rho t := Nat.lt_of_not_ge hnot
  unfold strictEventIndex at hlt
  have hmem : Event.tick v t ∈
      rho.events.filter (fun e => decide (e.time < t)) := by
    rw [Proofs.Optimistic.filter_eq_take S sch _ (Proofs.Optimistic.downward_lt t)]
    exact List.mem_of_getElem? (by
      rw [List.getElem?_take_of_lt hlt]
      exact hi)
  have himpossible := (List.mem_filter.mp hmem).2
  simp only [decide_eq_true_eq, Event.time] at himpossible
  exact lt_irrefl t himpossible

/-! ## Named prefix witness -/

structure PrefixFGSelectorConeAt
    (S : Setup V) (rho : Run V) (start stop : Nat) (blocked : Height)
    (index : Nat) (attestation : NamedAttestation V) (actionTime : Time)
    (selectedBlock : NamedBlock V) (checkpoint : Block V) : Prop where
  startLeIndex : start ≤ index
  indexLtStop : index < stop
  signerHonest : attestation.val_index ∈ rho.honest
  exactTick : rho.events[index]? =
    some (Event.tick attestation.val_index actionTime)
  tickOutput : Object.attest attestation ∈
    NamedRun.emittedAt S rho index attestation.val_index actionTime
  emitted : NamedRun.emits S rho attestation.val_index
    (Object.attest attestation) actionTime
  actionTime_eq : actionTime = S.a attestation.round
  exactAction : attestation =
    actionAttestationAt S rho attestation.val_index attestation.round
  exactFGSource : actionFGSource S
      (actionStoreAt S rho attestation.val_index attestation.round) =
      some selectedBlock.erase
  sourceMem : selectedBlock ∈
    (actionStoreAt S rho attestation.val_index attestation.round).st.bodies
  sourceStoredHeight :
    ((actionStoreAt S rho attestation.val_index attestation.round).st.core.σ
      selectedBlock.erase).h = blocked + 1
  sourceDerivedHeight :
    (Protocol.derive_named S.E S.cfg selectedBlock).h = blocked + 1
  checkpointStored : checkpoint =
    ((actionStoreAt S rho attestation.val_index attestation.round).st.core.σ
      selectedBlock.erase).T_h
  checkpointDerived : checkpoint =
    (Protocol.derive_named S.E S.cfg selectedBlock).T_h
  targetOrTimeout :
    attestation.height_pair.erase = HeightPair.target (blocked + 1) checkpoint.root ∨
      attestation.height_pair.erase = HeightPair.timeout (blocked + 1)
  cone :
    NamedHonestVotesCone S rho (S.hc.opening_slot attestation.round)
      (fun X => Block.Preceq selectedBlock.erase X) ∨
    NamedHonestVotesCone S rho (S.hc.opening_slot attestation.round + 1)
      (fun X => Block.Preceq selectedBlock.erase X)

theorem PrefixFGSelectorConeAt.actionPrefix_lt
    {S : Setup V} {rho : Run V} (sch : ScheduleWellFormed S rho)
    {start stop : Nat} {blocked : Height} {i : Nat}
    {a : NamedAttestation V} {ta : Time} {Cfg : NamedBlock V} {T : Block V}
    (hseed : PrefixFGSelectorConeAt S rho start stop blocked i a ta Cfg T) :
    strictEventIndex rho (S.a a.round) < stop := by
  have hle := strictEventIndex_le_tickIndex S sch hseed.exactTick
  rw [hseed.actionTime_eq] at hle
  exact hle.trans_lt hseed.indexLtStop

theorem PrefixFGSelectorConeAt.actionHorizon
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    {start stop : Nat} {blocked : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg : NamedBlock V} {T : Block V}
    (hseed : PrefixFGSelectorConeAt S rho start stop blocked i a ta Cfg T) :
    S.a a.round ≤ rho.horizon := by
  have h := (adm.in_horizon (Event.tick a.val_index ta)
    (List.mem_of_getElem? hseed.exactTick)).2
  simpa only [Event.time, hseed.actionTime_eq] using h

#print axioms PrefixFGSelectorConeAt.actionPrefix_lt
#print axioms PrefixFGSelectorConeAt.actionHorizon

























end HealingSurface
end Proofs
end DecoupledConsensusModel

end
