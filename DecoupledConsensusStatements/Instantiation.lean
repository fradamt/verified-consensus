module
public import DecoupledConsensusStatements.Generic.Claims
public import DecoupledConsensusModel.Execution.Instance
public import DecoupledConsensusModel.Execution.Setup
public import DecoupledConsensusModel.Protocol.Evidence
public import DecoupledConsensusStatements.Instantiation.RoundTimes
public import DecoupledConsensusStatements.Instantiation.Deadlines
public import DecoupledConsensusStatements.Instantiation.Certificates
public import DecoupledConsensusStatements.Instantiation.OutageWindow
public import DecoupledConsensusStatements.Instantiation.Proposals

@[expose] public section

/-!
# Selected protocol instantiation

Purpose: fill the generic review contract with the selected protocol's
execution specification, observations, timing constants, and evidence.
An auditor checks every field against the protocol model and the timing units
in `Generic.Constants`.

Defines: `actionRound`, `env`, `interface`, `constants`, and `Consensus`.
Read after: the generic statement files and the model execution interface.
Read next: the proof bridge and the concrete witnesses.
-/

namespace DecoupledConsensusModel.Statements.Instantiation

open DecoupledConsensusModel
open DecoupledConsensusModel.Execution DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Round `r` owns the half-open action window `[a_r, a_{r+1})`.

Times below `a_0` clamp to round `0`. The public environment uses this value
only through `env.awake`. -/
def actionRound (S : Setup V) (t : Time) : Round :=
  if t < S.a 0 then 0
  else Int.toNat ((t - 6 * S.E.Δ) / (S.a 1 - S.a 0))

def env (S : Setup V) : Generic.Env V where
  Δ := S.E.Δ
  Δ_pos := S.E.Δ_pos
  t_GST := S.E.t_GST
  t_GST_nonneg := S.E.t_GST_nonneg
  electorate := S.E.electorate
  awake := fun v t => (S.node v).awake (actionRound S t)

def interface (S : Setup V) :
    Generic.Interface (DecoupledConsensusModel.Execution.spec S) where
  confirmed := fun n => Protocol.get_confirmed n.st.core
  stable := fun n => Protocol.get_stable n.st.core
  finalized := fun n => n.st.core.F
  proposer := S.E.proposer
  proposalTime := Protocol.proposal_time S.E
  /- The block the proposal duty produces for slot `s` on the prepared read;
  total; the duty's output. -/
  proposedBlock := fun rho s =>
    (proposedBlockAt S rho s).map NamedBlock.erase
  opening := fun s => ∃ r : Round, s = S.hc.opening_slot r
  committee := fun s => S.E.committee s
  Certificate := NamedBlock V
  finalizes := fun c T => ∃ h, NamedFinalizedAt S.E S.cfg c T h
  collisionFree := fun c c' => RootInjectiveOnAncestors c.erase c'.erase
  evidence := fun c c' =>
    HasSlashableWeightBetween S.E (chain_attestations c.erase)
      (chain_attestations c'.erase)
  slashable := fun n n' =>
    HasSlashableWeightBetween S.E (store_attestations n.st.core)
      (store_attestations n'.st.core)
  inRun := fun rho c => NamedRun.blockInRun S rho c
  idealization := NamedRootCollisionFree S
  /- Two reads of the run, at any nodes and any times, hold evidence
  attributable to `v`; the evidence-holding nodes need not be honest. -/
  slashes := fun rho v =>
    ∃ (u u' : V) (t t' : Time),
      SlashableBetween
        (store_attestations (Run.storeAt S rho u t).core)
        (store_attestations (Run.storeAt S rho u' t').core) v

/-- `period` is one SG round: `R` slots of `4Δ`, i.e. `S.a 1 − S.a 0 = 4ΔR`;
`participationLag` is one round and `participationWindow` is `η_SG` rounds;
`growthDelay` and `stableGrowthDelay` are the exact inclusion-to-liveness
corollary delays `gap · period + confirmationDelay` and
`gap · period + stableInclusionDelay`. -/
noncomputable def constants (S : Setup V) : Generic.Constants where
  period := S.a 1 - S.a 0
  participationWindow := (S.hc.η_SG : Time) * (S.a 1 - S.a 0)
  participationLag := S.a 1 - S.a 0
  proposerSlots := 3
  prefixEnd := fun t₀ gap => S.a
    (recoveryRound S t₀ gap (S.cfg.timeoutDelay / S.hc.R - 2))
  recoveryEnd := fun t₀ gap =>
    healingBoundaryTime S
      (recoveryRound S t₀ gap (S.cfg.timeoutDelay / S.hc.R - 2))
  maxGap := S.cfg.K
  confirmationDelay := 6 * S.E.Δ
  growthDelay := fun gap =>
    (gap : Time) * (S.a 1 - S.a 0) + 6 * S.E.Δ
  stableGrowthDelay := fun gap =>
    (gap : Time) * (S.a 1 - S.a 0) +
      (6 * S.E.Δ + ((1 + S.hc.η_SG : Nat) * (S.a 1 - S.a 0) + 2 * S.E.Δ))
  stableInclusionDelay :=
    6 * S.E.Δ + ((1 + S.hc.η_SG : Nat) * (S.a 1 - S.a 0) + 2 * S.E.Δ)
  finalityStartup := fun gap =>
    healingBoundaryTime S
        (DecoupledConsensusModel.Statements.Instantiation.finalityStartup S gap
          (S.cfg.timeoutDelay / S.hc.R - 2) + 1) - S.a 0
  finalityDeadline := fun gap =>
    healingBoundaryTime S
        (DecoupledConsensusModel.Statements.Instantiation.finalityDeadline S gap
          (S.cfg.timeoutDelay / S.hc.R - 2) + 1) - S.a 0 +
      3 * S.E.Δ
  outageStart := fun T =>
    Statements.Instantiation.nextAction S T + (S.a 1 - S.a 0) + S.E.Δ
  expiry := fun T =>
    DecoupledConsensusModel.Protocol.early S.E S.hc
      (S.hc.round_of (S.E.slotOf (Statements.Instantiation.nextAction S T)) +
        S.hc.η_SG + 1) .g2

/-- The proposition that the selected protocol satisfies the generic consensus
bundle. Its proof is `Proofs.concreteConsensus` in the proof library. -/
def Consensus (S : Setup V) : Prop :=
  Generic.Consensus (DecoupledConsensusModel.Execution.spec S) (env S)
    (interface S) (constants S)

end DecoupledConsensusModel.Statements.Instantiation

end
