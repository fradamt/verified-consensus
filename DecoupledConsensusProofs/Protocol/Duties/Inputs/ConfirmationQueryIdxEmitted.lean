module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.LayerAHistoryIndices
public import DecoupledConsensusInternal.Definitions.ActionSources

@[expose] public section

/-!
# Emission-backed index confirmation history

The original proof-layer provenance records a computed SG carrier at every
honest action tick, including a tick at which the validator is asleep. This
additive restatement records an SG carrier only when that action was emitted.
The live-confirmed arm is unchanged.
-/

namespace DecoupledConsensusModel.Internal.NamedOutageEntry.History

open Execution Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

def WitnessProvenanceIdxEmitted (S : Setup V) (rho : NamedRun V) (n : Nat)
    (C : NamedBlock V) : Prop :=
  C = .genesis ∨
    ∃ (i : Nat) (v : V) (r : Round), i ≤ n ∧ v ∈ rho.honest ∧
      rho.events[i]? = some (.tick v (S.a r)) ∧
      C ∈ (actionReadFrom S (NamedRun.stateBefore S rho i v) r).st.bodies ∧
      (C.erase = (actionReadFrom S
          (NamedRun.stateBefore S rho i v) r).st.core.live_confirmed ∨
        C.erase = Protocol.get_sg_vote_with
            (NamedProfile.gradeContract
              (actionReadFrom S
                (NamedRun.stateBefore S rho i v) r).cache)
            S.E S.hc
            (actionReadFrom S
              (NamedRun.stateBefore S rho i v) r).st.core.toHealing r
            (Protocol.grade2_block_with
              (NamedProfile.gradeContract
                (actionReadFrom S
                  (NamedRun.stateBefore S rho i v) r).cache)
              S.E S.hc
              (actionReadFrom S
                (NamedRun.stateBefore S rho i v) r).st.core.toHealing r) ∧
          NamedRun.emits S rho v
            (Object.attest (Proofs.HealingSurface.actionAttestationAt S rho v r))
            (S.a r))

def LayerAJointHistoryIdxEmitted (S : Setup V) (rho : NamedRun V) (n : Nat)
    (C : NamedBlock V) : Prop :=
  LayerAJointHistoryIdx S rho n C ∧ WitnessProvenanceIdxEmitted S rho n C

def NamedConfirmationIdxQueryEmitted
    (S : Setup V) (rho : NamedRun V) (cap : Time) : Prop :=
  ∀ (n : Nat) (C : NamedBlock V), LayerAJointHistoryIdxEmitted S rho n C →
    ∀ (i : Nat) (v : V) (r : Round), v ∈ rho.honest →
      rho.events[i]? = some (.tick v (S.a r)) → i = n → S.a r ≤ cap →
      ∃ (C' L : NamedBlock V),
        NamedRun.blockInRun S rho C' ∧ NamedBlock.Preceq C C' ∧
        (C' = C ∨ C' = L) ∧ NamedRun.blockInRun S rho L ∧
        L ∈ (actionReadFrom S (NamedRun.stateBefore S rho i v) r).st.bodies ∧
        L.erase = (actionReadFrom S
          (NamedRun.stateBefore S rho i v) r).st.core.live_confirmed ∧
        NamedBlock.Preceq L C'

end DecoupledConsensusModel.Internal.NamedOutageEntry.History

end
