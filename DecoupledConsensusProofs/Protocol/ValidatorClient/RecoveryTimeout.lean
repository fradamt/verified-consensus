module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ChainState.NjGap
public import DecoupledConsensusProofs.Protocol.ChainState.ProgressQuorumCore
public import DecoupledConsensusProofs.Protocol.Handlers.Bridges
public import DecoupledConsensusInternal.Healing
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge
public import DecoupledConsensusProofs.Protocol.Schedule.Action
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.FrontierRise
public import DecoupledConsensusProofs.Protocol.ValidatorClient.FinalityPairCore
public import DecoupledConsensusProofs.Protocol.ValidatorClient.RecordFresh
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ActionSourceCore
public import DecoupledConsensusProofs.Protocol.Schedule.ConfirmationHistoryProducer
public import DecoupledConsensusInternal.Execution.Run
public import DecoupledConsensusProofs.Execution.Concentration
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.ActionSources
public import DecoupledConsensusProofs.Protocol.ChainState.DerivationGeometry
public import DecoupledConsensusProofs.Protocol.ValidatorClient.HeightPairCases

@[expose] public section

/-!
# Recovery timeout emission at the exact Section 7 action

`RecordFreshRun` proves that a height which an honest validator has not used
is fresh in its anti-slashing record. `NjGap` proves that no chain state in a
nonfinality run can carry a justification at a recovery height. This file
connects those facts to the exact named `round_action` value emitted by
Section 7.

The source of the height pair is `fg_source`, while the source of the finality
pair is the action's Goldfish head. They need not be the same block. The proof
therefore keeps the two sources separate and uses only the fact that the latter
cannot have justification height equal to the recovery height.

Open (class d, statement-shape). The run-level derivation of the
two facts a fresh-source timeout needs at a recovery height —
`(store).σ Q).nj = true` and `(store).σ head).h_j ≠ H` — used
`NjGap.derivedStateAgrees_storeAt` and `NjGap.store_chainCap`, both stated
against the pre-selection `derived_state` (the erased derivation). `NjGapRun.lean`
 already removed both from its own module rather than porting
them, and its Open comment names this exact file as a real consumer. The named
runtime's own coherence invariant (`Proofs.NamedStoreBridge.derivedView_*`,
consumed here for the *tree-membership* half of this file, which needs no
`derived_state` fact at all) gives only `st.core.σ D.erase = derive_named E cfg
D` for a retained named body `D` — agreement with `derived_state` holds only on
timeout-free chains, an **open query**
(`Internal.NamedDerivationAgreesWithoutTimeoutsQuery`, Q-E1,
`DecoupledConsensusStatements/Instantiation/NamedEvidence.lean:70`), not a
theorem. Closing the two run-level derivations therefore needs either Q-E1
discharged (a new hypothesis on a public statement) or a fresh `NamedBlock`/
`derive_named` induction mirroring `Proofs.HealingLemmas.NjGap`'s `nj_of_cap`/
`h_j_ne_recovery_height` chain, which does not exist and is not obviously true
under targeted timeouts (design caveat caveat). Not guessed at; not available.

Dropped here, with real cone consumers so  does not license archiving them
(consumer counts at Open time, from a full-cone grep):
`actionHead_h_j_ne_recoveryHeight` (MigrationResidualsRun and others),
`actionSource_nj_recoveryHeight` (RecoveryRecordInvariantRun and others),
`actionAttestationAt_height_pair_timeout_recoveryHeight`
(RecoveryRecordInvariantRun), `honest_emits_recoveryHeight_timeout`
(RecoveryActivationRun, RecoverySourceWeightRun via
`honest_emits_recoveryHeight_timeout_all`). Every one of those consumer files
is itself still on the pre-selection `Protocol.round_action`/bare-`Record` shape
(unbuilt), so none of them is unblocked by this proof regardless; they carry
the same Open forward once their own turn comes.

Everything else in the file — the pure `height_pair`/`round_action_with`
bridges, the tree-membership fact for the action head (no `derived_state`
dependency, only `NamedStoreBridge`'s `justifiedInTree_*`/`finalizedInTree_*`
and `Proofs.Records.healing_get_head_mem`), and the *recorded*-timeout end-to-end
theorems (whose record-guard premise is supplied directly, not derived) — is
mechanical and restated below.
-/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Protocol (Record height_pair own_lock finality_pair)
open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

omit [DecidableEq V] [Fintype V] in
/-- At a fresh height whose `nj` bit is set, the pair rule emits a timeout if
the same attestation's finality pair does not use that height. -/
theorem height_pair_timeout_of_fresh_of_finality_avoids
    {Lambda : Record} {H : Height} {T : BlockId}
    (hfresh : RecordFreshAt Lambda H) (fp : Option FinalityPair)
    (havoid : forall p : FinalityPair, fp = some p -> p.height ≠ H) :
    height_pair Lambda (some (H, T, true)) fp = HeightPair.timeout H := by
  cases fp with
  | none =>
      rcases hfresh with ⟨htarget, htimeout, hlock⟩
      simp [height_pair, own_lock, htarget, htimeout, hlock]
  | some p =>
      exact height_pair_timeout_of_fresh_of_finality_height_ne
        hfresh (havoid p rfl)


/-- The named round action's finality pair, unfolded to the compatibility call at the
action's own resolved Goldfish head. Unconditional counterpart of
`HeightPairCasesRun.named_round_action_height_pair` for the finality-pair
field: both fields are copied verbatim from one `create_attestation` call. -/
theorem round_action_finality_pair_eq (contract : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (nd : Protocol.Node V)
    (st : Protocol.HealingStore V) (record : Protocol.NamedRecord) :
    (Protocol.NamedActions.round_action_with contract E hc nd st record).2.finality_pair =
      finality_pair record.legacy
        (st.σ (actionHeadWith contract E hc st)).h_j
        (st.σ (actionHeadWith contract E hc st)).J.root
        (st.σ (actionHeadWith contract E hc st)).h_F := by
  simp only [Protocol.NamedActions.round_action_with, Protocol.with_attestation_input,
    Protocol.NamedActions.creatorInput, Protocol.NamedRecord.create,
    Protocol.NamedRecord.legacyCreate, Protocol.NamedRecord.encodeRow,
    Protocol.get_fg_vote_with, Protocol.create_attestation, actionHeadWith]

/-- Pure action bridge. If the exact `fg_source` used by the named
`round_action` is at a fresh nonjustifiable height `H`, and the exact
Goldfish head has no justification at `H`, the emitted named height pair is a
timeout row at `H`.

The head and the height source may be on different branches; no compatibility
between them is assumed. -/
theorem round_action_height_pair_timeout_of_fresh_source
    (contract : Protocol.GradeContract V) (E : Env V) (hc : Protocol.HealConfig)
    (nd : Protocol.Node V) (st : Protocol.HealingStore V) (record : Protocol.NamedRecord)
    {H : Height} {Q : Block V}
    (hsource : actionSource contract E hc st = some Q)
    (hheight : (st.σ Q).h = H) (hnj : (st.σ Q).nj = true)
    (hfresh : RecordFreshAt record.legacy H)
    (hheadj : (st.σ (actionHeadWith contract E hc st)).h_j ≠ H) :
    (Protocol.NamedActions.round_action_with contract E hc nd st record).2.height_pair =
      NamedHeightPair.vote H (st.σ Q).T_h.root true := by
  have havoid : ∀ p : FinalityPair,
      (Protocol.NamedActions.round_action_with contract E hc nd st record).2.finality_pair =
        some p → p.height ≠ H := by
    intro p hp
    rw [round_action_finality_pair_eq] at hp
    have hpHeight := finality_pair_height hp
    intro hpH
    exact hheadj (hpHeight.trans hpH)
  rw [named_round_action_height_pair, hsource, Option.map_some, hheight, hnj,
    height_pair_timeout_of_fresh_of_finality_avoids hfresh _ havoid]
  exact encodeHeight_of_timeout

/-- Pure action bridge for a recorded timeout. If the exact `fg_source` is
still at `H`, the named round action repeats a timeout row at `H` without a
freshness or recovery arithmetic premise. -/
theorem round_action_height_pair_timeout_of_recorded_source
    (contract : Protocol.GradeContract V) (E : Env V) (hc : Protocol.HealConfig)
    (nd : Protocol.Node V) (st : Protocol.HealingStore V) (record : Protocol.NamedRecord)
    {H : Height} {Q : Block V}
    (hsource : actionSource contract E hc st = some Q)
    (hheight : (st.σ Q).h = H)
    (htimeout : record.legacy.timeout H = true) :
    (Protocol.NamedActions.round_action_with contract E hc nd st record).2.height_pair =
      NamedHeightPair.vote H (st.σ Q).T_h.root true := by
  rw [named_round_action_height_pair, hsource, Option.map_some, hheight,
    height_pair_eq_timeout_of_timeout record.legacy _ htimeout]
  exact encodeHeight_of_timeout

/-! ## Run-level exclusion of the recovery height at the action head -/

/-- The strict pre-time store is the inclusive store one integer instant
earlier. -/
theorem storeBeforeTime_eq_storeAt_sub_one_recovery
    (S : Setup V) (rho : Run V) (v : V) (t : Time) :
    rho.storeBeforeTime S v t = rho.storeAt S v (t - 1) := by
  have hfilter :
      (fun e : Event V => decide (e.time < t)) =
        (fun e : Event V => decide (e.time <= t - 1)) := by
    funext e
    exact Bool.decide_congr (Int.le_sub_one_iff).symm
  show (NamedRun.stateBeforeTime S rho t v).st = (NamedRun.readAt S rho (t - 1) v).st
  unfold NamedRun.stateBeforeTime NamedRun.readAt
  rw [hfilter]


/-- End-to-end repeat behavior at the exact Section 7 action. A validator
whose local record already contains `timeout H` emits the same timeout row
whenever the action's exact height source is still at `H`. -/
theorem actionAttestationAt_height_pair_timeout_of_recorded
    (S : Setup V) (rho : Run V) {v : V} {r : Round} {Q : Block V} {H : Height}
    (hsource : actionFGSource S (actionStoreAt S rho v r) = some Q)
    (hheight : ((actionStoreAt S rho v r).σ Q).h = H)
    (htimeout :
      (rho.stateBeforeTime S (S.a r) v).record.legacy.timeout H = true) :
    (actionAttestationAt S rho v r).height_pair =
      NamedHeightPair.vote H ((actionStoreAt S rho v r).σ Q).T_h.root true := by
  have hrecEq : (actionStoreAt S rho v r).record =
      (rho.stateBeforeTime S (S.a r) v).record := rfl
  show (Protocol.NamedActions.round_action_with
      (NamedProfile.gradeContract (actionStoreAt S rho v r).cache)
      S.E S.hc (S.node v) (actionStoreAt S rho v r).toHealing
      (actionStoreAt S rho v r).record).2.height_pair =
      NamedHeightPair.vote H ((actionStoreAt S rho v r).σ Q).T_h.root true
  rw [hrecEq]
  exact round_action_height_pair_timeout_of_recorded_source
    (NamedProfile.gradeContract (actionStoreAt S rho v r).cache)
    S.E S.hc (S.node v) (actionStoreAt S rho v r).toHealing
    (rho.stateBeforeTime S (S.a r) v).record hsource hheight htimeout


end HealingSurface
end Proofs
end DecoupledConsensusModel

end
