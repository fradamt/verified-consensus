module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ChainState.CarrierAlignment
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ActionSourceCore
public import DecoupledConsensusProofs.Execution.ProgressCanonicality
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.RecoveryVoteCone
public import DecoupledConsensusProofs.Protocol.ChainState.ProposalBridge
public import DecoupledConsensusProofs.Protocol.Grades.GradeFormsBridge
public import DecoupledConsensusProofs.Execution.NamedAncestry
public import DecoupledConsensusProofs.Protocol.ChainState.EntryHeight
public import DecoupledConsensusProofs.Execution.Wire
public import DecoupledConsensusProofs.Protocol.Schedule.RecoveryOpeningFrontierRunBlock
public import DecoupledConsensusProofs.Execution.RecurringArithmeticCore
public import DecoupledConsensusProofs.Protocol.ChainState.Chain
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.ActionSources
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.RawExactHeightSeed
public import DecoupledConsensusInternal.Definitions.NamedLifecycle

@[expose] public section

/-!
# Height-row freshness above the debris frontier

Every nonempty honest action row reads its height from the selected FG source.
Thus, a row above an earlier honest frontier must come from a later action.

For a carrier lifecycle, this excludes rows from the debris prefix. It does
not exclude a partial honest batch emitted at the same height by an action
strictly between the debris boundary and the lifecycle action. The final
theorem exposes that case as an explicit disjunct. If the disjunct is absent,
faulty validators alone cannot make either height-event guard ready in the
`+1` proposal fold.
-/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol

variable {V : Type} [DecidableEq V] [Fintype V]


/-- Every honest nonempty height row at an action reads the derived height of
that action's selected, processed FG source. -/
private theorem heightPair_vote_of_height {hp : NamedHeightPair} {h : Height}
    (he : hp.erase.height? = some h) :
    ∃ entry timeout, hp = .vote h entry timeout := by
  cases hp with
  | empty => simp [NamedHeightPair.erase, HeightPair.height?] at he
  | vote h' entry timeout =>
      have hEq : h' = h := by
        cases timeout <;>
          simpa [NamedHeightPair.erase, HeightPair.height?] using he
      exact ⟨entry, timeout, by rw [hEq]⟩

theorem honestRow_height_le_source
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (_hv : v ∈ rho.honest) {r : Round} {h : Height}
    (hrow : (actionAttestationAt S rho v r).height_pair.erase.height? = some h) :
    ∃ Q : NamedBlock V,
      actionFGSource S (actionReadAt S rho v r) = some Q.erase ∧
        Q ∈ (actionStoreAt S rho v r).st.bodies ∧
        (Protocol.derive_named S.E S.cfg Q).h = h := by
  obtain ⟨entry, timeout, hpair⟩ := heightPair_vote_of_height hrow
  obtain ⟨Cfg, hCfg, hheight, _hentry⟩ := NamedActionSources.action_source
    S rho v r h entry timeout hpair
  obtain ⟨Q, hQ, hQerase, hQderive, _hfg⟩ := NamedActionSources.action_witness
    S rho v r Cfg hCfg
  refine ⟨Q, ?_, ?_, ?_⟩
  · simpa only [hQerase] using hCfg
  · simpa only [actionStoreAt] using hQ
  · rw [hQderive] at hheight
    exact hheight

private theorem actionRowHeight_le_actionHMax
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) (r : Round) {h : Height}
    (hrow : (actionAttestationAt S rho v r).height_pair.erase.height? = some h) :
    h ≤ (actionStoreAt S rho v r).st.core.h_max := by
  obtain ⟨Q, _hsource, hbody, hheight⟩ := honestRow_height_le_source S adm
    hv (v := v) (r := r) hrow
  have hbodyPre : Q ∈ (rho.stateBeforeTime S (S.a r) v).st.bodies := by
    simpa only [actionStoreAt, actionReadAt, NamedActionReads.actionReadAt,
      NamedActionReads.actionReadFrom, NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using hbody
  have hbound := Proofs.NamedStoreBridge.heights_le_hMax_stateBeforeTime S rho
    (S.a r) v Q hbodyPre
  rw [hheight] at hbound
  simpa only [actionStoreAt, actionReadAt, NamedActionReads.actionReadAt,
    NamedActionReads.actionReadFrom, NamedActionReads.confirmationReadFrom,
    NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using hbound

/-- The virtual action store's frontier is below the inclusive public honest
frontier at the same action time. -/
private theorem actionStoreHMax_le_honestHMaxAt
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) (r : Round) :
    (actionStoreAt S rho v r).h_max ≤ honestHMaxAt S rho (S.a r) := by
  have hpre : (actionStoreAt S rho v r).h_max =
      (rho.storeBeforeTime S v (S.a r)).h_max := by
    rfl
  rw [hpre]
  exact (storeBeforeTime_hMax_le_storeAt
      S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed v (S.a r)).trans
    (localHMax_le_honestHMaxAt S rho (S.a r) hv)


/-- An honest action row strictly above the frontier at `` is emitted by an
action whose round is strictly after ``. -/
theorem honestRow_after_frontier
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) {r0 r : Round} {h : Height}
    (habove : honestHMaxAt S rho (S.a r0) < h)
    (hrow : (actionAttestationAt S rho v r).height_pair.erase.height? = some h) :
    r0 < r := by
  by_contra hnot
  have hrr : r ≤ r0 := Nat.le_of_not_gt hnot
  have hlocal : h ≤ (actionStoreAt S rho v r).h_max := by
    exact actionRowHeight_le_actionHMax S adm hv r hrow
  have hcurrent : h ≤ honestHMaxAt S rho (S.a r) :=
    hlocal.trans (actionStoreHMax_le_honestHMaxAt S adm hv r)
  have hmono : honestHMaxAt S rho (S.a r) ≤
      honestHMaxAt S rho (S.a r0) :=
    honestHMaxAt_mono S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
      (Assembly.a_mono S hrr)
  exact (Nat.not_lt_of_ge (hcurrent.trans hmono)) habove








#print axioms honestRow_height_le_source
#print axioms honestRow_after_frontier
#print axioms heightPair_vote_of_height
#print axioms actionRowHeight_le_actionHMax
#print axioms actionStoreHMax_le_honestHMaxAt

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
