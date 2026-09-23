module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ValidatorClient.RecoveryBoundary
public import DecoupledConsensusProofs.Execution.FGSelectorWitness

@[expose] public section

/-! # Named prefix-record recovery boundary
This module ports the retained prefix-record induction to the named execution.
The record fields remain in `NamedRecord.legacy`, while every action row and
every chain-state argument uses `NamedAttestation` and `derive_named`.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Protocol
open Protocol
open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- An honest named record has no recovery-height lock in a capped prefix. -/
theorem stateBefore_lock_none_recoveryHeight_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {stop : Nat} {hF0 blocked : Height}
    (hcap : HonestPrefixFinalityCap S rho stop hF0)
    (hrec : NjGap.RecoveryHeight S.cfg hF0 blocked)
    {v : V} (hv : v ∈ rho.honest) :
    ∀ n : Nat, n ≤ stop →
      (rho.stateBefore S n v).record.legacy.lock blocked = none := by
  intro n
  induction n with
  | zero =>
      intro _
      simp [Run.stateBefore, NamedRun.stateBefore, NamedWorld.init,
        NamedNode.initial, Protocol.NamedRecord.initial,
        Protocol.Record.initial]
  | succ n ih =>
      intro hnSuccStop
      have hnStop : n ≤ stop := (Nat.le_succ n).trans hnSuccStop
      have ihN := ih hnStop
      have hstep : rho.stateBefore S (n + 1) =
          (rho.events[n]?.toList).foldl (World.step S)
            (rho.stateBefore S n) := by
        unfold Run.stateBefore NamedRun.stateBefore
        rw [List.take_add_one, List.foldl_append]
      rcases hevent : rho.events[n]? with _ | e
      · rw [hstep, hevent]
        simpa only [Option.toList, List.foldl_nil] using ihN
      · cases e with
        | deliver u o t =>
            by_cases huv : u = v
            · subst u
              rw [hstep, hevent]
              simp only [Option.toList, List.foldl_cons, List.foldl_nil,
                World.step, NamedWorld.step, Function.update_self]
              simpa only [NamedNode.process_record_eq] using ihN
            · rw [hstep, hevent]
              simp only [Option.toList, List.foldl_cons, List.foldl_nil,
                World.step, NamedWorld.step, Function.update_of_ne (Ne.symm huv)]
              exact ihN
        | tick u t =>
            by_cases huv : u = v
            · subst u
              have hrecord : (rho.stateBefore S (n + 1) v).record =
                  (on_tick_emit S v (rho.stateBefore S n v) t).1.record :=
                stateBefore_succ_record S rho hevent
              cases hpost :
                  (rho.stateBefore S (n + 1) v).record.legacy.lock blocked with
              | none => rfl
              | some T =>
                  have hpostTick :
                      (on_tick_emit S v (rho.stateBefore S n v) t).1.record.legacy.lock
                          blocked = some T := by
                    rw [← hrecord]
                    exact hpost
                  obtain ⟨a, hemitted, hpair⟩ :=
                    Protocol.on_tick_emit_lock_introduced
                      S v (rho.stateBefore S n v) t ihN hpostTick
                  have hemit : rho.emits S v (Object.attest a) t :=
                    ⟨n, hevent, hemitted⟩
                  have htime : t = S.a a.round :=
                    (Proofs.Optimistic.emits_attest_shape S hemit).2
                  have haEq : a = actionAttestationAt S rho v a.round := by
                    subst t
                    exact ((NamedActionSources.action_run_emission S rho
                      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
                      v a.round a).mp hemit).2.2
                  have hcapN : HonestPrefixFinalityCap S rho n hF0 :=
                    honestPrefixFinalityCap_of_le S
                      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hnStop hcap
                  have huniverse : HonestPrefixNJUniverse S rho n blocked :=
                    honestPrefixNJUniverse_of_finalityCap S
                      adm.toNamedAdmissibleCore.toNamedDeliveryWellFormed hcapN hrec
                  have hstate : rho.stateBefore S n v =
                      rho.stateBeforeTime S (S.a a.round) v := by
                    have htick := Proofs.Optimistic.stateBefore_tick_eq_stateBeforeTime
                      S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hevent
                    rw [htime] at htick
                    exact htick
                  have hne := actionHead_h_j_ne_of_honestPrefixNJUniverse
                    S adm huniverse hv hstate
                  have hfp :
                      (actionAttestationAt S rho v a.round).finality_pair =
                        some ⟨blocked, T⟩ := by
                    rw [← haEq]
                    exact hpair
                  have hfpAtHead := hfp
                  change (Protocol.NamedActions.round_action_with
                      (NamedProfile.gradeContract
                        (actionStoreAt S rho v a.round).cache)
                      S.E S.hc (S.node v)
                      (actionStoreAt S rho v a.round).st.core.toHealing
                      (actionStoreAt S rho v a.round).record).2.finality_pair =
                    some ⟨blocked, T⟩ at hfpAtHead
                  rw [round_action_finality_pair_eq] at hfpAtHead
                  have hheadHeight := finality_pair_height hfpAtHead
                  exact absurd hheadHeight hne
            · rw [hstep, hevent]
              simp only [Option.toList, List.foldl_cons, List.foldl_nil,
                World.step, NamedWorld.step, Function.update_of_ne (Ne.symm huv)]
              exact ihN


/-- An honest named record has no proper target at the recovery height in a
capped prefix. This is the named prefix-record induction retained in the prior
`RecoveryBoundaryRun` Open record. -/
theorem stateBefore_target_none_recoveryHeight_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {stop : Nat} {hF0 blocked : Height}
    (hcap : HonestPrefixFinalityCap S rho stop hF0)
    (hrec : NjGap.RecoveryHeight S.cfg hF0 blocked)
    {v : V} (hv : v ∈ rho.honest) :
    ∀ n : Nat, n ≤ stop →
      (rho.stateBefore S n v).record.legacy.target blocked = none := by
  intro n
  induction n with
  | zero =>
      intro _
      simp [Run.stateBefore, NamedRun.stateBefore, NamedWorld.init,
        NamedNode.initial, Protocol.NamedRecord.initial,
        Protocol.Record.initial]
  | succ n ih =>
      intro hnSuccStop
      have hnStop : n ≤ stop := (Nat.le_succ n).trans hnSuccStop
      have ihN := ih hnStop
      have hstep : rho.stateBefore S (n + 1) =
          (rho.events[n]?.toList).foldl (World.step S)
            (rho.stateBefore S n) := by
        unfold Run.stateBefore NamedRun.stateBefore
        rw [List.take_add_one, List.foldl_append]
      rcases hevent : rho.events[n]? with _ | e
      · rw [hstep, hevent]
        simpa only [Option.toList, List.foldl_nil] using ihN
      · cases e with
        | deliver u o t =>
            by_cases huv : u = v
            · subst u
              rw [hstep, hevent]
              simp only [Option.toList, List.foldl_cons, List.foldl_nil,
                World.step, NamedWorld.step, Function.update_self]
              simpa only [NamedNode.process_record_eq] using ihN
            · rw [hstep, hevent]
              simp only [Option.toList, List.foldl_cons, List.foldl_nil,
                World.step, NamedWorld.step, Function.update_of_ne (Ne.symm huv)]
              exact ihN
        | tick u t =>
            by_cases huv : u = v
            · subst u
              have hrecord : (rho.stateBefore S (n + 1) v).record =
                  (on_tick_emit S v (rho.stateBefore S n v) t).1.record :=
                stateBefore_succ_record S rho hevent
              cases hpost :
                  (rho.stateBefore S (n + 1) v).record.legacy.target blocked with
              | none => rfl
              | some T =>
                  have hpostTick :
                      (on_tick_emit S v (rho.stateBefore S n v) t).1.record.legacy.target
                          blocked = some T := by
                    rw [← hrecord]
                    exact hpost
                  obtain ⟨a, hemitted, hpair⟩ :=
                    Protocol.on_tick_emit_target_introduced
                      S v (rho.stateBefore S n v) t ihN hpostTick
                  have hemit : rho.emits S v (Object.attest a) t :=
                    ⟨n, hevent, hemitted⟩
                  have htime : t = S.a a.round :=
                    (Proofs.Optimistic.emits_attest_shape S hemit).2
                  have hrow : a.height_pair.erase.height? = some blocked :=
                    by
                      simpa only [NamedAttestation.erase] using
                        congrArg HeightPair.height? hpair
                  have hval : a.val_index = v :=
                    (Proofs.Optimistic.emits_attest_shape S hemit).1
                  have hemitAuthor : rho.emits S a.val_index (Object.attest a) t := by
                    rw [hval]
                    exact hemit
                  have haHon : a.val_index ∈ rho.honest := by
                    rw [hval]
                    exact hv
                  subst v
                  obtain ⟨D, J, -, haEq, hsource, -, hheight, -, -, -⟩ :=
                    honestEmittedHeightRow_exactFGSelectorWitness
                      S adm haHon hemitAuthor hrow
                  have hcapN : HonestPrefixFinalityCap S rho n hF0 :=
                    honestPrefixFinalityCap_of_le S
                      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hnStop hcap
                  have huniverse : HonestPrefixNJUniverse S rho n blocked :=
                    honestPrefixNJUniverse_of_finalityCap S
                      adm.toNamedAdmissibleCore.toNamedDeliveryWellFormed hcapN hrec
                  have hpairNamed : a.height_pair.erase =
                      HeightPair.target blocked T := by
                    simpa only [NamedAttestation.erase] using hpair
                  have hstate : rho.stateBefore S n a.val_index =
                      rho.stateBeforeTime S (S.a a.round) a.val_index := by
                    have htick := Proofs.Optimistic.stateBefore_tick_eq_stateBeforeTime
                      S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hevent
                    rw [htime] at htick
                    exact htick
                  have hrecordEq : (rho.stateBefore S n a.val_index).record =
                      (rho.stateBeforeTime S (S.a a.round) a.val_index).record :=
                    congrArg (fun st => st.record) hstate
                  cases ht : (rho.stateBefore S n a.val_index).record.legacy.timeout blocked with
                  | false =>
                      have hlock :
                          (rho.stateBefore S n a.val_index).record.legacy.lock blocked = none :=
                        stateBefore_lock_none_recoveryHeight_named
                          S adm hcap hrec haHon n hnStop
                      have hfresh : RecordFreshAt
                          (actionStoreAt S rho a.val_index a.round).record.legacy blocked := by
                        have htarget :
                            (rho.stateBeforeTime S (S.a a.round) a.val_index).record.legacy.target
                              blocked = none := by
                          rw [← hrecordEq]
                          exact ihN
                        have htimeout :
                            (rho.stateBeforeTime S (S.a a.round) a.val_index).record.legacy.timeout
                              blocked = false := by
                          rw [← hrecordEq]
                          exact ht
                        have hlock' :
                            (rho.stateBeforeTime S (S.a a.round) a.val_index).record.legacy.lock
                              blocked = none := by
                          rw [← hrecordEq]
                          exact hlock
                        exact ⟨htarget, htimeout, hlock'⟩
                      have htimeoutPair :=
                        actionAttestationAt_height_pair_timeout_of_honestPrefixNJUniverse
                          S adm huniverse haHon hstate hsource hheight hfresh
                      rw [← haEq] at htimeoutPair
                      have herase := congrArg NamedHeightPair.erase htimeoutPair
                      rw [hpairNamed] at herase
                      cases herase
                  | true =>
                      have htimeout :
                          (rho.stateBeforeTime S (S.a a.round) a.val_index).record.legacy.timeout
                            blocked = true := by
                        rw [← hrecordEq]
                        exact ht
                      have htimeoutPair :=
                        actionAttestationAt_height_pair_timeout_of_recorded
                          S rho hsource hheight htimeout
                      rw [← haEq] at htimeoutPair
                      have herase := congrArg NamedHeightPair.erase htimeoutPair
                      rw [hpairNamed] at herase
                      cases herase
            · rw [hstep, hevent]
              simp only [Option.toList, List.foldl_cons, List.foldl_nil,
                World.step, NamedWorld.step, Function.update_of_ne (Ne.symm huv)]
              exact ihN

/-- The action at a capped recovery height emits a named timeout, including
the repeated-timeout record case. -/
theorem actionAttestationAt_height_pair_timeout_recoveryHeight_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {stop : Nat} {hF0 blocked : Height}
    (hcap : HonestPrefixFinalityCap S rho stop hF0)
    (hrec : NjGap.RecoveryHeight S.cfg hF0 blocked)
    {v : V} (hv : v ∈ rho.honest) {r : Round}
    (haction : strictEventIndex rho (S.a r) ≤ stop)
    {Q : Block V}
    (hsource : actionFGSource S (actionStoreAt S rho v r) = some Q)
    (hheight : ((actionStoreAt S rho v r).st.core.σ Q).h = blocked) :
    (actionAttestationAt S rho v r).height_pair =
      NamedHeightPair.vote blocked
        ((actionStoreAt S rho v r).st.core.σ Q).T_h.root true := by
  let actionPrefix := strictEventIndex rho (S.a r)
  have hstateWorld := stateBeforeTime_eq_stateBefore_strictEventIndex
    S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed (S.a r)
  have hstate : rho.stateBefore S actionPrefix v =
      rho.stateBeforeTime S (S.a r) v :=
    congrFun hstateWorld.symm v
  have hcapAction : HonestPrefixFinalityCap S rho actionPrefix hF0 :=
    honestPrefixFinalityCap_of_le S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed haction hcap
  have huniverse : HonestPrefixNJUniverse S rho actionPrefix blocked :=
    honestPrefixNJUniverse_of_finalityCap S
      adm.toNamedAdmissibleCore.toNamedDeliveryWellFormed hcapAction hrec
  have htarget :
      (rho.stateBeforeTime S (S.a r) v).record.legacy.target blocked = none := by
    rw [← congrArg (fun st => st.record) hstate]
    exact stateBefore_target_none_recoveryHeight_named
      S adm hcap hrec hv actionPrefix haction
  have hlock :
      (rho.stateBeforeTime S (S.a r) v).record.legacy.lock blocked = none := by
    rw [← congrArg (fun st => st.record) hstate]
    exact stateBefore_lock_none_recoveryHeight_named
      S adm hcap hrec hv actionPrefix haction
  cases ht : (rho.stateBeforeTime S (S.a r) v).record.legacy.timeout blocked with
  | false =>
      exact actionAttestationAt_height_pair_timeout_of_honestPrefixNJUniverse
        S adm huniverse hv hstate hsource hheight ⟨htarget, ht, hlock⟩
  | true =>
      exact actionAttestationAt_height_pair_timeout_of_recorded
        S rho hsource hheight ht

/-- A proper honest target row cannot use a capped recovery height. -/
theorem honestEmittedTarget_height_ne_recovery_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {stop : Nat} {blocked hF0 h : Height}
    (hcap : HonestPrefixFinalityCap S rho stop hF0)
    (hrec : NjGap.RecoveryHeight S.cfg hF0 blocked)
    {a : NamedAttestation V} {ta : Time} {root : BlockId}
    (ha : a.val_index ∈ rho.honest)
    (hemit : NamedRun.emits S rho a.val_index (Object.attest a) ta)
    (haction : strictEventIndex rho (S.a a.round) ≤ stop)
    (hpair : a.height_pair.erase = HeightPair.target h root) :
    h ≠ blocked := by
  intro heq
  subst h
  have hrow : a.height_pair.erase.height? = some blocked := hpair ▸ rfl
  obtain ⟨D, _, _, haEq, hsource, _, hheight, _, _, -⟩ :=
    honestEmittedHeightRow_exactFGSelectorWitness S adm ha hemit hrow
  have htimeout := actionAttestationAt_height_pair_timeout_recoveryHeight_named
    S adm hcap hrec ha haction hsource hheight
  have herase := congrArg NamedHeightPair.erase htimeout
  rw [← haEq, hpair] at herase
  cases herase

#print axioms stateBefore_lock_none_recoveryHeight_named
#print axioms stateBefore_target_none_recoveryHeight_named
#print axioms actionAttestationAt_height_pair_timeout_recoveryHeight_named
#print axioms honestEmittedTarget_height_ne_recovery_named

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
