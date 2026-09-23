module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.IdxDriverSteps
public import DecoupledConsensusProofs.Execution.IdxDriverHelpers
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.ConfirmationQueryIdxEmitted
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.ActionSources

@[expose] public section

/-!
# Emission-backed index-history driver

This additive driver keeps the previous confirmation witness when an honest
action tick emits no attestation. When the action emits, it performs the same
SG renewal as the original driver and records that emission in provenance.
-/

namespace DecoupledConsensusModel.Proofs.NamedOutageHistory.IdxDriverEmitted

open Internal Execution Execution Internal.NamedOutageEntry Protocol
open Internal.NamedOutageEntry.History
open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol
open JointHistoryProducersTime

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem provenance_mono (S : Setup V) (rho : NamedRun V)
    {n m : Nat} {C : NamedBlock V}
    (h : WitnessProvenanceIdxEmitted S rho n C) (hle : n ≤ m) :
    WitnessProvenanceIdxEmitted S rho m C := by
  rcases h with rfl | ⟨i, v, r, hin, hv, he, hbody, hroot⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨i, v, r, hin.trans hle, hv, he, hbody, hroot⟩

private theorem weak_provenance (S : Setup V) (rho : NamedRun V)
    {n : Nat} {C : NamedBlock V}
    (h : WitnessProvenanceIdxEmitted S rho n C) :
    WitnessProvenanceIdx S rho n C := by
  rcases h with rfl | ⟨i, v, r, hin, hv, he, hbody, hroot | ⟨hroot, hemit⟩⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨i, v, r, hin, hv, he, hbody, Or.inl hroot⟩
  · exact Or.inr ⟨i, v, r, hin, hv, he, hbody, Or.inr hroot⟩

omit [DecidableEq V] [Fintype V] in
private theorem tick_eq {rho : NamedRun V} {i : Nat} {u v : V} {t t' : Time}
    (hi : rho.events[i]? = some (.tick u t))
    (hj : rho.events[i]? = some (.tick v t')) : u = v ∧ t = t' := by
  have h := Option.some.inj (hi.symm.trans hj)
  exact NamedEvent.tick.inj h

set_option linter.unusedVariables false in
theorem jointHistoryIdx_step_action
    (S : Setup V) (rho : NamedRun V) (cap : Time)
    (core : NamedAdmissibleCore S rho)
    (healthy : NamedHealthyPrefixDelivery S rho cap)
    (committees : HonestCommittees S rho.honest) (hR : 3 ≤ S.hc.R)
    (hcap : cap ≤ rho.horizon)
    (windows : ∀ k, 0 < k → domain S.E S.hc k .g2 ≤ cap →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG k)
    (hbad : S.E.electorate.weightOf (Finset.univ \ rho.honest) < S.E.q)
    (hconf : NamedConfirmationIdxQueryEmitted S rho cap)
    (n : Nat) (C : NamedBlock V)
    (hhist : LayerAJointHistoryIdxEmitted S rho n C)
    (hcapn : ∀ i, i < n → ∀ e : NamedEvent V,
      rho.events[i]? = some e → e.time ≤ cap)
    (v : V) (r : Round) (hv : v ∈ rho.honest)
    (hn : rho.events[n]? = some (.tick v (S.a r)))
    (hta : S.a r ≤ cap) :
    ∃ C' : NamedBlock V, NamedRun.blockInRun S rho C' ∧
      NamedBlock.Preceq C C' ∧ LayerAJointHistoryIdxEmitted S rho (n + 1) C' := by
  obtain ⟨C'', L, hC''run, hCC'', hchoice, hLrun, hLbody, hLe, hLC''⟩ :=
    hconf n C hhist n v r hv hn rfl hta
  have hprovC'' : WitnessProvenanceIdxEmitted S rho n C'' := by
    rcases hchoice with hEq | hEq
    · rw [hEq]
      exact hhist.2
    · rw [hEq]
      exact Or.inr ⟨n, v, r, le_rfl, hv, hn, hLbody, Or.inl hLe⟩
  have hhist'' : LayerAJointHistoryIdx S rho n C'' :=
    IdxDriverSteps.jointHistoryIdx_mono S rho n C C'' hhist.1 hCC'' hC''run
      (weak_provenance S rho hprovC'')
  have hconf4'' : JointHistoryGaps.ConfirmationAtTick S rho n C'' := by
    intro u r' hu hi
    obtain ⟨rfl, hr'⟩ := tick_eq hn hi
    have hrr : r' = r := JointHistoryGapsTime.setup_a_injective S hr'.symm
    subst hrr
    exact ⟨L, hLrun, hLbody, hLe, hLC''⟩
  by_cases hemit : NamedRun.emits S rho v
      (Object.attest (Proofs.HealingSurface.actionAttestationAt S rho v r)) (S.a r)
  · obtain ⟨K0, hK0run, hK0body, hK0e, hK0C⟩ :=
      SGVoteOnHistory.sg_vote_on_history S rho cap core healthy committees hR
        hcap windows hbad n C'' hhist'' hcapn n v r hv hn (le_refl n) hconf4''
    obtain ⟨C', hC'run, hC''C', hK0C', hprovC'⟩ :
        ∃ C' : NamedBlock V, NamedRun.blockInRun S rho C' ∧
          NamedBlock.Preceq C'' C' ∧ NamedBlock.Preceq K0 C' ∧
          WitnessProvenanceIdxEmitted S rho n C' := by
      rcases hK0C with hle | hge
      · exact ⟨C'', hC''run, named_preceq_self C'', hle, hprovC''⟩
      · exact ⟨K0, hK0run, hge, named_preceq_self K0,
          Or.inr ⟨n, v, r, le_rfl, hv, hn, hK0body, Or.inr ⟨hK0e, hemit⟩⟩⟩
    have hhist' : LayerAJointHistoryIdx S rho n C' :=
      IdxDriverSteps.jointHistoryIdx_mono S rho n C'' C' hhist'' hC''C'
        hC'run (weak_provenance S rho hprovC')
    have hconf4' : JointHistoryGaps.ConfirmationAtTick S rho n C' := by
      intro u r' hu hi
      obtain ⟨L', hL'run, hL'body, hL'e, hL'C⟩ := hconf4'' u r' hu hi
      exact ⟨L', hL'run, hL'body, hL'e, named_preceq_trans hL'C hC''C'⟩
    have hgraded := JointHistoryGaps.graded_root_on_history S rho cap core healthy
      committees hR hcap windows hbad n C' hhist' hcapn
    obtain ⟨⟨hC'run', h1, h2, h3⟩, h0, h4, hprovWeak⟩ := hhist'
    have hhistA : LayerAHistoryIdx S rho n C' := ⟨hC'run', h1, h2, h3⟩
    have hc1 : IdxDriverSteps.Clause1Idx S rho (n + 1) C' := by
      intro i u ta' a hu hi hem hlt fp hfp
      rcases (by omega : i < n ∨ i = n) with hlt' | rfl
      · exact h1 i u ta' a hu hi hem hlt' fp hfp
      · obtain ⟨rfl, rfl⟩ := tick_eq hn hi
        exact IdxDriverSteps.clause1_at_action_tick S rho core hbad i C' hhistA
          v hv (S.a r) hi a hem fp hfp
    refine ⟨C', hC'run, named_preceq_trans hCC'' hC''C', ?_⟩
    refine ⟨?_, provenance_mono S rho hprovC' (Nat.le_succ _)⟩
    refine ⟨⟨hC'run', hc1, ?_, IdxDriverSteps.clause3_of_clause1
      S rho core (n + 1) C' hC'run' hc1 hbad⟩, ?_, ?_,
      weak_provenance S rho
        (provenance_mono S rho hprovC' (Nat.le_succ _))⟩
    · intro i u ta' a hu hi hem hlt h T timeout hp
      rcases (by omega : i < n ∨ i = n) with hlt' | rfl
      · exact h2 i u ta' a hu hi hem hlt' h T timeout hp
      · obtain ⟨rfl, rfl⟩ := tick_eq hn hi
        exact IdxDriverSteps.clause2_at_action_tick S rho core i C' hgraded
          hconf4' v hv (S.a r) hi a hem h T timeout hp
    · intro i u ta' a hu hi hem hlt key hkey
      rcases (by omega : i < n ∨ i = n) with hlt' | rfl
      · exact h0 i u ta' a hu hi hem hlt' key hkey
      · obtain ⟨rfl, rfl⟩ := tick_eq hn hi
        exact IdxDriverSteps.clause0_at_action_tick S rho core i C' v r hi K0
          hK0run hK0body hK0e hK0C' a hem key hkey
    · intro i u r' hu hi hlt
      rcases (by omega : i < n ∨ i = n) with hlt' | rfl
      · exact h4 i u r' hu hi hlt'
      · exact hconf4' u r' hu hi
  · obtain ⟨⟨hC''run', h1, h2, h3⟩, h0, h4, hprovWeak⟩ := hhist''
    have no_row {u : V} {ta : Time} {a : NamedAttestation V}
        (hi : rho.events[n]? = some (.tick u ta))
        (hem : NamedObject.attest a ∈ NamedRun.emittedAt S rho n u ta) : False := by
      obtain ⟨rfl, rfl⟩ := tick_eq hn hi
      have ha : NamedRun.emits S rho v (.attest a) (S.a r) := ⟨n, hn, hem⟩
      have hshape := (NamedActionSources.action_run_emission S rho
        core.toNamedScheduleWellFormed v r a).mp ha
      apply hemit
      simpa only [hshape.2.2] using ha
    have hc1 : IdxDriverSteps.Clause1Idx S rho (n + 1) C'' := by
      intro i u ta' a hu hi hem hlt fp hfp
      rcases (by omega : i < n ∨ i = n) with hlt' | rfl
      · exact h1 i u ta' a hu hi hem hlt' fp hfp
      · exact False.elim (no_row hi hem)
    refine ⟨C'', hC''run, hCC'', ?_⟩
    refine ⟨?_, provenance_mono S rho hprovC'' (Nat.le_succ _)⟩
    refine ⟨⟨hC''run', hc1, ?_, IdxDriverSteps.clause3_of_clause1
      S rho core (n + 1) C'' hC''run' hc1 hbad⟩, ?_, ?_,
      weak_provenance S rho
        (provenance_mono S rho hprovC'' (Nat.le_succ _))⟩
    · intro i u ta' a hu hi hem hlt h T timeout hp
      rcases (by omega : i < n ∨ i = n) with hlt' | rfl
      · exact h2 i u ta' a hu hi hem hlt' h T timeout hp
      · exact False.elim (no_row hi hem)
    · intro i u ta' a hu hi hem hlt key hkey
      rcases (by omega : i < n ∨ i = n) with hlt' | rfl
      · exact h0 i u ta' a hu hi hem hlt' key hkey
      · exact False.elim (no_row hi hem)
    · intro i u r' hu hi hlt
      rcases (by omega : i < n ∨ i = n) with hlt' | rfl
      · exact h4 i u r' hu hi hlt'
      · exact hconf4'' u r' hu hi

#print axioms jointHistoryIdx_step_action

theorem layerA_joint_history_idx_emitted
    (S : Setup V) (rho : NamedRun V) (cap : Time)
    (core : NamedAdmissibleCore S rho)
    (healthy : NamedHealthyPrefixDelivery S rho cap)
    (committees : HonestCommittees S rho.honest) (hR : 3 ≤ S.hc.R)
    (hcap : cap ≤ rho.horizon)
    (windows : ∀ k, 0 < k → domain S.E S.hc k .g2 ≤ cap →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG k)
    (hbad : S.E.electorate.weightOf (Finset.univ \ rho.honest) < S.E.q)
    (hconf : NamedConfirmationIdxQueryEmitted S rho cap) :
    ∀ n : Nat, n ≤ boundaryIdx rho cap →
      ∃ C : NamedBlock V, LayerAJointHistoryIdxEmitted S rho n C := by
  intro n
  induction n with
  | zero =>
      intro hle
      exact ⟨.genesis, IdxDriverHelpers.jointHistoryIdx_zero S rho hbad,
        Or.inl rfl⟩
  | succ n ih =>
      intro hle
      obtain ⟨C, hC⟩ := ih (by omega)
      have hnb : n < boundaryIdx rho cap := by omega
      have hcapn := IdxDriverHelpers.hcapn_of_le_boundaryIdx rho core.sorted
        (le_of_lt hnb : n ≤ boundaryIdx rho cap)
      cases hev : rho.events[n]? with
      | none =>
          exact ⟨C,
            IdxDriverHelpers.jointHistoryIdx_succ_no_event S rho n C
              (List.getElem?_eq_none_iff.mp hev) hC.1,
            provenance_mono S rho hC.2 (Nat.le_succ _)⟩
      | some ev =>
          cases ev with
          | deliver u o tt =>
              exact ⟨C,
                IdxDriverSteps.jointHistoryIdx_step_deliver S rho cap core healthy
                  committees hR hcap windows hbad n C hC.1 hcapn u o tt hev,
                provenance_mono S rho hC.2 (Nat.le_succ _)⟩
          | tick u tt =>
              have htt : tt ≤ cap := by
                simpa only [NamedEvent.time] using
                  IdxDriverHelpers.time_le_of_lt_boundaryIdx rho core.sorted hev hnb
              by_cases hact : u ∈ rho.honest ∧ ∃ r : Round, tt = S.a r
              · obtain ⟨hu, r, rfl⟩ := hact
                obtain ⟨C', hC'run, hCC', hC'⟩ :=
                  jointHistoryIdx_step_action S rho cap core healthy committees
                    hR hcap windows hbad hconf n C hC hcapn u r hu hev htt
                exact ⟨C', hC'⟩
              · exact ⟨C,
                  IdxDriverSteps.jointHistoryIdx_step_tick_inert S rho core hbad
                    n C hC.1 u tt hev (by
                      intro r hr hu
                      exact hact ⟨hu, r, hr⟩),
                  provenance_mono S rho hC.2 (Nat.le_succ _)⟩

#print axioms layerA_joint_history_idx_emitted

end DecoupledConsensusModel.Proofs.NamedOutageHistory.IdxDriverEmitted

end
