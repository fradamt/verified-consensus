module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.FixedHeightRootOpeningParentComplete

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Internal.PhaseGrades
open DecoupledConsensusModel.Protocol
open Protocol
open Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The action read's raw input view is the strict read's -/

/-- The same-tick confirmation duty changes no field the grade view reads. -/
private theorem actionRead_gradeView_eq (S : Setup V) (rho : Run V)
    (v : V) (q : Round) :
    (actionReadAt S rho v q).st.core.toHealing.gradeView =
      (rho.stateBeforeTime S (S.a q) v).st.core.toHealing.gradeView := rfl

/-- The grade view resolves roots in the reader's own processed tree. -/
private theorem actionRead_tree_eq (S : Setup V) (rho : Run V)
    (v : V) (q : Round) :
    (actionReadAt S rho v q).st.core.toHealing.gradeView.T =
      (rho.stateBeforeTime S (S.a q) v).st.core.T := rfl

/-! ## An honest author's window input is that author's own action vote -/

/-- Every raw round-`q` window input tagged with an honest author is that
author's own round-`u.round` action vote, so its head field is that author's
exact action SG carrier for the round the vote was cast in.

The author tag is authentic, an honest node emits exactly one attestation per
round (`Proofs.Optimistic.emits_attest_unique`), and the exact action attestation's
`confirmed` field IS the round's carrier root
(`actionAttestationAt_shape`). This is the round-local half of earlier's
`nextActionBatchAligned_of_carriersPreceq`. -/
theorem honestRawInput_confirmed_eq_actionCarrier_root
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q : Round} (hhor : S.a q ≤ rho.horizon) {cutoff : Time} {v w : V}
    (hw : w ∈ rho.honest)
    {u : Protocol.SGVote V}
    (hu : u ∈ DecoupledConsensusModel.Protocol.rawInputs
      (actionReadAt S rho v q).st.core.toHealing.gradeView
      S.hc.η_SG q cutoff w) :
    u.round ∈ Protocol.latest_window S.hc.η_SG q ∧
      u.confirmed = some (actionSGBlockAt S rho w u.round).root := by
  have hu' : u ∈ DecoupledConsensusModel.Protocol.rawInputs
      (rho.stateBeforeTime S (S.a q) v).st.core.toHealing.gradeView
      S.hc.η_SG q cutoff w := by
    rw [← actionRead_gradeView_eq S rho v q]
    exact hu
  obtain ⟨a, -, hround, hproj, hwindow, hlt, hemit⟩ :=
    NamedOutageClosure.rawInputs_trace S rho
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
      adm.toNamedAdmissibleCore.toNamedUnforgeable
      (S.a q) cutoff v S.hc.η_SG q w hw hu'
  refine ⟨hwindow, ?_⟩
  have hactionHor : S.a a.round ≤ rho.horizon :=
    le_of_lt (lt_of_lt_of_le hlt hhor)
  have hexact := honest_emits_exact_actionAttestationAt S adm hw a.round
    hactionHor
  have hshape := actionAttestationAt_shape S rho w a.round
  have haEq : a = actionAttestationAt S rho w a.round :=
    Proofs.Optimistic.emits_attest_unique S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hemit hexact
      hshape.2.1.symm
  have hconfA : a.confirmed = some (actionSGBlockAt S rho w a.round).root := by
    nth_rewrite 1 [haEq]
    exact hshape.2.2
  have hconfU : u.confirmed = a.confirmed := by
    rw [← hproj]
    exact NamedOutageClosure.sgVote_confirmed a
  rw [hconfU, ← hround]
  exact hconfA

/-- The head of an honest author's raw window input, when it resolves in the
reader's tree, IS that author's exact round-`u.round` action carrier.

Both blocks are run blocks — the head because the reader is honest and holds
it, the carrier because it was selected from the author's own processed tree —
so the shared root makes them equal
(`Protocol.runBlock_eq_of_root_eq`). -/
theorem honestWindowInput_head_eq_actionCarrier
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q : Round} (hhor : S.a q ≤ rho.horizon) {cutoff : Time} {v w : V}
    (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    {u : Protocol.SGVote V}
    (hu : u ∈ DecoupledConsensusModel.Protocol.rawInputs
      (actionReadAt S rho v q).st.core.toHealing.gradeView
      S.hc.η_SG q cutoff w)
    {head : Block V} (hconf : u.confirmed = some head.root)
    (hfind : Block.find?
      (actionReadAt S rho v q).st.core.toHealing.gradeView.T head.root
        = some head) :
    u.round ∈ Protocol.latest_window S.hc.η_SG q ∧
      head = actionSGBlockAt S rho w u.round := by
  obtain ⟨hwindow, hcarrier⟩ :=
    honestRawInput_confirmed_eq_actionCarrier_root S adm hhor hw hu
  refine ⟨hwindow, ?_⟩
  have hroot : head.root = (actionSGBlockAt S rho w u.round).root :=
    Option.some.inj (hconf.symm.trans hcarrier)
  have hheadMem : head ∈ (rho.stateBeforeTime S (S.a q) v).st.core.T := by
    rw [← actionRead_tree_eq S rho v q]
    exact Proofs.HealingLemmas.find?_mem hfind
  obtain ⟨H, hHerase, hHrun⟩ :=
    Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hv (S.a q) hheadMem
  have hcarrierMem : actionSGBlockAt S rho w u.round ∈
      (rho.stateBeforeTime S (S.a u.round) w).st.core.T :=
    actionSGBlockAt_mem_storeBeforeTime S rho w u.round
  obtain ⟨D, hDerase, hDrun⟩ :=
    Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hw (S.a u.round)
      hcarrierMem
  have hrootEq : H.erase.root = D.erase.root := by
    rw [hHerase, hDerase]
    exact hroot
  have hHD : H.erase = D.erase :=
    Protocol.runBlock_eq_of_root_eq
      adm.toNamedAdmissibleCore.toNamedRootCollisionFree hHrun hDrun hrootEq
  rw [← hHerase, ← hDerase]
  exact hHD





/-- **The pre-rewrite batch-alignment producer, latest-vote form.** With every
honest action carrier of round `q - 1` below `Can`, the LATEST interpreted
round-`q` input of an honest author has its head below `Can`, as soon as that
author's own round-`(q - 1)` action vote is one of its interpreted inputs.

This is the round-local premise set of earlier's producer. The selection premise
is what `Protocol.latest_window` is read through: the grade tests
`covers u.key B` only at the maximal-round token
(`DecoupledConsensusModel.Protocol.Supports`), so this form is what the restated grade
consumes. The window's upper bound puts every input at a round `< q`, and the
author's own round-`(q - 1)` vote puts the maximum at `q - 1`.

`0 < q` is not needed: at `q = 0` the window is empty, so the
selection premise is unsatisfiable. -/
theorem nextActionBatchAligned_preceq_of_carriersPreceq_at_latest
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q : Round} (hhor : S.a q ≤ rho.horizon) {Can : Block V}
    (hcarriers : ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u (q - 1)) Can) :
    ∀ v ∈ rho.honest, ∀ w ∈ rho.honest,
      let n := actionReadAt S rho v q
      Protocol.sgVote (actionAttestationAt S rho w (q - 1)).erase ∈
        DecoupledConsensusModel.Protocol.interpretedInputs n.st.core.toHealing.gradeView
          n.st.core.F S.hc.η_SG q (allPhasesCutoff S.E S.hc q) w →
      ∀ u ∈ DecoupledConsensusModel.Protocol.interpretedInputs n.st.core.toHealing.gradeView
          n.st.core.F S.hc.η_SG q (allPhasesCutoff S.E S.hc q) w,
        (∀ x ∈ DecoupledConsensusModel.Protocol.interpretedInputs
            n.st.core.toHealing.gradeView n.st.core.F S.hc.η_SG q
            (allPhasesCutoff S.E S.hc q) w, x.round ≤ u.round) →
        ∀ head : Block V, u.confirmed = some head.root →
          Block.find? n.st.core.toHealing.gradeView.T head.root = some head →
          Block.Preceq head Can := by
  intro v hv w hw n hprev u hu hmax head hconf hfind
  have hraw : u ∈ DecoupledConsensusModel.Protocol.rawInputs
      (actionReadAt S rho v q).st.core.toHealing.gradeView
      S.hc.η_SG q (allPhasesCutoff S.E S.hc q) w :=
    (Finset.mem_filter.mp hu).1
  have hfind' : Block.find?
      (actionReadAt S rho v q).st.core.toHealing.gradeView.T head.root
        = some head := hfind
  obtain ⟨hwindow, hhead⟩ :=
    honestWindowInput_head_eq_actionCarrier S adm hhor hv hw hraw hconf hfind'
  have hge : q - 1 ≤ u.round := by
    have hle := hmax _ hprev
    have hround : (Protocol.sgVote
        (actionAttestationAt S rho w (q - 1)).erase).round = q - 1 := by
      rw [NamedOutageClosure.sgVote_round]
      exact (actionAttestationAt_shape S rho w (q - 1)).2.1
    rwa [hround] at hle
  have hlt : u.round < q := (NamedOutageClosure.window_bounds hwindow).2
  have hround : u.round = q - 1 :=
    Nat.le_antisymm (Nat.le_sub_one_of_lt hlt) hge
  rw [hhead, hround]
  exact hcarriers w hw

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
