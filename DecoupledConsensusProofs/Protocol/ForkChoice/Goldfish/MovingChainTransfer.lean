module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.MovingChainSlot
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SGOpeningFrozenSuffix

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Moving-frontier proposal transfer

This module compares the honest proposer read with every honest voter read in
the same slot. A crossing row visible at the later voter read was emitted
before the proposal event. The moving event history therefore puts its source
below the proposal parent. This prevents more than one unit of numeric
frontier growth between the two reads.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Internal.NamedRecoveryRead
open Protocol

variable {V : Type} [DecidableEq V] [Fintype V]








/-- Strict event times give strict event indices. This local copy keeps the
transfer module independent of the current dispatch object-file version. -/
private theorem movingEventIndex_lt_of_eventTime_lt
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    {i j : Nat} {e f : Event V}
    (hi : rho.events[i]? = some e)
    (hj : rho.events[j]? = some f)
    (ht : e.time < f.time) :
    i < j := by
  by_contra hnot
  have hji : j ≤ i := Nat.le_of_not_gt hnot
  rcases lt_or_eq_of_le hji with hji | rfl
  · have hkey := Proofs.Optimistic.key_le_of_index_lt S sch hji hj hi
    have htime := Proofs.Bridges.time_le_of_key_le hkey
    exact (not_le_of_gt ht) htime
  · have heq : e = f := Option.some.inj (hi.symm.trans hj)
    exact lt_irrefl _ (by simpa only [heq] using ht)

private theorem movingFrontierChainStateN_transfer_endpoint_mono
    {S : Setup V} {rho : Run V} {t1 : Time} {M0 : Height}
    {n0 i : Nat} {End : Nat → Block V}
    (h : MovingFrontierChainStateN S rho t1 M0 n0 i End)
    {j k : Nat} (hj : n0 ≤ j) (hjk : j ≤ k) (hki : k ≤ i) :
    Block.Preceq (End j) (End k) := by
  induction hjk with
  | refl => exact Block.preceq_self _
  | @step k hjk ih =>
      exact Block.preceq_trans (ih (Nat.le_trans (Nat.le_succ k) hki))
        (h.endpointMono k (hj.trans hjk) (Nat.lt_of_succ_le hki))

private theorem movingFrontierChainStateN_transfer_named_preceq_cases_endpoint
    {A B : NamedBlock V} (h : NamedBlock.Preceq A B) :
    A = B ∨ NamedBlock.Preceq A B.parent := by
  cases B with
  | genesis =>
      left
      simpa only [NamedBlock.Preceq, NamedBlock.preceq, decide_eq_true_eq] using h
  | node parent slot root votes support rows proposer =>
      simpa only [NamedBlock.Preceq, NamedBlock.preceq, NamedBlock.parent,
        Bool.or_eq_true, decide_eq_true_eq] using h

private theorem movingFrontierChainStateN_transfer_named_chain_attestations_own
    {A : NamedBlock V} {a : NamedAttestation V}
    (ha : a ∈ A.attestations) :
    a ∈ Protocol.named_chain_attestations A := by
  cases A with
  | genesis => simp [NamedBlock.attestations] at ha
  | node p s r gv gsv rows proposer =>
      exact Finset.mem_union_right _ (List.mem_toFinset.mpr ha)

private theorem movingFrontierChainStateN_transfer_named_chain_attestations_mono
    {A B : NamedBlock V} (hAB : NamedBlock.Preceq A B) :
    Protocol.named_chain_attestations A ⊆
      Protocol.named_chain_attestations B := by
  induction B with
  | genesis =>
      have hA : A = .genesis := by
        simpa only [NamedBlock.Preceq, NamedBlock.preceq, decide_eq_true_eq] using hAB
      subst hA
      exact Finset.Subset.refl _
  | node p s r gv sup rows pr ih =>
      rcases movingFrontierChainStateN_transfer_named_preceq_cases_endpoint hAB with
        rfl | hAp
      · exact Finset.Subset.refl _
      · exact (ih hAp).trans Finset.subset_union_left

private theorem movingFrontierChainStateN_transfer_named_chain_attestations_of_carrier
    {carrier D : NamedBlock V} {a : NamedAttestation V}
    (hcarrier : NamedBlock.Preceq carrier D)
    (ha : a ∈ carrier.attestations) :
    a ∈ Protocol.named_chain_attestations D :=
  movingFrontierChainStateN_transfer_named_chain_attestations_mono hcarrier
    (movingFrontierChainStateN_transfer_named_chain_attestations_own ha)

private theorem movingFrontierChainStateN_voteFrontierFloorAtProposal
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {t1 : Time} {M0 : Height} {n0 k : Nat} {End : Nat → Block V}
    (h : MovingFrontierChainStateN S rho t1 M0 n0 k End)
    {s : Slot}
    (hsep : ∀ q : Round, S.a q < Protocol.vote_time S.E s →
      S.a q < Protocol.proposal_time S.E s)
    (hcursor : strictEventIndex rho (Protocol.proposal_time S.E s) ≤ k)
    {v : V} (_hv : v ∈ rho.honest)
    {E : NamedBlock V} (hE : E.erase = End k) (hErun : RunBlock S rho E) :
    (rho.storeBeforeTime S v (Protocol.vote_time S.E s)).core.h_max - 1 ≤
      (Protocol.derive_named S.E S.cfg E).h := by
  let targetPre := rho.storeBeforeTime S v (Protocol.vote_time S.E s)
  change targetPre.core.h_max - 1 ≤
    (Protocol.derive_named S.E S.cfg E).h
  by_contra hnot
  have hhigh : (Protocol.derive_named S.E S.cfg E).h <
      targetPre.core.h_max - 1 := Nat.lt_of_not_ge hnot
  have hlarge : 1 < targetPre.core.h_max :=
    Nat.sub_pos_iff_lt.mp ((Nat.zero_le _).trans_lt hhigh)
  have hmajority : HonestWeightMajority S rho.honest :=
    AlignedRoundLemmas.honestWeightMajority_of_belowOneThird (S := S) hfb
  obtain ⟨_W, _hWT, _Q, _X, a, ta, _hmaxW, _hQ, _hXW, _haW,
      haHon, hemit, hta, haHeight⟩ :=
    Protocol.frontierQuorumWitness_stateBeforeTime
      S adm hmajority (by simpa only [targetPre] using hlarge)
  obtain ⟨j, hjevent, hja⟩ := hemit
  have hshape := Proofs.Optimistic.emits_attest_shape S ⟨j, hjevent, hja⟩
  have haction : S.a a.round < Protocol.vote_time S.E s := by
    simpa only [← hshape.2] using hta
  have htaProposal : ta < Protocol.proposal_time S.E s := by
    rw [hshape.2]
    exact hsep a.round haction
  have hjk : j < k :=
    (emission_index_lt_beforeTime_prefix S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hjevent htaProposal).trans_le
      hcursor
  by_cases hj0 : j < n0
  · exact (not_le_of_gt hhigh)
      (h.oldRow_le_endpointHeight_named S adm haHon hjevent hja hj0
        (by simpa only [targetPre] using haHeight) hE hErun)
  · have hn0j : n0 ≤ j := Nat.le_of_not_gt hj0
    obtain ⟨G, hGrun, hGheight, hGnext⟩ :=
      (h.outputs j hn0j hjk).height_gate_sources
        haHon hjevent hja (targetPre.core.h_max - 1)
          (by simpa only [targetPre] using haHeight)
    obtain ⟨Enext, hEnext, hEnextrun⟩ :=
      h.endpointRun (j + 1) (hn0j.trans (Nat.le_succ j))
        (Nat.succ_le_iff.mpr hjk)
    have hGnextNamed : NamedBlock.Preceq G Enext :=
      Protocol.namedPreceq_of_runBlock_erase_preceq adm hGrun hEnextrun (by
        simpa only [hEnext] using hGnext)
    have hnextEnd : Block.Preceq (End (j + 1)) (End k) :=
      movingFrontierChainStateN_transfer_endpoint_mono h
        (hn0j.trans (Nat.le_succ j))
        (Nat.succ_le_iff.mpr hjk) (Nat.le_refl k)
    have hEnextE : NamedBlock.Preceq Enext E :=
      Protocol.namedPreceq_of_runBlock_erase_preceq adm hEnextrun hErun (by
        simpa only [hEnext, hE] using hnextEnd)
    have hrowEnd : targetPre.core.h_max - 1 ≤
        (Protocol.derive_named S.E S.cfg E).h := by
      calc
        targetPre.core.h_max - 1 =
            (Protocol.derive_named S.E S.cfg G).h := hGheight.symm
        _ ≤ (Protocol.derive_named S.E S.cfg Enext).h :=
          Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hGnextNamed
        _ ≤ (Protocol.derive_named S.E S.cfg E).h :=
          Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hEnextE
    exact (not_le_of_gt hhigh) hrowEnd

theorem MovingFrontierChainStateN.voteFrontier_sub_one_le_endpointAtProposal_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {t1 : Time} {M0 : Height} {n0 i : Nat} {End : Nat → Block V}
    (h : MovingFrontierChainStateN S rho t1 M0 n0 i End)
    {s : Slot}
    (hevent : rho.events[i]? = some
      (Event.tick (S.E.proposer s) (Protocol.proposal_time S.E s)))
    {v : V} (hv : v ∈ rho.honest)
    {E : NamedBlock V} (hE : E.erase = End i) (hErun : RunBlock S rho E) :
    (voteDutyRead S rho v s).st.core.h_max - 1 ≤
      (Protocol.derive_named S.E S.cfg E).h := by
  have hcursor : strictEventIndex rho (Protocol.proposal_time S.E s) ≤ i :=
    filterBefore_length_le_tickIndex S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hevent (le_refl _)
  have hfloor := movingFrontierChainStateN_voteFrontierFloorAtProposal
    S adm hfb h (fun q hq =>
      Protocol.action_time_lt_proposal_of_lt_vote S hq)
      hcursor hv hE hErun
  simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
    NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using hfloor

private theorem movingFrontierChainStateN_transfer_gateOnRoot_preceq_of_boundary
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {t1 : Time} {M0 : Height} {n0 i : Nat} {End : Nat → Block V}
    (h : MovingFrontierChainStateN S rho t1 M0 n0 i End)
    {st : Protocol.NamedStore V} {C J : NamedBlock V}
    (hhj : (Protocol.derive_named S.E S.cfg C).h_j = st.core.h_j)
    (hJ : (Protocol.derive_named S.E S.cfg C).J = st.core.J)
    (hJrun : RunBlock S rho J) (hJerase : J.erase = st.core.J)
    (hfloorM : M0 ≤ st.core.h_max)
    (hgate : st.core.h_max = st.core.h_j + 1)
    (hrow : st.core.h_j ≠ 0 →
      ∃ (a : NamedAttestation V) (ta : Time) (j : Nat),
        a.val_index ∈ rho.honest ∧
        rho.events[j]? = some (Event.tick a.val_index ta) ∧
        Object.attest a ∈ NamedRun.emittedAt S rho j a.val_index ta ∧
        a.height_pair = NamedHeightPair.vote st.core.h_j st.core.J.root false ∧
        j < i) :
    Block.Preceq (Protocol.get_fg_root st.core.toHealing.toFG) (End i) := by
  have hrootEq : Protocol.get_fg_root st.core.toHealing.toFG = J.erase := by
    calc
      Protocol.get_fg_root st.core.toHealing.toFG = st.core.J := by
        simp only [Protocol.get_fg_root, Protocol.Store.toHealing, if_pos hgate]
      _ = J.erase := hJerase.symm
  rw [hrootEq]
  by_cases hz : st.core.h_j = 0
  · have hCJ : (Protocol.derive_named S.E S.cfg C).J = Block.genesis :=
      NamedJustificationCertificates.justified_zero_is_genesis S.E S.cfg C (by
        rw [hhj]
        exact hz)
    have hJgen : J.erase = Block.genesis :=
      hJerase.trans (hJ.symm.trans hCJ)
    rw [hJgen]
    exact Protocol.preceq_genesis (End i)
  · obtain ⟨a, ta, j, haHonest, hjevent, hja, haTarget, hji⟩ := hrow hz
    have hhjLow : M0 - 1 ≤ st.core.h_j := by
      have hM : M0 ≤ st.core.h_j + 1 := hfloorM.trans_eq hgate
      apply Nat.sub_le_iff_le_add.mpr
      simpa only [Nat.add_comm] using hM
    by_cases hj0 : j < n0
    · have htaLt : ta < t1 := by
        have hlt : j < strictEventIndex rho t1 := by
          rw [← h.historyStart]
          exact hj0
        simpa only [Event.time] using
          time_lt_of_index_lt_strictEventIndex S
            adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hlt hjevent
      have hJn0 : Block.Preceq J.erase (End n0) :=
        h.boundaryTargets a ta haHonest ⟨j, hjevent, hja⟩ htaLt
          st.core.h_j st.core.J.root hhjLow haTarget J hJrun (by rw [hJerase])
      exact Block.preceq_trans hJn0
        (movingFrontierChainStateN_transfer_endpoint_mono h
          (Nat.le_refl n0) h.start_le (Nat.le_refl i))
    · have hn0j : n0 ≤ j := Nat.le_of_not_gt hj0
      have hJnext : Block.Preceq J.erase (End (j + 1)) :=
        (h.outputs j hn0j hji).targets haHonest hjevent hja
          st.core.h_j st.core.J.root haTarget J hJrun (by rw [hJerase])
      exact Block.preceq_trans hJnext
        (movingFrontierChainStateN_transfer_endpoint_mono h
          (hn0j.trans (Nat.le_succ j))
          (Nat.succ_le_iff.mpr hji) (Nat.le_refl i))
theorem MovingFrontierChainStateN.voteRoot_preceq_endpointAtProposal_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {t1 : Time} {M0 : Height} {n0 i : Nat} {End : Nat → Block V}
    (h : MovingFrontierChainStateN S rho t1 M0 n0 i End)
    {s : Slot}
    (hevent : rho.events[i]? = some
      (Event.tick (S.E.proposer s) (Protocol.proposal_time S.E s)))
    {v : V} (hv : v ∈ rho.honest)
    (hstart : t1 ≤ Protocol.vote_time S.E s)
    {E : NamedBlock V} (hE : E.erase = End i) (hErun : RunBlock S rho E) :
    Block.Preceq
      (Protocol.get_fg_root
        (voteDutyRead S rho v s).st.core.toHealing.toFG) E.erase := by
  let pre := rho.storeBeforeTime S v (Protocol.vote_time S.E s)
  have hbelow : pre.core.h_j < pre.core.h_max :=
    NamedJustificationBound.justificationBelowMax_stateBeforeTime S rho
      (Protocol.vote_time S.E s) v
  have hmajority : HonestWeightMajority S rho.honest :=
    AlignedRoundLemmas.honestWeightMajority_of_belowOneThird (S := S) hfb
  have hsb : SlashableBound S rho :=
    slashableBound_of_admissible_belowOneThird S adm hfb
  have hcursor : strictEventIndex rho (Protocol.proposal_time S.E s) ≤ i :=
    filterBefore_length_le_tickIndex S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hevent (le_refl _)
  have hendFloor : pre.core.h_max - 1 ≤
      (Protocol.derive_named S.E S.cfg E).h := by
    simpa only [pre] using
      movingFrontierChainStateN_voteFrontierFloorAtProposal S adm hfb h
        (fun q hq => Protocol.action_time_lt_proposal_of_lt_vote S hq)
        hcursor hv hE hErun
  have hn0 : n0 ≤ strictEventIndex rho (Protocol.vote_time S.E s) := by
    rw [h.historyStart]
    exact strictEventIndex_mono rho hstart
  have hfloorM : M0 ≤ pre.core.h_max := by
    have hfl := h.frontierFloor v hv (strictEventIndex rho
      (Protocol.vote_time S.E s)) hn0
    rw [← storeBeforeTime_eq_stateBefore_strictEventIndex
      S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed v
      (Protocol.vote_time S.E s)] at hfl
    simpa only [pre] using hfl
  by_cases hgate : pre.core.h_max = pre.core.h_j + 1
  · obtain ⟨C, hCbody, hJ, hhj⟩ :=
      Proofs.Bridges.storeJustificationOnChain_stateBeforeTime S rho
        (Protocol.vote_time S.E s) v
    have hCbody' : C ∈ pre.bodies := by simpa only [pre] using hCbody
    have hJpre : (Protocol.derive_named S.E S.cfg C).J = pre.core.J := by
      simpa only [pre, Run.storeBeforeTime] using hJ
    have hhjpre : (Protocol.derive_named S.E S.cfg C).h_j =
        pre.core.h_j := by
      simpa only [pre, Run.storeBeforeTime] using hhj
    have hCbodyN : C ∈
        (rho.stateBefore S (strictEventIndex rho
          (Protocol.vote_time S.E s)) v).st.bodies := by
      rw [← storeBeforeTime_eq_stateBefore_strictEventIndex
        S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed v
        (Protocol.vote_time S.E s)]
      exact hCbody'
    have hCrun : RunBlock S rho C :=
      Proofs.Bridges.runBlock_of_stateBefore_mem S hv hCbodyN
    have hJmem : pre.core.J ∈ pre.core.T :=
      Proofs.NamedStoreBridge.justifiedInTree_stateBeforeTime S rho
        (Protocol.vote_time S.E s) v
    obtain ⟨J, hJbody, hJerase⟩ :=
      Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho
        (Protocol.vote_time S.E s) v hJmem
    have hJbodyN : J ∈
        (rho.stateBefore S (strictEventIndex rho
          (Protocol.vote_time S.E s)) v).st.bodies := by
      rw [← storeBeforeTime_eq_stateBefore_strictEventIndex
        S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed v
        (Protocol.vote_time S.E s)]
      simpa only [pre] using hJbody
    have hJrun : RunBlock S rho J :=
      Proofs.Bridges.runBlock_of_stateBefore_mem S hv hJbodyN
    have hrow : pre.core.h_j ≠ 0 →
        ∃ (a : NamedAttestation V) (ta : Time) (j : Nat),
          a.val_index ∈ rho.honest ∧
          rho.events[j]? = some (Event.tick a.val_index ta) ∧
          Object.attest a ∈ NamedRun.emittedAt S rho j a.val_index ta ∧
          a.height_pair = NamedHeightPair.vote pre.core.h_j pre.core.J.root false ∧
          j < i := by
      intro hz
      have hhjNe : (Protocol.derive_named S.E S.cfg C).h_j ≠ 0 := by
        rw [hhj]
        exact hz
      obtain ⟨J', hJD, hJeraseC, Q, hQ, hwitness⟩ :=
        NamedJustificationCertificates.justification_certificate S.E S.cfg C hhjNe
      obtain ⟨signer, hsignerQ, hsignerHonest⟩ :=
        HonestWeightMajority.exists_honest_member_of_quorum hmajority hQ
      obtain ⟨carrier, a, hcarrier, ha, haSigner, haPair⟩ :=
        hwitness signer hsignerQ
      have haHonest : a.val_index ∈ rho.honest := by
        rw [haSigner]
        exact hsignerHonest
      have haChain : a ∈ Protocol.named_chain_attestations C :=
        movingFrontierChainStateN_transfer_named_chain_attestations_of_carrier
          hcarrier ha
      have hrootJ : J'.root = pre.core.J.root := by
        rw [← Proofs.NamedWire.erase_root J', hJeraseC, hJpre]
      have haTarget : a.height_pair =
          NamedHeightPair.vote pre.core.h_j pre.core.J.root false := by
        rw [← hhjpre, ← hrootJ]
        exact haPair
      obtain ⟨j, ta, hj, hjevent, hja, _hemit⟩ :=
        honestCarriedAttestation_emittedBeforeIndex S adm hCbodyN haChain haHonest
      have hta : ta < Protocol.vote_time S.E s :=
        time_lt_of_index_lt_strictEventIndex S
          adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hj hjevent
      have hshape := Proofs.Optimistic.emits_attest_shape S
        (⟨j, hjevent, hja⟩ : rho.emits S a.val_index (Object.attest a) ta)
      have haction : S.a a.round < Protocol.vote_time S.E s := by
        simpa only [← hshape.2] using hta
      have htaProposal : ta < Protocol.proposal_time S.E s := by
        rw [hshape.2]
        exact Protocol.action_time_lt_proposal_of_lt_vote S haction
      have hjk : j < i :=
        (emission_index_lt_beforeTime_prefix S
          adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hjevent htaProposal).trans_le
          hcursor
      exact ⟨a, ta, j, haHonest, hjevent, hja, haTarget, hjk⟩
    have hgateRoot : Block.Preceq
        (Protocol.get_fg_root pre.core.toHealing.toFG) (End i) :=
      movingFrontierChainStateN_transfer_gateOnRoot_preceq_of_boundary
        (S := S) (rho := rho) (adm := adm) (t1 := t1) (M0 := M0)
        (n0 := n0) (i := i) (End := End) h hhjpre hJpre hJrun hJerase
        hfloorM hgate hrow
    simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      pre, hE] using hgateRoot
  · obtain ⟨C, hCbody, hCF, _hCheight⟩ :=
      Proofs.Bridges.storeFinalizationOnChain_stateBeforeTime S rho
        (Protocol.vote_time S.E s) v
    have hCbody' : C ∈ pre.bodies := by simpa only [pre] using hCbody
    have hCbodyN : C ∈
        (rho.stateBefore S (strictEventIndex rho
          (Protocol.vote_time S.E s)) v).st.bodies := by
      rw [← storeBeforeTime_eq_stateBefore_strictEventIndex
        S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed v
        (Protocol.vote_time S.E s)]
      exact hCbody'
    have hCrun : RunBlock S rho C :=
      Proofs.Bridges.runBlock_of_stateBefore_mem S hv hCbodyN
    have hgateOff : pre.core.h_j + 2 ≤ pre.core.h_max := by
      have hsucc : pre.core.h_j + 1 ≤ pre.core.h_max :=
        Nat.succ_le_iff.mpr hbelow
      have hstrict : pre.core.h_j + 1 < pre.core.h_max :=
        lt_of_le_of_ne hsucc (fun heq => hgate heq.symm)
      simpa only [Nat.add_assoc] using Nat.succ_le_iff.mpr hstrict
    have hhjlt : pre.core.h_j < pre.core.h_max - 1 := by
      rw [Nat.lt_sub_iff_add_lt]
      exact Nat.lt_of_succ_le (by simpa only [Nat.add_assoc] using hgateOff)
    have hnoHigh : Internal.NamedNoHighJustifications S.E S.cfg pre :=
      NamedJustificationBound.noHighJustifications_stateBeforeTime S rho
        (Protocol.vote_time S.E s) v
    have hcrossed : (Protocol.derive_named S.E S.cfg C).h_F <
        (Protocol.derive_named S.E S.cfg E).h := by
      calc
        (Protocol.derive_named S.E S.cfg C).h_F ≤
            (Protocol.derive_named S.E S.cfg C).h_j :=
          (Proofs.NamedStoreRoots.chainOrder_derive_named S.E S.cfg C).heights_ordered
        _ ≤ pre.core.h_j := hnoHigh C hCbody'
        _ < pre.core.h_max - 1 := hhjlt
        _ ≤ (Protocol.derive_named S.E S.cfg E).h := hendFloor
    have hFEnd : Block.Preceq pre.core.F E.erase := by
      have hpre := NamedFinalizationBridge.finalized_preceq_of_height_lt
        S rho E C hsb adm.toNamedRootCollisionFree hErun hCrun hcrossed
      simpa only [hCF] using hpre
    have hroot : Block.Preceq
        (Protocol.get_fg_root pre.core.toHealing.toFG) E.erase := by
      change (if pre.core.h_max = pre.core.h_j + 1 then pre.core.J else pre.core.F) ⪯
        E.erase
      rw [if_neg hgate]
      exact hFEnd
    simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      pre, hE] using hroot


/-
/-- At an honest proposal event, every later honest voter frontier boundary
is already below the current moving endpoint. A frontier-crossing row at the
vote read was emitted before the proposal event. The event-indexed output
history therefore puts its exact-height source on the endpoint chain. -/
theorem MovingFrontierChainState.voteFrontier_sub_one_le_endpointAtProposal
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hfb: BelowOneThird S rho.honest)
    {t1: Time} {M0: Height} {n0 i: Nat} {End: Nat → Block V}
    (h: MovingFrontierChainState S rho t1 M0 n0 i End)
    {s: Slot}
    (hevent: rho.events[i]? = some
      (Event.tick (S.E.proposer s) (Protocol.proposal_time S.E s)))
    {v: V} (_hv: v ∈ rho.honest):
    (Proofs.Optimistic.voteDutyStore S rho v s).h_max - 1 ≤
      (derived_state S.E S.cfg (End i)).h:= by
  let targetPre:= rho.storeBeforeTime S v (Protocol.vote_time S.E s)
  let target:= Proofs.Optimistic.voteDutyStore S rho v s
  change target.h_max - 1 ≤ (derived_state S.E S.cfg (End i)).h
  by_contra hnot
  have hhigh: (derived_state S.E S.cfg (End i)).h <
      targetPre.h_max - 1:= by
    simpa only [target, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore, targetPre] using Nat.lt_of_not_ge hnot
  have hlarge: 1 < targetPre.h_max:=
    Nat.sub_pos_iff_lt.mp ((Nat.zero_le _).trans_lt hhigh)
  have hmajority: HonestWeightMajority S rho.honest:=
    AlignedRoundLemmas.honestWeightMajority_of_belowOneThird (S:= S) hfb
  obtain ⟨_W, _hWT, _Q, _X, a, ta, _hmaxW, _hQ, _hXW, _haW,
      haHon, hemit, hta, haHeight⟩:=
    Protocol.frontierQuorumWitness_stateBeforeTime
      S adm hmajority (by simpa only [targetPre] using hlarge)
  obtain ⟨j, hjevent, hja⟩:= hemit
  have hshape:= Proofs.Optimistic.emits_attest_shape S ⟨j, hjevent, hja⟩
  have hactionVote: S.a a.round < Protocol.vote_time S.E s:= by
    simpa only [← hshape.2] using hta
  have htaProposal: ta < Protocol.proposal_time S.E s:= by
    calc
      ta = S.a a.round:= hshape.2
      _ < Protocol.proposal_time S.E s:=
        action_time_lt_proposal_of_lt_vote S hactionVote
  have hji: j < i:=
    movingEventIndex_lt_of_eventTime_lt S adm.toScheduleWellFormed
      hjevent hevent (by simpa only [Event.time] using htaProposal)
  by_cases hj0: j < n0
  · exact (not_le_of_gt hhigh)
      (h.oldRow_le_endpointHeight S haHon hjevent hja hj0
        (by simpa only [targetPre] using haHeight))
  · have hn0j: n0 ≤ j:= Nat.le_of_not_gt hj0
    obtain ⟨G, _hGrun, hGheight, hGnext⟩:=
      (h.outputs j hn0j hji).height_gate_sources
        haHon hjevent hja (targetPre.h_max - 1)
          (by simpa only [targetPre] using haHeight)
    have hnextEnd: Block.Preceq (End (j + 1)) (End i):=
      h.endpoint_mono (hn0j.trans (Nat.le_succ j))
        (Nat.succ_le_iff.mpr hji) (Nat.le_refl i)
    have hrowEnd: targetPre.h_max - 1 ≤
        (derived_state S.E S.cfg (End i)).h:= by
      calc
        targetPre.h_max - 1 = (derived_state S.E S.cfg G).h:=
          hGheight.symm
        _ ≤ (derived_state S.E S.cfg (End (j + 1))).h:=
          Protocol.derived_h_mono S.E S.cfg hGnext
        _ ≤ (derived_state S.E S.cfg (End i)).h:=
          Protocol.derived_h_mono S.E S.cfg hnextEnd
    exact (not_le_of_gt hhigh) hrowEnd
-/


/-
/-- At a later vote read in the same slot, the selected FG root is still
below the endpoint that preceded the honest proposal. A gate-on root has an
honest target row. Since no action instant lies between the proposal and vote
instants, that row was emitted before the proposal event and is covered by the
moving output history. The gate-off branch uses the voter frontier floor and
accountable finality crossing. -/
theorem MovingFrontierChainState.voteRoot_preceq_endpointAtProposal
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hfb: BelowOneThird S rho.honest)
    {t1: Time} {M0: Height} {n0 i: Nat} {End: Nat → Block V}
    (h: MovingFrontierChainState S rho t1 M0 n0 i End)
    {s: Slot}
    (hevent: rho.events[i]? = some
      (Event.tick (S.E.proposer s) (Protocol.proposal_time S.E s)))
    {v: V} (hv: v ∈ rho.honest)
    (hstart: t1 ≤ Protocol.vote_time S.E s):
    Block.Preceq
      (Protocol.get_fg_root
        (Proofs.Optimistic.voteDutyStore S rho v s).toHealing.toFG) (End i):= by
  let st:= Proofs.Optimistic.voteDutyStore S rho v s
  let pre:= rho.storeBeforeTime S v (Protocol.vote_time S.E s)
  have hdep: DepReachableStore S.E S.hc S.cfg (S.node v) pre:= by
    simpa only [pre, Run.storeBeforeTime] using
      (Proofs.Bridges.depReachable_stateBeforeTime S adm.toScheduleWellFormed
        adm.toDeliveryWellFormed (Protocol.vote_time S.E s) v)
  have hbelow: pre.h_j < pre.h_max:=
    FixedHeightRootCore.justificationBelowMax_depReachable
      S.E S.hc S.cfg (S.node v) hdep
  have hmajority: HonestWeightMajority S rho.honest:=
    AlignedRoundLemmas.honestWeightMajority_of_belowOneThird (S:= S) hfb
  have hsb: SlashableBound S rho:=
    slashableBound_of_admissible_belowOneThird S adm hfb
  have hendFloor: pre.h_max - 1 ≤
      (derived_state S.E S.cfg (End i)).h:= by
    simpa only [st, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore, pre] using
        h.voteFrontier_sub_one_le_endpointAtProposal S adm hfb hevent hv
  have hEndRun: RunBlock S rho (End i):=
    h.endpointRun i h.start_le (Nat.le_refl i)
  have hfloorM: M0 ≤ pre.h_max:= by
    have hn0: n0 ≤ strictEventIndex rho (Protocol.vote_time S.E s):= by
      rw [h.historyStart]
      exact strictEventIndex_mono rho hstart
    have hfl:= h.frontierFloor v hv
      (strictEventIndex rho (Protocol.vote_time S.E s)) hn0
    rw [← storeBeforeTime_eq_stateBefore_strictEventIndex
      S adm.toScheduleWellFormed v (Protocol.vote_time S.E s)] at hfl
    simpa only [pre] using hfl
  by_cases hgate: pre.h_max = pre.h_j + 1
  · obtain ⟨C, hC, hhj, hJ⟩:=
      (Proofs.Bridges.provenance_depReachable
        S.E S.hc S.cfg (S.node v) hdep).2
    have hJmem: pre.J ∈ pre.T:=
      Proofs.Records.justifiedInTree_depReachable
        S.E S.hc S.cfg (S.node v) pre hdep
    obtain ⟨k, hk, -⟩:= Proofs.Bridges.stateBeforeTime_eq_stateBefore
      S adm.toScheduleWellFormed (Protocol.vote_time S.E s)
    have hJrun: RunBlock S rho pre.J:= by
      apply Proofs.Bridges.runBlock_of_stateBefore_mem S hv (i:= k)
      simpa only [pre, Run.storeBeforeTime, hk] using hJmem
    have hres: Block.Preceq
        (Protocol.get_fg_root pre.toHealing.toFG) (End i):= by
      refine h.gateOnRoot_preceq_of_boundary S adm hhj hJ hJrun
        hfloorM hgate ?_
      intro hz
      have hhjNe: (derived_state S.E S.cfg C).h_j ≠ 0:= by
        rw [hhj]
        exact hz
      obtain ⟨Q, hQ, hwit⟩:=
        AlignedRoundLemmas.justification_certificate S.E S.cfg C hhjNe
      obtain ⟨signer, hsignerQ, hsignerHonest⟩:=
        HonestWeightMajority.exists_honest_member_of_quorum hmajority hQ
      obtain ⟨a, haC, haSigner, haPair⟩:= hwit signer hsignerQ
      have haHonest: a.val_index ∈ rho.honest:= by
        rw [haSigner]
        exact hsignerHonest
      have haTarget:
          a.height_pair = HeightPair.target pre.h_j pre.J.root:= by
        rw [← hhj, ← hJ]
        exact haPair
      obtain ⟨ta, hta, hemit⟩:=
        Proofs.Bridges.carriedArePastEmissions_of_admissible
          S adm (Protocol.vote_time S.E s) v hC a haC haHonest
      obtain ⟨j, hjevent, hja⟩:= hemit
      have hshape:= Proofs.Optimistic.emits_attest_shape S
        (⟨j, hjevent, hja⟩: rho.emits S a.val_index (Object.attest a) ta)
      have hactionVote: S.a a.round < Protocol.vote_time S.E s:= by
        simpa only [← hshape.2] using hta
      have htaProposal: _ < Protocol.proposal_time S.E s:=
        action_time_lt_proposal_of_lt_vote S hactionVote
      have hji: j < i:=
        movingEventIndex_lt_of_eventTime_lt S adm.toScheduleWellFormed
          hjevent hevent
          (by simpa only [Event.time, hshape.2] using htaProposal)
      exact ⟨a, ta, j, haHonest, hjevent, hja, haTarget, hji⟩
    simpa only [st, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore, pre] using hres
  · have hgateOff: pre.h_j + 2 ≤ pre.h_max:= by
      have hsucc: pre.h_j + 1 ≤ pre.h_max:= Nat.succ_le_iff.mpr hbelow
      have hstrict: pre.h_j + 1 < pre.h_max:=
        lt_of_le_of_ne hsucc (fun heq => hgate heq.symm)
      simpa only [Nat.add_assoc] using Nat.succ_le_iff.mpr hstrict
    have hhjlt: pre.h_j < pre.h_max - 1:= by
      rw [Nat.lt_sub_iff_add_lt]
      exact Nat.lt_of_succ_le (by simpa only [Nat.add_assoc] using hgateOff)
    have hnoHigh: NoHighJustifications S.E S.cfg pre:=
      FixedHeightRootCore.noHighJustifications_depReachable
        S.E S.hc S.cfg (S.node v) hdep
    obtain ⟨C, hC, hF⟩:=
      Proofs.Bridges.storeFinalizationOnChain_depReachable
        S.E S.hc S.cfg (S.node v) hdep
    obtain ⟨k, hk, -⟩:= Proofs.Bridges.stateBeforeTime_eq_stateBefore
      S adm.toScheduleWellFormed (Protocol.vote_time S.E s)
    have hCrun: RunBlock S rho C:= by
      apply Proofs.Bridges.runBlock_of_stateBefore_mem S hv (i:= k)
      simpa only [pre, Run.storeBeforeTime, hk] using hC
    have hcrossed: (derived_state S.E S.cfg C).h_F <
        (derived_state S.E S.cfg (End i)).h:= by
      calc
        (derived_state S.E S.cfg C).h_F ≤
            (derived_state S.E S.cfg C).h_j:=
          (Protocol.chainOrder_derived_state S.E S.cfg C).heights_ordered
        _ ≤ pre.h_j:= hnoHigh C hC
        _ < pre.h_max - 1:= hhjlt
        _ ≤ (derived_state S.E S.cfg (End i)).h:= hendFloor
    have hFEnd: Block.Preceq pre.F (End i):= by
      have hpre: Block.Preceq (derived_state S.E S.cfg C).F (End i):=
        Protocol.finalized_preceq_of_height_lt hsb hCrun hEndRun
          (adm.toRootCollisionFree.root_injective (End i) C hEndRun hCrun)
          ⟨rfl, rfl⟩ hcrossed
      simpa only [hF] using hpre
    simp only [Protocol.get_fg_root, Protocol.Store.toHealing,
      Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore,
      if_neg (by simpa only [st, Proofs.Optimistic.voteDutyStore,
        Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore, pre] using hgate)]
    exact hFEnd
-/

theorem MovingFrontierChainStateN.root_preceq_endpointAtProposal_beforeVote
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {t1 : Time} {M0 : Height} {n0 i : Nat} {End : Nat → Block V}
    (h : MovingFrontierChainStateN S rho t1 M0 n0 i End)
    {s : Slot}
    (hevent : rho.events[i]? = some
      (Event.tick (S.E.proposer s) (Protocol.proposal_time S.E s)))
    {k : Nat} {e : Event V} (hkevent : rho.events[k]? = some e)
    (hktime : e.time < Protocol.vote_time S.E s)
    {w : V} (hw : w ∈ rho.honest) (hn0k : n0 ≤ k)
    {E : NamedBlock V} (hE : E.erase = End i) (hErun : RunBlock S rho E) :
    Block.Preceq
      (Protocol.get_fg_root
        (rho.stateBefore S k w).st.core.toHealing.toFG) (End i) := by
  let st := (rho.stateBefore S k w).st
  have hmajority : HonestWeightMajority S rho.honest :=
    AlignedRoundLemmas.honestWeightMajority_of_belowOneThird (S := S) hfb
  have hsb : SlashableBound S rho :=
    slashableBound_of_admissible_belowOneThird S adm hfb
  have hemittedBefore : ∀ {B : NamedBlock V} {a : NamedAttestation V},
      B ∈ st.bodies →
      a ∈ Protocol.named_chain_attestations B →
      a.val_index ∈ rho.honest →
      ∃ j : Nat,
        j < i ∧
        rho.events[j]? = some (Event.tick a.val_index (S.a a.round)) ∧
        Object.attest a ∈ NamedRun.emittedAt S rho j a.val_index (S.a a.round) := by
    intro B a hB ha haHon
    obtain ⟨j, ta, hjk, hjevent, hja, hemit⟩ :=
      honestCarriedAttestation_emittedBeforeIndex S adm hB ha haHon
    have hshape := Proofs.Optimistic.emits_attest_shape S hemit
    have hkey := Proofs.Optimistic.key_le_of_index_lt S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hjk hjevent hkevent
    have htaK : ta ≤ e.time := Proofs.Bridges.time_le_of_key_le hkey
    have hactionVote : S.a a.round < Protocol.vote_time S.E s := by
      calc
        S.a a.round = ta := hshape.2.symm
        _ ≤ e.time := htaK
        _ < Protocol.vote_time S.E s := hktime
    have htaProposal : ta < Protocol.proposal_time S.E s := by
      calc
        ta = S.a a.round := hshape.2
        _ < Protocol.proposal_time S.E s :=
          Protocol.action_time_lt_proposal_of_lt_vote S hactionVote
    have hji : j < i :=
      movingEventIndex_lt_of_eventTime_lt S
        adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hjevent hevent (by
          simpa only [Event.time, hshape.2] using htaProposal)
    refine ⟨j, hji, ?_, ?_⟩
    · simpa only [hshape.2] using hjevent
    · simpa only [hshape.2] using hja
  have hkVote : k < strictEventIndex rho (Protocol.vote_time S.E s) := by
    by_contra hnot
    have hlen : (rho.events.filter
        (fun e => decide (e.time < Protocol.vote_time S.E s))).length ≤ k := by
      simpa only [strictEventIndex] using Nat.le_of_not_gt hnot
    have hge := Proofs.Optimistic.le_time_of_index_ge S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hlen hkevent
    exact (not_le_of_gt hktime) hge
  have hmaxMono : (rho.stateBefore S k w).st.core.h_max ≤
      (rho.stateBefore S (strictEventIndex rho
        (Protocol.vote_time S.E s)) w).st.core.h_max :=
    NamedNumericStore.stateBefore_hmax_mono S rho w (Nat.le_of_lt hkVote)
  have hmaxVote :
      (rho.stateBefore S (strictEventIndex rho
        (Protocol.vote_time S.E s)) w).st.core.h_max =
        (voteDutyRead S rho w s).st.core.h_max := by
    simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
      congrArg (fun x : Protocol.NamedStore V => x.core.h_max)
        (storeBeforeTime_eq_stateBefore_strictEventIndex S
          adm.toNamedAdmissibleCore.toNamedScheduleWellFormed w
          (Protocol.vote_time S.E s)).symm
  have hvoteFloor := h.voteFrontier_sub_one_le_endpointAtProposal_named
    S adm hfb hevent hw hE hErun
  have hfrontierFloor : st.core.h_max - 1 ≤
      (Protocol.derive_named S.E S.cfg E).h := by
    calc
      st.core.h_max - 1 ≤
          (rho.stateBefore S (strictEventIndex rho
            (Protocol.vote_time S.E s)) w).st.core.h_max - 1 := by
        simpa only [st] using Nat.sub_le_sub_right hmaxMono 1
      _ = (voteDutyRead S rho w s).st.core.h_max - 1 := by rw [hmaxVote]
      _ ≤ (Protocol.derive_named S.E S.cfg E).h := hvoteFloor
  have hfloorM : M0 ≤ st.core.h_max := by
    simpa only [st] using h.frontierFloor w hw k hn0k
  by_cases hgate : st.core.h_max = st.core.h_j + 1
  · obtain ⟨C, hCbody, hJ, hhj⟩ :=
      Proofs.Bridges.storeJustificationOnChain_stateBefore S rho k w
    have hCbody' : C ∈ st.bodies := by simpa only [st] using hCbody
    have hJpre : (Protocol.derive_named S.E S.cfg C).J = st.core.J := by
      simpa only [st] using hJ
    have hhjpre : (Protocol.derive_named S.E S.cfg C).h_j =
        st.core.h_j := by
      simpa only [st] using hhj
    have hJmem : st.core.J ∈ st.core.T := by
      simpa only [st] using
        Proofs.NamedStoreBridge.justifiedInTree_stateBefore S rho k w
    obtain ⟨J, hJbody, hJerase⟩ :=
      Proofs.NamedStoreBridge.exists_named_of_mem_stateBefore S rho k w hJmem
    have hJrun : RunBlock S rho J :=
      Proofs.Bridges.runBlock_of_stateBefore_mem S hw hJbody
    have hrow : st.core.h_j ≠ 0 →
        ∃ (a : NamedAttestation V) (ta : Time) (j : Nat),
          a.val_index ∈ rho.honest ∧
          rho.events[j]? = some (Event.tick a.val_index ta) ∧
          Object.attest a ∈ NamedRun.emittedAt S rho j a.val_index ta ∧
          a.height_pair = NamedHeightPair.vote st.core.h_j st.core.J.root false ∧
          j < i := by
      intro hz
      have hhjNe : (Protocol.derive_named S.E S.cfg C).h_j ≠ 0 := by
        rw [hhjpre]
        exact hz
      obtain ⟨J', hJD, hJeraseC, Q, hQ, hwitness⟩ :=
        NamedJustificationCertificates.justification_certificate S.E S.cfg C hhjNe
      obtain ⟨signer, hsignerQ, hsignerHonest⟩ :=
        HonestWeightMajority.exists_honest_member_of_quorum hmajority hQ
      obtain ⟨carrier, a, hcarrier, ha, haSigner, haPair⟩ :=
        hwitness signer hsignerQ
      have haHonest : a.val_index ∈ rho.honest := by
        rw [haSigner]
        exact hsignerHonest
      have haChain : a ∈ Protocol.named_chain_attestations C :=
        movingFrontierChainStateN_transfer_named_chain_attestations_of_carrier
          hcarrier ha
      have hrootJ : J'.root = st.core.J.root := by
        rw [← Proofs.NamedWire.erase_root J', hJeraseC, hJpre]
      have haTarget : a.height_pair =
          NamedHeightPair.vote st.core.h_j st.core.J.root false := by
        rw [← hhjpre, ← hrootJ]
        exact haPair
      obtain ⟨j, _hji, hjevent, hja⟩ :=
        hemittedBefore hCbody' haChain haHonest
      exact ⟨a, S.a a.round, j, haHonest, hjevent, hja, haTarget, _hji⟩
    have hroot : Block.Preceq
        (Protocol.get_fg_root st.core.toHealing.toFG) (End i) :=
      movingFrontierChainStateN_transfer_gateOnRoot_preceq_of_boundary
        (S := S) (rho := rho) (adm := adm) (t1 := t1) (M0 := M0)
        (n0 := n0) (i := i) (End := End) h hhjpre hJpre hJrun hJerase
        hfloorM hgate hrow
    simpa only [st, hE] using hroot
  · obtain ⟨C, hCbody, hCF, _hCheight⟩ :=
      Proofs.Bridges.storeFinalizationOnChain_stateBefore S rho k w
    have hCbody' : C ∈ st.bodies := by simpa only [st] using hCbody
    have hCrun : RunBlock S rho C :=
      Proofs.Bridges.runBlock_of_stateBefore_mem S hw hCbody
    have hgateOff : st.core.h_j + 2 ≤ st.core.h_max := by
      have hsucc : st.core.h_j + 1 ≤ st.core.h_max :=
        Nat.succ_le_iff.mpr
          (NamedJustificationBound.justificationBelowMax_stateBefore S rho k w)
      have hstrict : st.core.h_j + 1 < st.core.h_max :=
        lt_of_le_of_ne hsucc (fun heq => hgate heq.symm)
      simpa only [Nat.add_assoc] using Nat.succ_le_iff.mpr hstrict
    have hhjlt : st.core.h_j < st.core.h_max - 1 := by
      rw [Nat.lt_sub_iff_add_lt]
      exact Nat.lt_of_succ_le (by simpa only [Nat.add_assoc] using hgateOff)
    have hnoHigh : Internal.NamedNoHighJustifications S.E S.cfg st := by
      simpa only [st] using
        NamedJustificationBound.noHighJustifications_stateBefore S rho k w
    have hcrossed : (Protocol.derive_named S.E S.cfg C).h_F <
        (Protocol.derive_named S.E S.cfg E).h := by
      calc
        (Protocol.derive_named S.E S.cfg C).h_F ≤
            (Protocol.derive_named S.E S.cfg C).h_j :=
          (Proofs.NamedStoreRoots.chainOrder_derive_named S.E S.cfg C).heights_ordered
        _ ≤ st.core.h_j := hnoHigh C hCbody'
        _ < st.core.h_max - 1 := hhjlt
        _ ≤ (Protocol.derive_named S.E S.cfg E).h := hfrontierFloor
    have hFEnd : Block.Preceq st.core.F E.erase := by
      have hpre := NamedFinalizationBridge.finalized_preceq_of_height_lt
        S rho E C hsb adm.toNamedRootCollisionFree hErun hCrun hcrossed
      simpa only [hCF] using hpre
    have hroot : Block.Preceq
        (Protocol.get_fg_root st.core.toHealing.toFG) E.erase := by
      change (if st.core.h_max = st.core.h_j + 1 then st.core.J else st.core.F) ⪯
        E.erase
      rw [if_neg hgate]
      exact hFEnd
    simpa only [st, hE] using hroot


private theorem movingFrontierChainStateN_transfer_votePathAt_of_candidate
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {w : V} (hw : w ∈ rho.honest) {s : Slot} {C : Block V}
    (hC : C ∈ voterCandidateTreeAt S rho w (s + 1)) :
    ∀ D : Block V,
      Block.Preceq (voterAnchorAt S rho w (s + 1)) D →
      D ≠ voterAnchorAt S rho w (s + 1) → Block.Preceq D C → D ≠ C →
      D ∈ voterCandidateTreeAt S rho w (s + 1) := by
  let duty := voteDutyStore S rho w (s + 1)
  have hCraw : C ∈ Proofs.Optimistic.voter_candidate_tree S.E duty.toHealing := by
    simpa only [voterCandidateTreeAt, Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt, NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock, duty, voteDutyStore] using hC
  have hCfull : C ∈ Protocol.get_filtered_block_tree duty.toHealing.toFG :=
    frozenVoterCandidateTree_subset_filtered S.E duty.toHealing hCraw
  have hCT : C ∈ duty.T :=
    Proofs.Records.get_filtered_block_tree_subset duty.toHealing.toFG hCfull
  have hpc : ParentClosed duty := by
    simpa only [duty, voteDutyStore, Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt, NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock] using
      Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho
        (Protocol.vote_time S.E (s + 1)) w
  have hFJ : Block.Preceq duty.F duty.J := by
    simpa only [duty, voteDutyStore, Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt, NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock] using
      Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime S rho
        (Protocol.vote_time S.E (s + 1)) w
  have hrootAnchor : Block.Preceq
      (Protocol.get_fg_root duty.toHealing.toFG)
      (voterAnchorAt S rho w (s + 1)) := by
    simpa only [duty, voteDutyStore, voterAnchorAt, Internal.PhaseGrades.nodeAnchor,
      Internal.PhaseGrades.nodeRead,
      Internal.NamedRecoveryRead.voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
      fg_root_preceq_get_sg_root_with_frame
        (Internal.NamedRecoveryRead.voteDutyRead S rho w (s + 1)).cache S.E S.hc
        duty.toHealing (S.hc.round_of duty.toHealing.s)
  intro D hAD _hDne hDC _hDneC
  have hDT : D ∈ duty.T :=
    Proofs.Records.mem_of_preceq ((parentClosed_iff duty).mp hpc).2 D C hCT hDC
  have hCprocessed : C ∈ Protocol.voter_processed_block_tree S.E
      duty.toHealing.toFG.toSG.toGoldfishStore duty.toHealing.s := by
    have hCdata := hCraw
    simp only [Proofs.Optimistic.voter_candidate_tree, Protocol.get_filtered_block_tree_from,
      Protocol.viable_tree, Protocol.finalized_descendants,
      Finset.mem_filter] at hCdata
    exact hCdata.1.1.1
  have hDfull : D ∈ Protocol.get_filtered_block_tree duty.toHealing.toFG := by
    apply Proofs.Records.mem_filtered_of_preceq (st := duty.toHealing.toFG)
      hFJ hCfull hDT hDC
    exact Block.preceq_trans hrootAnchor hAD
  have hDprocessed : D ∈ Protocol.voter_processed_block_tree S.E
      duty.toHealing.toFG.toSG.toGoldfishStore duty.toHealing.s := by
    have hDprocessed' := WeakGoldfish.ancestorProcessed_of_voterProcessed
      (S := S) (rho := rho) (w := w) (s := s) (B := C)
      (adm := adm.toNamedAdmissibleCore) hw hCprocessed D hDC
    simpa only [duty] using hDprocessed'
  have hCdata := hCraw
  have hDdata := hDfull
  simp only [Proofs.Optimistic.voter_candidate_tree, Protocol.get_filtered_block_tree,
    Protocol.get_filtered_block_tree_from,
    Protocol.viable_tree, Protocol.finalized_descendants,
    Protocol.viable, Finset.mem_filter, decide_eq_true_eq] at hCdata hDdata
  obtain ⟨W, hWprocessed, hCW, hheight⟩ := hCdata.1.2
  have hDcandidate' : D ∈ Proofs.Optimistic.voter_candidate_tree S.E duty.toHealing := by
    simp only [Proofs.Optimistic.voter_candidate_tree, Protocol.get_filtered_block_tree_from,
      Protocol.viable_tree, Protocol.finalized_descendants,
      Protocol.viable, Finset.mem_filter, decide_eq_true_eq]
    exact ⟨⟨⟨hDprocessed, hDdata.1.1.2⟩, W, hWprocessed,
      Block.preceq_trans hDC hCW, hheight⟩, hDdata.2⟩
  simpa only [voterCandidateTreeAt, Internal.NamedRecoveryRead.voteDutyRead,
    NamedActionReads.confirmationReadAt, NamedActionReads.confirmationReadFrom,
    Protocol.NamedStore.setClock, duty, voteDutyStore] using hDcandidate'


theorem MovingFrontierChainStateN.voteInputsAtVote_of_proposalEvent_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {t1 : Time} {M0 : Height} {n0 i : Nat} {End : Nat → Block V}
    (h : MovingFrontierChainStateN S rho t1 M0 n0 i End)
    {r : Round} {s : Slot}
    (hround : S.hc.round_of (s + 1) = r + 1)
    (ht1 : t1 ≤ S.a r)
    (hpostAction : S.E.t_GST ≤ S.a r)
    (hcut : S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon)
    (hpostVote : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hslotHor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    (hvotes : NamedHonestVotesCone S rho s
      (fun X => Block.Preceq (End i) X))
    (hevent : rho.events[i]? = some
      (Event.tick (S.E.proposer (s + 1))
        (Protocol.proposal_time S.E (s + 1))))
    {w : V} (hw : w ∈ rho.honest)
    (hstart : t1 ≤ Protocol.vote_time S.E (s + 1)) :
    GoldfishConeVoteInputs' S rho s (End i) w ∧
      End i ∈ voterCandidateTreeAt S rho w (s + 1) ∧
      Block.Preceq (voterAnchorAt S rho w (s + 1)) (End i) := by
  obtain ⟨E, hE, hErun⟩ :=
    h.endpointRun i h.start_le (Nat.le_refl i)
  have hmajority : HonestWeightMajority S rho.honest :=
    AlignedRoundLemmas.honestWeightMajority_of_belowOneThird (S := S) hfb
  have hrootPrepared : Block.Preceq
      (Protocol.get_fg_root
        (voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG) (End i) :=
    by
      simpa only [hE] using
        (h.voteRoot_preceq_endpointAtProposal_named S adm hfb hevent hw hstart
          hE hErun)
  have hroot : Block.Preceq
      (Protocol.get_fg_root
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG) (End i) := by
    simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore] using
      hrootPrepared
  have hpositive : 0 < ((S.E.committee s) ∩ rho.honest).card := by
    have hcc := hcom s
    omega
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpositive
  have hxHonest : x ∈ rho.honest := (Finset.mem_inter.mp hx).2
  have hxCommittee : x ∈ S.E.committee s := (Finset.mem_inter.mp hx).1
  obtain ⟨X, hX, hXrun, hXemit⟩ := hvotes x hxHonest hxCommittee
  have hXhead : Proofs.Optimistic.HonestHead S rho s X.erase :=
    ⟨x, hxHonest, hxCommittee, ⟨X, rfl, hXrun⟩, hXemit⟩
  have hprocessedHead := honestHead_voterProcessed_at_nextDuty_of_postHealingCone
    S adm hpostVote hslotHor hvotes hXhead hw hroot
  have hprocessedEnd := WeakGoldfish.ancestorProcessed_of_voterProcessed
    S adm.toNamedAdmissibleCore hw hprocessedHead (End i) hX
  have hmemTarget : End i ∈
      (voteDutyRead S rho w (s + 1)).st.core.T := by
    have hdata := hprocessedEnd
    simp only [Protocol.voter_processed_block_tree, Finset.mem_filter] at hdata
    simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore] using
      hdata.1
  have hmemPre : End i ∈
      (rho.stateBeforeTime S (Protocol.vote_time S.E (s + 1)) w).st.core.T := by
    simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
      hmemTarget
  obtain ⟨E0, hE0body, hE0erase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho
      (Protocol.vote_time S.E (s + 1)) w hmemPre
  have hE0run : RunBlock S rho E0 := by
    obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
      (Protocol.vote_time S.E (s + 1))
    apply Proofs.Bridges.runBlock_of_stateBefore_mem S hw
    simpa only [Run.storeBeforeTime, hn] using hE0body
  have hE0eq : E0 = E := by
    apply adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective
      E0 E hE0run hErun E0 E (Or.inl (Proofs.NamedAncestry.named_self E0))
      (Or.inr (Proofs.NamedAncestry.named_self E))
    rw [← Proofs.NamedWire.erase_root E0, hE0erase, ← Proofs.NamedWire.erase_root E, hE]
  have hEbody : E ∈
      (rho.stateBeforeTime S (Protocol.vote_time S.E (s + 1)) w).st.bodies := by
    rw [← hE0eq]
    exact hE0body
  have hsigma :
      (voteDutyRead S rho w (s + 1)).st.core.σ (End i) =
        Protocol.derive_named S.E S.cfg E := by
    rw [← hE]
    simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
      Proofs.NamedStoreBridge.derivedView_stateBeforeTime S rho
        (Protocol.vote_time S.E (s + 1)) w E hEbody
  have hfloorDerived :
      (voteDutyRead S rho w (s + 1)).st.core.h_max - 1 ≤
        (Protocol.derive_named S.E S.cfg E).h :=
    h.voteFrontier_sub_one_le_endpointAtProposal_named S adm hfb hevent hw
      hE hErun
  have hfloor :
      (voteDutyRead S rho w (s + 1)).st.core.h_max - 1 ≤
        ((voteDutyRead S rho w (s + 1)).st.core.σ (End i)).h := by
    rw [hsigma]
    exact hfloorDerived
  have hFJ : Block.Preceq
      (voteDutyRead S rho w (s + 1)).st.core.F
      (voteDutyRead S rho w (s + 1)).st.core.J := by
    simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
      Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime S rho
        (Protocol.vote_time S.E (s + 1)) w
  have hFEnd : Block.Preceq
      (voteDutyRead S rho w (s + 1)).st.core.F (End i) :=
    Block.preceq_trans
      (Proofs.Records.preceq_get_fg_root_of_F
        (st := (voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG) hFJ)
      hrootPrepared
  have hEndFiltered : End i ∈
      Protocol.get_filtered_block_tree
        (voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG := by
    have hV : End i ∈ Protocol.V_tree
        (voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG := by
      simp only [Protocol.V_tree, Protocol.viable_tree,
        Protocol.finalized_descendants, Protocol.viable,
        Finset.mem_filter, decide_eq_true_eq, Protocol.Store.toHealing]
      exact ⟨⟨hmemTarget, hFEnd⟩, End i, hmemTarget,
        Block.preceq_self _, hfloor⟩
    exact Proofs.Records.mem_filtered_of_mem_V_tree hV hrootPrepared
  have hmax :
      (voteDutyRead S rho w (s + 1)).st.core.h_max ≤
        (Protocol.derive_named S.E S.cfg E).h + 1 :=
    Nat.sub_le_iff_le_add.mp hfloorDerived
  have hcandidate : End i ∈ voterCandidateTreeAt S rho w (s + 1) := by
    simpa only [voterCandidateTreeAt, Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt, NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock, Proofs.Optimistic.voteDutyStore,
      Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore] using
      (namedAncestorCandidate_of_processedDescendant_and_hMax
        (S := S) (rho := rho) (w := w) (s := s) (C := End i) (H := E)
        adm hw (by simpa only [hE] using hprocessedEnd) hErun
          (by simpa only [hE] using (Block.preceq_self (End i))) hEndFiltered hmax)
  have hpath := movingFrontierChainStateN_transfer_votePathAt_of_candidate
    S adm hw hcandidate
  have htargetRoundPos : 0 < S.hc.round_of (s + 1) := by
    rw [hround]
    exact Nat.succ_pos r
  have hdelay : S.a r + S.E.Δ ≤
      Protocol.proposal_time S.E (s + 1) := by
    have hdelay' := Protocol.previous_action_add_delta_le_proposal
      S htargetRoundPos
    simpa only [hround, Nat.add_sub_cancel] using hdelay'
  have hbefore : S.a r < Protocol.proposal_time S.E (s + 1) :=
    (Int.lt_add_of_pos_right (S.a r) S.E.Δ_pos).trans_le hdelay
  have hproposalHor : Protocol.proposal_time S.E (s + 1) ≤ rho.horizon :=
    (le_of_lt (Protocol.proposal_time_lt_vote_time S.E (s + 1))).trans
      ((le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans_eq
        (Protocol.vote_time_succ_add_delta_eq_confirmation_time S.E s) |>.trans
          hslotHor)
  have hactionHor : S.a r ≤ rho.horizon :=
    (le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans
      (hdelay.trans hproposalHor)
  have hupper : ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u r) (End i) := by
    intro u hu
    obtain ⟨j, hj, hout⟩ :=
      honest_emits_exact_actionAttestationAt S adm hu r hactionHor
    have hproposalCursor : strictEventIndex rho
        (Protocol.proposal_time S.E (s + 1)) ≤ i := by
      simpa only [strictEventIndex] using
        filterBefore_length_le_tickIndex S
          adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hevent (le_refl _)
    have hji : j < i :=
      (emission_index_lt_beforeTime_prefix S
        adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hj hbefore).trans_le
        hproposalCursor
    have hn0j : n0 ≤ j := by
      rw [h.historyStart]
      exact filterBefore_length_le_tickIndex S
        adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hj ht1
    exact Block.preceq_trans ((h.sgCarriers j hn0j hji) hu hj hout)
      (movingFrontierChainStateN_transfer_endpoint_mono h
        (hn0j.trans (Nat.le_succ j)) (Nat.succ_le_iff.mpr hji) (Nat.le_refl i))
  have hread : S.hc.Γ_0 S.E.Δ (r + 1) ≤
      Protocol.vote_time S.E (s + 1) := by
    simpa only using Γ_0_le_vote_time_of_round_eq S hround
  have hvoteHor : Protocol.vote_time S.E (s + 1) ≤ rho.horizon := by
    have htime : Protocol.vote_time S.E (s + 1) ≤
        Protocol.confirmation_time S.E s := by
      rw [← Protocol.vote_time_succ_add_delta_eq_confirmation_time S.E s]
      exact le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)
    exact htime.trans hslotHor
  have hanchorEnd : Block.Preceq
      (voterAnchorAt S rho w (s + 1)) (End i) :=
    voterAnchorAt_preceq_of_previousCarriers S adm hfb hround hpostAction hcut
      hvoteHor hupper hw hroot
  have hcompat : Block.compatible
      (voterAnchorAt S rho w (s + 1)) (End i) = true :=
    Block.compatible_of_preceq_common hanchorEnd (Block.preceq_self _)
  have hinputs : GoldfishConeVoteInputs' S rho s (End i) w :=
    { rootSide := Or.inl ⟨hrootPrepared, hcandidate, hpath⟩
      anchor := hcompat }
  exact ⟨hinputs, hcandidate, hanchorEnd⟩

/-! The same vote-input producer with the previous-round carrier ceiling
supplied explicitly. This is the ceiling-side companion of the ordinary
producer above; the explicit ceiling replaces only the reach-back argument. -/
theorem MovingFrontierChainStateN.voteInputsAtVote_of_proposalEvent_named_of_ceiling
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {t1 : Time} {M0 : Height} {n0 i : Nat} {End : Nat → Block V}
    (h : MovingFrontierChainStateN S rho t1 M0 n0 i End)
    {r : Round} {s : Slot}
    (hround : S.hc.round_of (s + 1) = r + 1)
    (hupper : ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u r) (End i))
    (hpostAction : S.E.t_GST ≤ S.a r)
    (hcut : S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon)
    (hpostVote : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hslotHor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    (hvotes : NamedHonestVotesCone S rho s
      (fun X => Block.Preceq (End i) X))
    (hevent : rho.events[i]? = some
      (Event.tick (S.E.proposer (s + 1))
        (Protocol.proposal_time S.E (s + 1))))
    {w : V} (hw : w ∈ rho.honest)
    (hstart : t1 ≤ Protocol.vote_time S.E (s + 1)) :
    GoldfishConeVoteInputs' S rho s (End i) w ∧
      End i ∈ voterCandidateTreeAt S rho w (s + 1) ∧
      Block.Preceq (voterAnchorAt S rho w (s + 1)) (End i) := by
  obtain ⟨E, hE, hErun⟩ :=
    h.endpointRun i h.start_le (Nat.le_refl i)
  have hrootPrepared : Block.Preceq
      (Protocol.get_fg_root
        (voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG) (End i) := by
    simpa only [hE] using
      (h.voteRoot_preceq_endpointAtProposal_named S adm hfb hevent hw hstart
        hE hErun)
  have hroot : Block.Preceq
      (Protocol.get_fg_root
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG) (End i) := by
    simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore] using
      hrootPrepared
  have hpositive : 0 < ((S.E.committee s) ∩ rho.honest).card := by
    have hcc := hcom s
    omega
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpositive
  have hxHonest : x ∈ rho.honest := (Finset.mem_inter.mp hx).2
  have hxCommittee : x ∈ S.E.committee s := (Finset.mem_inter.mp hx).1
  obtain ⟨X, hX, hXrun, hXemit⟩ := hvotes x hxHonest hxCommittee
  have hXhead : Proofs.Optimistic.HonestHead S rho s X.erase :=
    ⟨x, hxHonest, hxCommittee, ⟨X, rfl, hXrun⟩, hXemit⟩
  have hprocessedHead := honestHead_voterProcessed_at_nextDuty_of_postHealingCone
    S adm hpostVote hslotHor hvotes hXhead hw hroot
  have hprocessedEnd := WeakGoldfish.ancestorProcessed_of_voterProcessed
    S adm.toNamedAdmissibleCore hw hprocessedHead (End i) hX
  have hmemTarget : End i ∈
      (voteDutyRead S rho w (s + 1)).st.core.T := by
    have hdata := hprocessedEnd
    simp only [Protocol.voter_processed_block_tree, Finset.mem_filter] at hdata
    simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore] using
      hdata.1
  have hmemPre : End i ∈
      (rho.stateBeforeTime S (Protocol.vote_time S.E (s + 1)) w).st.core.T := by
    simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
      hmemTarget
  obtain ⟨E0, hE0body, hE0erase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho
      (Protocol.vote_time S.E (s + 1)) w hmemPre
  have hE0run : RunBlock S rho E0 := by
    obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
      (Protocol.vote_time S.E (s + 1))
    apply Proofs.Bridges.runBlock_of_stateBefore_mem S hw
    simpa only [Run.storeBeforeTime, hn] using hE0body
  have hE0eq : E0 = E := by
    apply adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective
      E0 E hE0run hErun E0 E (Or.inl (Proofs.NamedAncestry.named_self E0))
      (Or.inr (Proofs.NamedAncestry.named_self E))
    rw [← Proofs.NamedWire.erase_root E0, hE0erase, ← Proofs.NamedWire.erase_root E, hE]
  have hEbody : E ∈
      (rho.stateBeforeTime S (Protocol.vote_time S.E (s + 1)) w).st.bodies := by
    rw [← hE0eq]
    exact hE0body
  have hsigma :
      (voteDutyRead S rho w (s + 1)).st.core.σ (End i) =
        Protocol.derive_named S.E S.cfg E := by
    rw [← hE]
    simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
      Proofs.NamedStoreBridge.derivedView_stateBeforeTime S rho
        (Protocol.vote_time S.E (s + 1)) w E hEbody
  have hfloorDerived :
      (voteDutyRead S rho w (s + 1)).st.core.h_max - 1 ≤
        (Protocol.derive_named S.E S.cfg E).h :=
    h.voteFrontier_sub_one_le_endpointAtProposal_named S adm hfb hevent hw
      hE hErun
  have hfloor :
      (voteDutyRead S rho w (s + 1)).st.core.h_max - 1 ≤
        ((voteDutyRead S rho w (s + 1)).st.core.σ (End i)).h := by
    rw [hsigma]
    exact hfloorDerived
  have hFJ : Block.Preceq
      (voteDutyRead S rho w (s + 1)).st.core.F
      (voteDutyRead S rho w (s + 1)).st.core.J := by
    simpa only [voteDutyRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
      Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime S rho
        (Protocol.vote_time S.E (s + 1)) w
  have hFEnd : Block.Preceq
      (voteDutyRead S rho w (s + 1)).st.core.F (End i) :=
    Block.preceq_trans
      (Proofs.Records.preceq_get_fg_root_of_F
        (st := (voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG) hFJ)
      hrootPrepared
  have hEndFiltered : End i ∈
      Protocol.get_filtered_block_tree
        (voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG := by
    have hV : End i ∈ Protocol.V_tree
        (voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG := by
      simp only [Protocol.V_tree, Protocol.viable_tree,
        Protocol.finalized_descendants, Protocol.viable,
        Finset.mem_filter, decide_eq_true_eq, Protocol.Store.toHealing]
      exact ⟨⟨hmemTarget, hFEnd⟩, End i, hmemTarget,
        Block.preceq_self _, hfloor⟩
    exact Proofs.Records.mem_filtered_of_mem_V_tree hV hrootPrepared
  have hmax :
      (voteDutyRead S rho w (s + 1)).st.core.h_max ≤
        (Protocol.derive_named S.E S.cfg E).h + 1 :=
    Nat.sub_le_iff_le_add.mp hfloorDerived
  have hcandidate : End i ∈ voterCandidateTreeAt S rho w (s + 1) := by
    simpa only [voterCandidateTreeAt, Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt, NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock, Proofs.Optimistic.voteDutyStore,
      Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore] using
      (namedAncestorCandidate_of_processedDescendant_and_hMax
        (S := S) (rho := rho) (w := w) (s := s) (C := End i) (H := E)
        adm hw (by simpa only [hE] using hprocessedEnd) hErun
          (by simpa only [hE] using (Block.preceq_self (End i))) hEndFiltered hmax)
  have hpath := movingFrontierChainStateN_transfer_votePathAt_of_candidate
    S adm hw hcandidate
  have hvoteHor : Protocol.vote_time S.E (s + 1) ≤ rho.horizon := by
    have htime : Protocol.vote_time S.E (s + 1) ≤
        Protocol.confirmation_time S.E s := by
      rw [← Protocol.vote_time_succ_add_delta_eq_confirmation_time S.E s]
      exact le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)
    exact htime.trans hslotHor
  have hanchorEnd : Block.Preceq
      (voterAnchorAt S rho w (s + 1)) (End i) :=
    voterAnchorAt_preceq_of_previousCarriers S adm hfb hround hpostAction hcut
      hvoteHor hupper hw hroot
  have hcompat : Block.compatible
      (voterAnchorAt S rho w (s + 1)) (End i) = true :=
    Block.compatible_of_preceq_common hanchorEnd (Block.preceq_self _)
  have hinputs : GoldfishConeVoteInputs' S rho s (End i) w :=
    { rootSide := Or.inl ⟨hrootPrepared, hcandidate, hpath⟩
      anchor := hcompat }
  exact ⟨hinputs, hcandidate, hanchorEnd⟩

#print axioms MovingFrontierChainStateN.voteInputsAtVote_of_proposalEvent_named_of_ceiling


/-
/-- The pre-proposal moving history supplies the complete primed Goldfish
input at a same-slot honest vote read. The earlier vote cone supplies frozen
processing. The direct root theorem above and the previous-action carrier
ceiling supply the full-store root and anchor geometry. -/
theorem MovingFrontierChainState.voteInputsAtVote_of_proposalEvent
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hfb: BelowOneThird S rho.honest)
    {t1: Time} {M0: Height} {n0 i: Nat} {End: Nat → Block V}
    (h: MovingFrontierChainState S rho t1 M0 n0 i End)
    {r: Round} {s: Slot}
    (hround: S.hc.round_of (s + 1) = r + 1)
    (ht1: t1 ≤ S.a r)
    (hpostAction: S.E.t_GST ≤ S.a r)
    (hcut: S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon)
    (hpostVote: S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hslotHor: Protocol.confirmation_time S.E s ≤ rho.horizon)
    (hvotes: Proofs.Optimistic.HonestVotesCone S rho s
      (fun X => Block.Preceq (End i) X))
    (hevent: rho.events[i]? = some
      (Event.tick (S.E.proposer (s + 1))
        (Protocol.proposal_time S.E (s + 1))))
    {w: V} (hw: w ∈ rho.honest)
    (hstart: t1 ≤ Protocol.vote_time S.E (s + 1)):
    GoldfishConeVoteInputs' S rho s (End i) w ∧
      End i ∈ Protocol.get_filtered_block_tree
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG ∧
      Block.Preceq
        (Proofs.Optimistic.healAnchor S.E S.hc
          (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing) (End i):= by
  have hmajority: HonestWeightMajority S rho.honest:=
    AlignedRoundLemmas.honestWeightMajority_of_belowOneThird (S:= S) hfb
  have hroot: Block.Preceq
      (Protocol.get_fg_root
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG) (End i):=
    h.voteRoot_preceq_endpointAtProposal S adm hfb hevent hw hstart
  have havailable:= honestHeadsAvailableBefore_of_postHealingCone_atVoteDuty
    S adm hw hpostVote
      ((support_cutoff_le_confirmation_time S.E s).trans hslotHor)
      hroot hvotes
  have hprocessed:= Protocol.voterProcessedConeEndpoint_of_availableBefore
    S adm hcom havailable hvotes
  let target:= Proofs.Optimistic.voteDutyStore S rho w (s + 1)
  let pre:= rho.storeBeforeTime S w (Protocol.vote_time S.E (s + 1))
  have hmemTarget: End i ∈ target.T:= by
    have hdata:= hprocessed
    simp only [Protocol.voter_processed_block_tree, Finset.mem_filter] at hdata
    simpa only [target] using hdata.1
  have hmemPre: End i ∈ pre.T:= by
    simpa only [target, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore, pre] using hmemTarget
  have hdep: DepReachableStore S.E S.hc S.cfg (S.node w) pre:= by
    simpa only [pre, Run.storeBeforeTime] using
      (Proofs.Bridges.depReachable_stateBeforeTime S adm.toScheduleWellFormed
        adm.toDeliveryWellFormed (Protocol.vote_time S.E (s + 1)) w)
  have hreach: ReachableStore S.E S.hc S.cfg (S.node w) pre:=
    Proofs.Bridges.reachableStore_of_depReachableStore
      S.E S.hc S.cfg (S.node w) hdep
  have hpc: ParentClosed pre:=
    parentClosed_depReachable S.E S.hc S.cfg (S.node w) pre hdep
  have hFJ: Block.Preceq pre.F pre.J:=
    finalizedPrecedesJustifiedInvariant S.E S.hc S.cfg
      (S.node w) pre hreach
  have hagree: DerivedStateAgrees S.E S.cfg pre:=
    derivedStateAgrees_depReachable S.E S.hc S.cfg (S.node w) pre hdep
  have hfloorDerived: pre.h_max - 1 ≤
      (derived_state S.E S.cfg (End i)).h:= by
    simpa only [target, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore, pre] using
        h.voteFrontier_sub_one_le_endpointAtProposal S adm hfb hevent hw
  have hfloor: pre.h_max - 1 ≤ (pre.σ (End i)).h:= by
    rw [hagree (End i) hmemPre]
    exact hfloorDerived
  have hFEnd: Block.Preceq pre.F (End i):=
    Block.preceq_trans
      (Proofs.Records.preceq_get_fg_root_of_F (st:= pre.toHealing.toFG) hFJ)
      (by simpa only [target, Proofs.Optimistic.voteDutyStore,
        Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore, pre] using hroot)
  have hEndFilteredPre: End i ∈
      Protocol.get_filtered_block_tree pre.toHealing.toFG:= by
    have hV: End i ∈ Protocol.V_tree pre.toHealing.toFG:= by
      simp only [Protocol.V_tree, Protocol.viable_tree,
        Protocol.finalized_descendants, Protocol.viable,
        Finset.mem_filter, decide_eq_true_eq, Protocol.Store.toHealing]
      exact ⟨⟨hmemPre, hFEnd⟩, End i, hmemPre,
        Block.preceq_self _, hfloor⟩
    exact Proofs.Records.mem_filtered_of_mem_V_tree hV
      (by simpa only [target, Proofs.Optimistic.voteDutyStore,
        Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore, pre] using hroot)
  have hpathPre: ∀ D: Block V,
      Block.Preceq
        (Protocol.get_fg_root pre.toHealing.toFG) D →
      Block.Preceq D (End i) →
      D ∈ Protocol.get_filtered_block_tree pre.toHealing.toFG:= by
    intro D hrootD hDEnd
    have hDmem: D ∈ pre.T:=
      Proofs.Records.mem_of_preceq ((parentClosed_iff pre).mp hpc).2
        D (End i) hmemPre hDEnd
    exact Proofs.Records.mem_filtered_of_preceq
      (st:= pre.toHealing.toFG)
      (by simpa only [Protocol.Store.toHealing] using hFJ)
      hEndFilteredPre hDmem hDEnd hrootD
  have hrootRaw: Block.Preceq
      (Protocol.get_fg_root pre.toHealing.toFG) (End i):= by
    simpa only [target, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore, pre] using hroot
  have htargetRoundPos: 0 < S.hc.round_of (s + 1):= by
    rw [hround]
    exact Nat.succ_pos r
  have hdelay: S.a r + S.E.Δ ≤
      Protocol.proposal_time S.E (s + 1):= by
    have hdelay':= Protocol.previous_action_add_delta_le_proposal
      S htargetRoundPos
    simpa only [hround, Nat.add_sub_cancel] using hdelay'
  have hbefore: S.a r < Protocol.proposal_time S.E (s + 1):=
    (Int.lt_add_of_pos_right (S.a r) S.E.Δ_pos).trans_le hdelay
  have hproposalHor: Protocol.proposal_time S.E (s + 1) ≤ rho.horizon:=
    (le_of_lt (Protocol.proposal_time_lt_vote_time S.E (s + 1))).trans
      ((le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans_eq
        (Protocol.vote_time_succ_add_delta_eq_confirmation_time
          S.E s) |>.trans hslotHor)
  have hactionHor: S.a r ≤ rho.horizon:=
    (le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans
      (hdelay.trans hproposalHor)
  have hupper:= h.previousActionCarriersPreceqAtIndex
    S adm hevent ht1 hactionHor hbefore
  have hread: S.hc.Γ_0 S.E.Δ (r + 1) ≤
      Protocol.vote_time S.E (s + 1):= by
    simpa only using Γ_0_le_vote_time_of_round_eq S hround
  have hanchorRaw:= readAnchor_preceq_of_previousActionCeiling
    S adm hfb hpostAction hcut hread hw hmemPre hrootRaw hupper
  have hanchor: Block.Preceq
      (Proofs.Optimistic.healAnchor S.E S.hc target.toHealing) (End i):= by
    rw [Proofs.Optimistic.healAnchor_eq_get_sg_root]
    have hslot: target.toHealing.s = s + 1:= by
      simpa only [target, Proofs.Optimistic.toHealing_slot] using
        Proofs.Optimistic.voteDutyStore_slot S rho w (s + 1)
    rw [hslot, hround]
    simpa only [target, pre] using hanchorRaw
  have hrootSide:
      (Block.Preceq
          (Protocol.get_fg_root target.toHealing.toFG) (End i) ∧
        End i ∈ Protocol.get_filtered_block_tree target.toHealing.toFG ∧
        ∀ D: Block V,
          Block.Preceq
            (Protocol.get_fg_root target.toHealing.toFG) D →
          Block.Preceq D (End i) →
          D ∈ Protocol.get_filtered_block_tree target.toHealing.toFG) ∨
      Block.Preceq (End i)
        (Protocol.get_fg_root target.toHealing.toFG):= by
    exact Or.inl ⟨hroot,
      by simpa only [target, Proofs.Optimistic.voteDutyStore,
        Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore, pre] using hEndFilteredPre,
      by
        intro D hrootD hDEnd
        simpa only [target, Proofs.Optimistic.voteDutyStore,
          Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore, pre] using
            hpathPre D (by simpa only [target, Proofs.Optimistic.voteDutyStore,
              Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore, pre] using hrootD)
              hDEnd⟩
  have hmax: target.h_max ≤
      (derived_state S.E S.cfg (End i)).h + 1:= by
    exact Nat.sub_le_iff_le_add.mp (by
      simpa only [target, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore, pre] using hfloorDerived)
  refine ⟨voteInputs_of_rootSideWithPath S adm hw
    (by simpa only [target] using hprocessed) hmax hrootSide
      (Block.compatible_of_preceq_common hanchor (Block.preceq_self _)), ?_, hanchor⟩
  simpa only [target, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
    Proofs.Optimistic.tickStore, pre] using hEndFilteredPre
-/


/- /-- At the honest proposal read, the integrated SG anchor is below the previous
moving endpoint. The endpoint is in the proposer store because it precedes
the selected proposal parent. -/
/-- At the honest proposal read, the integrated SG anchor is below the prior
moving endpoint. The endpoint is in the proposer store because it precedes
the selected proposal parent. -/
theorem MovingFrontierChainState.proposalAnchor_preceq_endpointAtProposal
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hfb: BelowOneThird S rho.honest)
    {t1: Time} {M0: Height} {n0 i: Nat} {End: Nat → Block V}
    (h: MovingFrontierChainState S rho t1 M0 n0 i End)
    {r: Round} {s: Slot}
    (hround: S.hc.round_of s = r + 1)
    (ht1: t1 ≤ S.a r)
    (hpostAction: S.E.t_GST ≤ S.a r)
    (hcut: S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon)
    (hprop: S.E.proposer s ∈ rho.honest)
    (hevent: rho.events[i]? = some
      (Event.tick (S.E.proposer s) (Protocol.proposal_time S.E s)))
    (hhor: Protocol.proposal_time S.E s ≤ rho.horizon)
    (hendParent: Block.Preceq (End i) (proposedParent S rho s)):
    Block.Preceq
      (Proofs.Optimistic.healAnchor S.E S.hc
        (proposerDutyStore S rho s).toHealing) (End i):= by
  let duty:= proposerDutyStore S rho s
  let pre:= rho.storeBeforeTime S (S.E.proposer s)
    (Protocol.proposal_time S.E s)
  have hparentDuty: proposedParent S rho s ∈ duty.T:=
    proposedParent_mem S adm s
  have hparentPre: proposedParent S rho s ∈ pre.T:= by
    simpa only [duty, proposerDutyStore, Proofs.Optimistic.tickStore, pre] using
      hparentDuty
  have hpc: ParentClosed pre:=
    parentClosed_depReachable S.E S.hc S.cfg
      (S.node (S.E.proposer s)) pre (by
        simpa only [pre, Run.storeBeforeTime] using
          (Proofs.Bridges.depReachable_stateBeforeTime S adm.toScheduleWellFormed
            adm.toDeliveryWellFormed (Protocol.proposal_time S.E s)
              (S.E.proposer s)))
  have hmem: End i ∈ pre.T:=
    Proofs.Records.mem_of_preceq ((parentClosed_iff pre).mp hpc).2
      (End i) (proposedParent S rho s) hparentPre hendParent
  have hrootState:= h.newRoot_on_endpointChainAtIndex_of_start
    S adm hfb h.start_le (Nat.le_refl i) hprop
  have hstate:= Proofs.Optimistic.stateBefore_tick_eq_stateBeforeTime
    S adm.toScheduleWellFormed hevent
  have hroot: Block.Preceq
      (Protocol.get_fg_root pre.toHealing.toFG) (End i):= by
    rw [hstate] at hrootState
    simpa only [pre, Run.storeBeforeTime] using hrootState
  have hroundPos: 0 < S.hc.round_of s:= by
    rw [hround]
    exact Nat.succ_pos r
  have hdelay: S.a r + S.E.Δ ≤ Protocol.proposal_time S.E s:= by
    have hdelay':= Protocol.previous_action_add_delta_le_proposal
      S hroundPos
    simpa only [hround, Nat.add_sub_cancel] using hdelay'
  have hbefore: S.a r < Protocol.proposal_time S.E s:=
    (Int.lt_add_of_pos_right (S.a r) S.E.Δ_pos).trans_le hdelay
  have hactionHor: S.a r ≤ rho.horizon:=
    (le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans
      (hdelay.trans hhor)
  have hupper:= h.previousActionCarriersPreceqAtIndex
    S adm hevent ht1 hactionHor hbefore
  have hopen: S.hc.opening_slot (r + 1) ≤ s:= by
    unfold Protocol.HealConfig.round_of at hround
    unfold Protocol.HealConfig.opening_slot
    rw [← hround]
    exact Nat.div_mul_le_self s S.hc.R
  have hread: S.hc.Γ_0 S.E.Δ (r + 1) ≤
      Protocol.proposal_time S.E s:= by
    rw [Protocol.Γ_0_eq_proposal_time]
    exact Protocol.proposal_time_mono S.E hopen
  have hanchorRaw:= readAnchor_preceq_of_previousActionCeiling
    S adm hfb hpostAction hcut hread hprop hmem hroot hupper
  rw [Proofs.Optimistic.healAnchor_eq_get_sg_root]
  have hslot: duty.toHealing.s = s:= by
    simp only [duty, proposerDutyStore, Proofs.Optimistic.tickStore,
      Proofs.Optimistic.slotOf_proposal_time, Protocol.Store.toHealing]
  rw [hslot, hround]
  simpa only [duty, proposerDutyStore, Proofs.Optimistic.tickStore, pre] using
    hanchorRaw
-/

theorem MovingFrontierChainStateN.proposalAnchor_preceq_endpointAtProposal_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {t1 : Time} {M0 : Height} {n0 i : Nat} {End : Nat → Block V}
    (h : MovingFrontierChainStateN S rho t1 M0 n0 i End)
    {r : Round} {s : Slot}
    (hround : S.hc.round_of s = r + 1)
    (ht1 : t1 ≤ S.a r)
    (hpostAction : S.E.t_GST ≤ S.a r)
    (hcut : S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon)
    (hprop : S.E.proposer s ∈ rho.honest)
    (hevent : rho.events[i]? = some
      (Event.tick (S.E.proposer s) (Protocol.proposal_time S.E s)))
    (hhor : Protocol.proposal_time S.E s ≤ rho.horizon)
    (hendParent : Block.Preceq (End i) (proposedParent S rho s))
    {E : NamedBlock V} (hE : E.erase = End i) (hErun : RunBlock S rho E) :
    Block.Preceq
      (Internal.PhaseGrades.nodeAnchor S (proposerReadAt S rho s)
        (S.hc.round_of (proposerReadAt S rho s).st.core.s)) (End i) := by
  have hrootState := h.root_preceq_endpointAtProposal_beforeVote
    S adm hfb hevent hevent
      (by simpa only [Event.time] using
        (Protocol.proposal_time_lt_vote_time S.E s))
      hprop h.start_le hE hErun
  have hstate := Proofs.Optimistic.stateBefore_tick_eq_stateBeforeTime S
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hevent
  have hroot : Block.Preceq
      (Protocol.get_fg_root
        (proposerReadAt S rho s).st.core.toHealing.toFG) (End i) := by
    rw [hstate] at hrootState
    simpa only [proposerReadAt, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
      hrootState
  have hroundPos : 0 < S.hc.round_of s := by
    rw [hround]
    exact Nat.succ_pos r
  have hdelay : S.a r + S.E.Δ ≤ Protocol.proposal_time S.E s := by
    have hdelay' := Protocol.previous_action_add_delta_le_proposal
      S hroundPos
    simpa only [hround, Nat.add_sub_cancel] using hdelay'
  have hbefore : S.a r < Protocol.proposal_time S.E s :=
    (Int.lt_add_of_pos_right (S.a r) S.E.Δ_pos).trans_le hdelay
  have hactionHor : S.a r ≤ rho.horizon :=
    (le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans
      (hdelay.trans hhor)
  have hcursor : strictEventIndex rho (Protocol.proposal_time S.E s) ≤ i :=
    filterBefore_length_le_tickIndex S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hevent (le_refl _)
  have hupper : ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u r) (End i) := by
    intro u hu
    obtain ⟨j, hj, hout⟩ :=
      honest_emits_exact_actionAttestationAt S adm hu r hactionHor
    have hji : j < i :=
      (emission_index_lt_beforeTime_prefix S
        adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hj hbefore).trans_le
        hcursor
    have hn0j : n0 ≤ j := by
      rw [h.historyStart]
      exact filterBefore_length_le_tickIndex S
        adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hj ht1
    exact Block.preceq_trans ((h.sgCarriers j hn0j hji) hu hj hout)
      (movingFrontierChainStateN_transfer_endpoint_mono h
        (hn0j.trans (Nat.le_succ j)) (Nat.succ_le_iff.mpr hji) (Nat.le_refl i))
  exact proposalAnchorAt_preceq_of_previousCarriers_named
    S adm hfb hround hpostAction hcut hhor hupper hprop hroot

#print axioms MovingFrontierChainStateN.proposalAnchor_preceq_endpointAtProposal_named


/-
/-- Any honest read before the proposal's same-slot vote keeps its selected
FG root below the endpoint that preceded the proposal. This indexed form is
used for the finalized-root guard at proposal delivery events. -/
private theorem MovingFrontierChainState.root_preceq_endpointAtProposal_beforeVote
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hfb: BelowOneThird S rho.honest)
    {t1: Time} {M0: Height} {n0 i: Nat} {End: Nat → Block V}
    (h: MovingFrontierChainState S rho t1 M0 n0 i End)
    {s: Slot}
    (hevent: rho.events[i]? = some
      (Event.tick (S.E.proposer s) (Protocol.proposal_time S.E s)))
    {k: Nat} {e: Event V} (hkevent: rho.events[k]? = some e)
    (hktime: e.time < Protocol.vote_time S.E s)
    {w: V} (hw: w ∈ rho.honest) (hn0k: n0 ≤ k):
    Block.Preceq
      (Protocol.get_fg_root
        (rho.stateBefore S k w).st.toHealing.toFG) (End i):= by
  let st:= (rho.stateBefore S k w).st
  have hdep: DepReachableStore S.E S.hc S.cfg (S.node w) st:= by
    simpa only [st] using
      (Proofs.Bridges.depReachable_of_admissible S adm.toDeliveryWellFormed w k)
  have hbelow: st.h_j < st.h_max:=
    FixedHeightRootCore.justificationBelowMax_depReachable
      S.E S.hc S.cfg (S.node w) hdep
  have hmajority: HonestWeightMajority S rho.honest:=
    AlignedRoundLemmas.honestWeightMajority_of_belowOneThird (S:= S) hfb
  have hsb: SlashableBound S rho:=
    slashableBound_of_admissible_belowOneThird S adm hfb
  have hemittedBefore: ∀ {B: Block V} {a: CombinedAttestation V},
      B ∈ st.T → a ∈ chain_attestations B →
      a.val_index ∈ rho.honest →
      ∃ j: Nat,
        j < i ∧
        rho.events[j]? = some (Event.tick a.val_index (S.a a.round)) ∧
        Object.attest a ∈
          (on_tick_emit S (S.node a.val_index)
            (rho.stateBefore S j a.val_index).st
            (rho.stateBefore S j a.val_index).Λ (S.a a.round)).2.2:= by
    intro B a hB ha haHon
    obtain ⟨j, ta, hjk, hjevent, hja, hemit⟩:=
      honestCarriedAttestation_emittedBeforeIndex
        S adm (by simpa only [st] using hB) ha haHon
    have hshape:= Proofs.Optimistic.emits_attest_shape S hemit
    have hkey:= Proofs.Optimistic.key_le_of_index_lt
      S adm.toScheduleWellFormed hjk hjevent hkevent
    have htaK: ta ≤ e.time:= Proofs.Bridges.time_le_of_key_le hkey
    have hactionVote: S.a a.round < Protocol.vote_time S.E s:= by
      calc
        S.a a.round = ta:= hshape.2.symm
        _ ≤ e.time:= htaK
        _ < Protocol.vote_time S.E s:= hktime
    have hactionProposal:=
      action_time_lt_proposal_of_lt_vote S hactionVote
    have hji: j < i:=
      movingEventIndex_lt_of_eventTime_lt S adm.toScheduleWellFormed
        hjevent hevent (by
          simpa only [Event.time, hshape.2] using hactionProposal)
    refine ⟨j, hji, ?_, ?_⟩
    · simpa only [hshape.2] using hjevent
    · simpa only [hshape.2] using hja
  have hfrontierFloor: st.h_max - 1 ≤
      (derived_state S.E S.cfg (End i)).h:= by
    by_contra hnot
    have hhigh: (derived_state S.E S.cfg (End i)).h < st.h_max - 1:=
      Nat.lt_of_not_ge hnot
    have hlarge: 1 < st.h_max:=
      Nat.sub_pos_iff_lt.mp ((Nat.zero_le _).trans_lt hhigh)
    have hagree: DerivedStateAgrees S.E S.cfg st:=
      derivedStateAgrees_depReachable S.E S.hc S.cfg (S.node w) st hdep
    obtain ⟨W, hWT, hmaxW⟩:=
      hMaxInTree_depReachable S.E S.hc S.cfg (S.node w) hdep
    have hcross: st.h_max - 1 < (derived_state S.E S.cfg W).h:= by
      rw [← hagree W hWT]
      exact (Nat.sub_lt (Nat.zero_lt_of_lt hlarge) (by omega)).trans_le hmaxW
    obtain ⟨Q, _X, hQ, _hXW, hwitness⟩:=
      Protocol.height_crossing S.E S.cfg (st.h_max - 1)
        (Nat.sub_pos_iff_lt.mpr hlarge) W hcross
    obtain ⟨signer, hsignerQ, hsignerHonest⟩:=
      HonestWeightMajority.exists_honest_member_of_quorum hmajority hQ
    obtain ⟨a, haW, haSigner, haPair⟩:= hwitness signer hsignerQ
    have haHonest: a.val_index ∈ rho.honest:= by
      rw [haSigner]
      exact hsignerHonest
    have haHeight: a.height_pair.height? = some (st.h_max - 1):= by
      rcases haPair with htarget | htimeout
      · rw [htarget]
        rfl
      · rw [htimeout]
        rfl
    obtain ⟨j, hji, hjevent, hja⟩:=
      hemittedBefore hWT haW haHonest
    by_cases hj0: j < n0
    · exact (not_le_of_gt hhigh)
        (h.oldRow_le_endpointHeight S haHonest hjevent hja hj0 haHeight)
    · have hn0j: n0 ≤ j:= Nat.le_of_not_gt hj0
      obtain ⟨G, _hGrun, hGheight, hGnext⟩:=
        (h.outputs j hn0j hji).height_gate_sources
          haHonest hjevent hja (st.h_max - 1) haHeight
      have hnextEnd: Block.Preceq (End (j + 1)) (End i):=
        h.endpoint_mono (hn0j.trans (Nat.le_succ j))
          (Nat.succ_le_iff.mpr hji) (Nat.le_refl i)
      have hrowEnd: st.h_max - 1 ≤
          (derived_state S.E S.cfg (End i)).h:= by
        calc
          st.h_max - 1 = (derived_state S.E S.cfg G).h:= hGheight.symm
          _ ≤ (derived_state S.E S.cfg (End (j + 1))).h:=
            Protocol.derived_h_mono S.E S.cfg hGnext
          _ ≤ (derived_state S.E S.cfg (End i)).h:=
            Protocol.derived_h_mono S.E S.cfg hnextEnd
      exact (not_le_of_gt hhigh) hrowEnd
  have hEndRun: RunBlock S rho (End i):=
    h.endpointRun i h.start_le (Nat.le_refl i)
  have hfloorM: M0 ≤ st.h_max:= by
    simpa only [st] using h.frontierFloor w hw k hn0k
  by_cases hgate: st.h_max = st.h_j + 1
  · obtain ⟨C, hC, hhj, hJ⟩:=
      (Proofs.Bridges.provenance_depReachable
        S.E S.hc S.cfg (S.node w) hdep).2
    have hJmem: st.J ∈ st.T:=
      Proofs.Records.justifiedInTree_depReachable
        S.E S.hc S.cfg (S.node w) st hdep
    have hJrun: RunBlock S rho st.J:= by
      apply Proofs.Bridges.runBlock_of_stateBefore_mem S hw (i:= k)
      simpa only [st] using hJmem
    refine h.gateOnRoot_preceq_of_boundary S adm hhj hJ hJrun
      hfloorM hgate ?_
    intro hz
    have hhjNe: (derived_state S.E S.cfg C).h_j ≠ 0:= by
      rw [hhj]
      exact hz
    obtain ⟨Q, hQ, hwit⟩:=
      AlignedRoundLemmas.justification_certificate S.E S.cfg C hhjNe
    obtain ⟨signer, hsignerQ, hsignerHonest⟩:=
      HonestWeightMajority.exists_honest_member_of_quorum hmajority hQ
    obtain ⟨a, haC, haSigner, haPair⟩:= hwit signer hsignerQ
    have haHonest: a.val_index ∈ rho.honest:= by
      rw [haSigner]
      exact hsignerHonest
    have haTarget: a.height_pair = HeightPair.target st.h_j st.J.root:= by
      rw [← hhj, ← hJ]
      exact haPair
    obtain ⟨j, hji, hjevent, hja⟩:= hemittedBefore hC haC haHonest
    exact ⟨a, S.a a.round, j, haHonest, hjevent, hja, haTarget, hji⟩
  · have hgateOff: st.h_j + 2 ≤ st.h_max:= by
      have hsucc: st.h_j + 1 ≤ st.h_max:= Nat.succ_le_iff.mpr hbelow
      have hstrict: st.h_j + 1 < st.h_max:=
        lt_of_le_of_ne hsucc (fun heq => hgate heq.symm)
      simpa only [Nat.add_assoc] using Nat.succ_le_iff.mpr hstrict
    have hhjlt: st.h_j < st.h_max - 1:= by
      rw [Nat.lt_sub_iff_add_lt]
      exact Nat.lt_of_succ_le (by simpa only [Nat.add_assoc] using hgateOff)
    have hnoHigh: NoHighJustifications S.E S.cfg st:=
      FixedHeightRootCore.noHighJustifications_depReachable
        S.E S.hc S.cfg (S.node w) hdep
    obtain ⟨C, hC, hF⟩:=
      Proofs.Bridges.storeFinalizationOnChain_depReachable
        S.E S.hc S.cfg (S.node w) hdep
    have hCrun: RunBlock S rho C:= by
      apply Proofs.Bridges.runBlock_of_stateBefore_mem S hw (i:= k)
      simpa only [st] using hC
    have hcrossed: (derived_state S.E S.cfg C).h_F <
        (derived_state S.E S.cfg (End i)).h:= by
      calc
        (derived_state S.E S.cfg C).h_F ≤
            (derived_state S.E S.cfg C).h_j:=
          (Protocol.chainOrder_derived_state S.E S.cfg C).heights_ordered
        _ ≤ st.h_j:= hnoHigh C hC
        _ < st.h_max - 1:= hhjlt
        _ ≤ (derived_state S.E S.cfg (End i)).h:= hfrontierFloor
    have hFEnd: Block.Preceq st.F (End i):= by
      have hpre: Block.Preceq (derived_state S.E S.cfg C).F (End i):=
        Protocol.finalized_preceq_of_height_lt hsb hCrun hEndRun
          (adm.toRootCollisionFree.root_injective (End i) C hEndRun hCrun)
          ⟨rfl, rfl⟩ hcrossed
      simpa only [hF] using hpre
    simp only [Protocol.get_fg_root, Protocol.Store.toHealing,
      if_neg (by simpa only [st] using hgate)]
    exact hFEnd
-/


/- /-- The moving source history supplies the common frozen-suffix inputs for one
honest voter. Proposal delivery is safe because every receiver FG root before
the vote is below the previous endpoint, and the previous endpoint is below the proposal
parent. -/
/-- The moving source history supplies the common frozen-suffix inputs for one
honest voter. Proposal delivery is safe because every receiver FG root before
the vote is below the prior endpoint, and the prior endpoint is below the proposal
parent. -/
theorem MovingFrontierChainState.frozenProposalSuffixCoreInputs_of_proposalEvent
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hfb: BelowOneThird S rho.honest)
    {t1: Time} {M0: Height} {n0 i: Nat} {End: Nat → Block V}
    (h: MovingFrontierChainState S rho t1 M0 n0 i End)
    {r: Round} {s: Slot}
    (hround: S.hc.round_of (s + 1) = r + 1)
    (ht1: t1 ≤ S.a r)
    (hpostAction: S.E.t_GST ≤ S.a r)
    (hcut: S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon)
    (hpostVote: S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hslotHor: Protocol.confirmation_time S.E s ≤ rho.horizon)
    (hvotes: Proofs.Optimistic.HonestVotesCone S rho s
      (fun X => Block.Preceq (End i) X))
    (hprop: S.E.proposer (s + 1) ∈ rho.honest)
    (hevent: rho.events[i]? = some
      (Event.tick (S.E.proposer (s + 1))
        (Protocol.proposal_time S.E (s + 1))))
    (hendParent: Block.Preceq (End i)
      (proposedParent S rho (s + 1)))
    (hstart: t1 ≤ Protocol.proposal_time S.E (s + 1))
    {w: V} (hw: w ∈ rho.honest):
    FrozenProposalSuffixCoreInputs S rho (s + 1) (End i) w:= by
  let proposalTime:= Protocol.proposal_time S.E (s + 1)
  let voteTime:= Protocol.vote_time S.E (s + 1)
  let target:= Proofs.Optimistic.voteDutyStore S rho w (s + 1)
  let targetPre:= rho.storeBeforeTime S w voteTime
  have hproposalVote: proposalTime ≤ voteTime:=
    le_of_lt (Protocol.proposal_time_lt_vote_time S.E (s + 1))
  have hvoteData:= h.voteInputsAtVote_of_proposalEvent
    S adm hcom hfb hround ht1 hpostAction hcut hpostVote hslotHor
      hvotes hevent hw (hstart.trans hproposalVote)
  have hproposalHor: proposalTime ≤ rho.horizon:= by
    exact hproposalVote.trans
      ((le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans_eq
        (Protocol.vote_time_succ_add_delta_eq_confirmation_time
          S.E s) |>.trans hslotHor)
  have hsourceAnchor:= h.proposalAnchor_preceq_endpointAtProposal
    S adm hfb hround ht1 hpostAction hcut hprop hevent hproposalHor
      hendParent
  have hvoteHor: voteTime ≤ rho.horizon:= by
    exact (le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans_eq
      (Protocol.vote_time_succ_add_delta_eq_confirmation_time S.E s)
      |>.trans hslotHor
  have hFhist: ProposalFinalizedBelowAtDeliveries S rho (s + 1)
      (proposedBlock S rho (s + 1)):= by
    intro v hv k t hdelivery _htLower htUpper
    have hcursor: strictEventIndex rho proposalTime ≤ k:= by
      by_contra hnot
      have hk: k < (rho.events.filter
          (fun e => decide (e.time < proposalTime))).length:= by
        simpa only [strictEventIndex] using Nat.lt_of_not_ge hnot
      have htProposal:= Proofs.Optimistic.filter_true_of_index_lt
        S adm.toScheduleWellFormed _
        (Proofs.Optimistic.downward_lt proposalTime) hk hdelivery
      simp only [decide_eq_true_eq, Event.time] at htProposal
      exact (not_lt_of_ge _htLower) htProposal
    have hn0k: n0 ≤ k:= by
      rw [h.historyStart]
      exact (strictEventIndex_mono rho hstart).trans hcursor
    have hroot:= h.root_preceq_endpointAtProposal_beforeVote
      S adm hfb hevent hdelivery (by simpa only [Event.time] using htUpper)
        hv hn0k
    let st:= (rho.stateBefore S k v).st
    have hdep: DepReachableStore S.E S.hc S.cfg (S.node v) st:= by
      simpa only [st] using
        (Proofs.Bridges.depReachable_of_admissible S adm.toDeliveryWellFormed v k)
    have hFJ: Block.Preceq st.F st.J:=
      finalizedPrecedesJustifiedInvariant S.E S.hc S.cfg
        (S.node v) st
        (Proofs.Bridges.reachableStore_of_depReachableStore
          S.E S.hc S.cfg (S.node v) hdep)
    exact Block.preceq_trans
      (Proofs.Records.preceq_get_fg_root_of_F (st:= st.toHealing.toFG) hFJ)
      (Block.preceq_trans (by simpa only [st] using hroot)
        (Block.preceq_trans hendParent
          (proposedParent_preceq_proposedBlock S rho (s + 1))))
  have hadmit:= proposedBlock_admittedBefore_vote_after_gst
    S adm (Nat.succ_pos s) hprop
      (hpostVote.trans (by
        have hvoteCut: Protocol.vote_time S.E s <
            Protocol.support_cutoff S.E s:= by
          rw [← Proofs.Optimistic.vote_time_add_delta]
          exact Int.lt_add_of_pos_right _ S.E.Δ_pos
        exact (le_of_lt hvoteCut).trans
          (le_of_lt (Protocol.support_cutoff_lt_proposal_time_succ S.E s))))
      hvoteHor hFhist w hw
  have hPpre: proposedBlock S rho (s + 1) ∈ targetPre.T:= by
    simpa only [targetPre, voteTime] using
      (admittedBefore_mem_and_stamp_at S adm.toScheduleWellFormed
        hadmit (le_refl voteTime)).1
  have hPtarget: proposedBlock S rho (s + 1) ∈ target.T:= by
    simpa only [target, targetPre, voteTime, Proofs.Optimistic.voteDutyStore,
      Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore] using hPpre
  have hdepTarget: DepReachableStore S.E S.hc S.cfg (S.node w) targetPre:= by
    simpa only [targetPre, voteTime, Run.storeBeforeTime] using
      (Proofs.Bridges.depReachable_stateBeforeTime S adm.toScheduleWellFormed
        adm.toDeliveryWellFormed voteTime w)
  have hagree: DerivedStateAgrees S.E S.cfg targetPre:=
    derivedStateAgrees_depReachable S.E S.hc S.cfg
      (S.node w) targetPre hdepTarget
  have hPheight: targetPre.h_max - 1 ≤
      (targetPre.σ (proposedBlock S rho (s + 1))).h:= by
    calc
      targetPre.h_max - 1 ≤ (derived_state S.E S.cfg (End i)).h:= by
        simpa only [target, targetPre, voteTime, Proofs.Optimistic.voteDutyStore,
          Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore] using
            h.voteFrontier_sub_one_le_endpointAtProposal
              S adm hfb hevent hw
      _ ≤ (derived_state S.E S.cfg (proposedBlock S rho (s + 1))).h:=
        Protocol.derived_h_mono S.E S.cfg
          (Block.preceq_trans hendParent
            (proposedParent_preceq_proposedBlock S rho (s + 1)))
      _ = (targetPre.σ (proposedBlock S rho (s + 1))).h:=
        (congrArg (fun x => x.h) (hagree _ hPpre)).symm
  have hFJTarget: Block.Preceq targetPre.F targetPre.J:=
    finalizedPrecedesJustifiedInvariant S.E S.hc S.cfg
      (S.node w) targetPre
      (Proofs.Bridges.reachableStore_of_depReachableStore
        S.E S.hc S.cfg (S.node w) hdepTarget)
  have hrootTarget:= h.voteRoot_preceq_endpointAtProposal
    S adm hfb hevent hw (hstart.trans hproposalVote)
  have hFProposal: Block.Preceq targetPre.F
      (proposedBlock S rho (s + 1)):=
    Block.preceq_trans
      (Proofs.Records.preceq_get_fg_root_of_F
        (st:= targetPre.toHealing.toFG) hFJTarget)
      (Block.preceq_trans (by
        simpa only [target, targetPre, voteTime, Proofs.Optimistic.voteDutyStore,
          Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore] using hrootTarget)
        (Block.preceq_trans hendParent
          (proposedParent_preceq_proposedBlock S rho (s + 1))))
  have hV: proposedBlock S rho (s + 1) ∈
      Protocol.V_tree targetPre.toHealing.toFG:= by
    simp only [Protocol.V_tree, Protocol.viable_tree,
      Protocol.finalized_descendants, Protocol.viable,
      Finset.mem_filter, decide_eq_true_eq, Protocol.Store.toHealing]
    exact ⟨⟨hPpre, hFProposal⟩, proposedBlock S rho (s + 1), hPpre,
      Block.preceq_self _, hPheight⟩
  have hPfilteredPre: proposedBlock S rho (s + 1) ∈
      Protocol.get_filtered_block_tree targetPre.toHealing.toFG:=
    Proofs.Records.mem_filtered_of_mem_V_tree hV
      (Block.preceq_trans (by
        simpa only [target, targetPre, voteTime, Proofs.Optimistic.voteDutyStore,
          Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore] using hrootTarget)
        (Block.preceq_trans hendParent
          (proposedParent_preceq_proposedBlock S rho (s + 1))))
  have htargetSlot: target.toHealing.s = s + 1:= by
    simpa only [target, Proofs.Optimistic.toHealing_slot] using
      Proofs.Optimistic.voteDutyStore_slot S rho w (s + 1)
  have hPprocessed: proposedBlock S rho (s + 1) ∈
      Protocol.voter_processed_block_tree S.E
        target.toHealing.toFG.toSG.toGoldfishStore target.toHealing.s:= by
    simp only [Protocol.voter_processed_block_tree, Finset.mem_filter]
    exact ⟨hPtarget, Or.inr ⟨proposedBlock S rho (s + 1),
      ⟨hPtarget, by simp only [proposedBlock_slot, htargetSlot]⟩,
      Block.preceq_self _⟩⟩
  have hPfrontier: target.h_max - 1 ≤
      (target.σ (proposedBlock S rho (s + 1))).h:= by
    simpa only [target, targetPre, voteTime, Proofs.Optimistic.voteDutyStore,
      Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore] using hPheight
  have hPcandidate: proposedBlock S rho (s + 1) ∈
      Proofs.Optimistic.voter_candidate_tree S.E target.toHealing:=
    voterCandidate_of_processed_self_and_filtered
      S.E target.toHealing hPprocessed hPfrontier (by
        simpa only [target, targetPre, voteTime, Proofs.Optimistic.voteDutyStore,
          Proofs.Optimistic.voteStore, Proofs.Optimistic.tickStore] using hPfilteredPre)
  exact
    { sourceAnchor:= hsourceAnchor
      pivotTarget:= hvoteData.2.1
      proposalCandidate:= by simpa only [target] using hPcandidate
      pivotAnchorCompatible:= hvoteData.1.anchor
      proposalAnchorCompatible:=
        Block.compatible_of_preceq_common
          (Block.preceq_trans hvoteData.2.2
            (Block.preceq_trans hendParent
              (proposedParent_preceq_proposedBlock S rho (s + 1))))
          (Block.preceq_self _ ) }
-/


/-
/-- The voter frontier boundary is already on the honest proposal parent's
chain. The result is stronger than the one-step numeric bound: it identifies
the exact `h_max - 1` crossing height below the proposal parent. -/
theorem MovingSlotEntryState.voteFrontier_sub_one_le_proposedParent
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hfb: BelowOneThird S rho.honest)
    {t1: Time} {M0: Height} {s: Slot} {Prev End: Block V}
    (hentry: MovingSlotEntryState S rho t1 M0 s Prev End)
    (hs: 0 < s) (hprop: S.E.proposer s ∈ rho.honest)
    (hhor: Protocol.vote_time S.E s ≤ rho.horizon)
    {v: V} (_hv: v ∈ rho.honest):
    (Proofs.Optimistic.voteDutyStore S rho v s).h_max - 1 ≤
      (derived_state S.E S.cfg (proposedParent S rho s)).h:= by
  let targetPre:= rho.storeBeforeTime S v (Protocol.vote_time S.E s)
  let target:= Proofs.Optimistic.voteDutyStore S rho v s
  let H:= proposedParent S rho s
  let cursor:= inclusiveEventIndex rho (Protocol.proposal_time S.E s)
  obtain ⟨EndAt, hhistory, hEnd⟩:= hentry.eventHistory
  obtain ⟨_B, _hBslot, hpemit, _hBeq⟩:=
    Proofs.Optimistic.proposalTick S adm.toScheduleWellFormed s hs hprop
      ((le_of_lt (Protocol.proposal_time_lt_vote_time S.E s)).trans hhor)
  obtain ⟨p, hpevent, _hpblock⟩:= hpemit
  have hpCursor: p < cursor:= by
    unfold cursor inclusiveEventIndex
    by_contra hnot
    have hp:= Proofs.Optimistic.filter_false_of_index_ge
      S adm.toScheduleWellFormed _ (Proofs.Optimistic.downward_le
        (Protocol.proposal_time S.E s)) (Nat.le_of_not_gt hnot) hpevent
    simp only [Event.time, decide_eq_false_iff_not, not_le] at hp
    exact lt_irrefl _ hp
  have hn0p: strictEventIndex rho t1 ≤ p:=
    filterBefore_length_le_tickIndex
      S adm.toScheduleWellFormed hpevent hentry.startTime
  have hslot:= Proofs.Optimistic.slotOf_proposal_time S.E s
  have hpactive: 0 < S.E.slotOf (Protocol.proposal_time S.E s) ∧
      Protocol.proposal_time S.E s =
        Protocol.proposal_time S.E
          (S.E.slotOf (Protocol.proposal_time S.E s)) ∧
      S.E.proposer (S.E.slotOf (Protocol.proposal_time S.E s)) =
        (S.node (S.E.proposer s)).val_index:= by
    rw [hslot]
    exact ⟨hs, rfl, (S.node_val_index (S.E.proposer s)).symm⟩
  have hpobs: HonestCanonicalObservationAtIndex S rho p 0 H:= by
    have hobs:= HonestCanonicalObservationAtIndex.proposalParent
      hprop hpevent hpactive
    rw [proposalStageParentAtIndex_eq_proposedParent
      S adm hpevent hpactive, hslot] at hobs
    exact hobs
  have hEndpH: Block.Preceq (EndAt p) H:=
    (hhistory.proposalChain p (by
      simpa only [hhistory.historyStart] using hn0p) hpCursor
        0 H (by norm_num [ProposalChainStage]) hpobs).1
  change target.h_max - 1 ≤ (derived_state S.E S.cfg H).h
  by_contra hnot
  have hhigh: (derived_state S.E S.cfg H).h < targetPre.h_max - 1:= by
    simpa only [target, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore, targetPre] using Nat.lt_of_not_ge hnot
  have hlarge: 1 < targetPre.h_max:=
    Nat.sub_pos_iff_lt.mp ((Nat.zero_le _).trans_lt hhigh)
  have hmajority: HonestWeightMajority S rho.honest:=
    AlignedRoundLemmas.honestWeightMajority_of_belowOneThird (S:= S) hfb
  obtain ⟨_W, _hWT, _Q, _X, a, ta, _hmaxW, _hQ, _hXW, _haW,
      haHon, hemit, hta, haHeight⟩:=
    Protocol.frontierQuorumWitness_stateBeforeTime
      S adm hmajority (by simpa only [targetPre] using hlarge)
  obtain ⟨j, hjevent, hja⟩:= hemit
  have hshape:= Proofs.Optimistic.emits_attest_shape S ⟨j, hjevent, hja⟩
  have hactionVote: S.a a.round < Protocol.vote_time S.E s:= by
    simpa only [← hshape.2] using hta
  have htaProposal: ta < Protocol.proposal_time S.E s:= by
    calc
      ta = S.a a.round:= hshape.2
      _ < Protocol.proposal_time S.E s:=
        action_time_lt_proposal_of_lt_vote S hactionVote
  have hjp: j < p:=
    movingEventIndex_lt_of_eventTime_lt S adm.toScheduleWellFormed
      hjevent hpevent (by simpa only [Event.time] using htaProposal)
  by_cases hj0: j < strictEventIndex rho t1
  · have hrowOld:= hhistory.oldRows haHon hjevent hja hj0 (targetPre.h_max - 1)
      (by simpa only [targetPre] using haHeight)
    have hbaseH: Block.Preceq (EndAt (strictEventIndex rho t1)) H:=
      Block.preceq_trans
        (hhistory.endpoint_mono (Nat.le_refl _) hn0p (Nat.le_of_lt hpCursor)) hEndpH
    exact (not_le_of_gt hhigh) (hrowOld.trans (Protocol.derived_h_mono S.E S.cfg hbaseH))
  · have hn0j: strictEventIndex rho t1 ≤ j:= Nat.le_of_not_gt hj0
    have hn0j': strictEventIndex rho t1 ≤ j:= by
      simpa only [hhistory.historyStart] using hn0j
    obtain ⟨G, _hGrun, hGheight, hGnext⟩:=
      (hhistory.outputs j hn0j'
          (hjp.trans hpCursor)).height_gate_sources
        haHon hjevent hja (targetPre.h_max - 1)
          (by simpa only [targetPre] using haHeight)
    have hnextp: Block.Preceq (EndAt (j + 1)) (EndAt p):=
      hhistory.endpoint_mono
        (hn0j'.trans (Nat.le_succ j))
        (Nat.succ_le_iff.mpr hjp) (Nat.le_of_lt hpCursor)
    have hrowH: targetPre.h_max - 1 ≤
        (derived_state S.E S.cfg H).h:= by
      calc
        targetPre.h_max - 1 = (derived_state S.E S.cfg G).h:=
          hGheight.symm
        _ ≤ (derived_state S.E S.cfg (EndAt (j + 1))).h:=
          Protocol.derived_h_mono S.E S.cfg hGnext
        _ ≤ (derived_state S.E S.cfg (EndAt p)).h:=
          Protocol.derived_h_mono S.E S.cfg hnextp
        _ ≤ (derived_state S.E S.cfg H).h:=
          Protocol.derived_h_mono S.E S.cfg hEndpH
    exact (not_le_of_gt hhigh) hrowH
-/


/-
/-- Between an honest proposal read and any honest vote read in the same slot,
the numeric frontier can rise by at most one. -/
theorem MovingSlotEntryState.frontier_rise_le_one_between_reads
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hfb: BelowOneThird S rho.honest)
    {t1: Time} {M0: Height} {s: Slot} {Prev End: Block V}
    (hentry: MovingSlotEntryState S rho t1 M0 s Prev End)
    (hs: 0 < s) (hprop: S.E.proposer s ∈ rho.honest)
    (hhor: Protocol.vote_time S.E s ≤ rho.horizon)
    {v: V} (hv: v ∈ rho.honest):
    (Proofs.Optimistic.voteDutyStore S rho v s).h_max ≤
      (proposerDutyStore S rho s).h_max + 1:= by
  let sourcePre:= rho.storeBeforeTime S (S.E.proposer s)
    (Protocol.proposal_time S.E s)
  let source:= proposerDutyStore S rho s
  let H:= proposedParent S rho s
  have hdepPre: DepReachableStore S.E S.hc S.cfg
      (S.node (S.E.proposer s)) sourcePre:= by
    simpa only [sourcePre, Run.storeBeforeTime] using
      (Proofs.Bridges.depReachable_stateBeforeTime S adm.toScheduleWellFormed
        adm.toDeliveryWellFormed (Protocol.proposal_time S.E s)
          (S.E.proposer s))
  have hHmem: H ∈ source.T:= by
    simpa only [source, H] using proposedParent_mem S adm s
  have hHmemPre: H ∈ sourcePre.T:= by
    simpa only [source, proposerDutyStore, Proofs.Optimistic.tickStore] using hHmem
  have hagree: DerivedStateAgrees S.E S.cfg sourcePre:=
    derivedStateAgrees_depReachable S.E S.hc S.cfg
      (S.node (S.E.proposer s)) sourcePre hdepPre
  have htree: TreeHeightsLeHMax sourcePre:=
    treeHeightsLeHMax_depReachable S.E S.hc S.cfg
      (S.node (S.E.proposer s)) hdepPre
  have hHupper: (derived_state S.E S.cfg H).h ≤ source.h_max:= by
    have hpre: (derived_state S.E S.cfg H).h ≤ sourcePre.h_max:= by
      rw [← hagree H hHmemPre]
      exact htree H hHmemPre
    simpa only [source, proposerDutyStore, Proofs.Optimistic.tickStore] using hpre
  have htarget:= hentry.voteFrontier_sub_one_le_proposedParent
    S adm hfb hs hprop hhor hv
  change (Proofs.Optimistic.voteDutyStore S rho v s).h_max ≤ source.h_max + 1
  exact (Nat.sub_le_iff_le_add.mp htarget).trans
    (Nat.add_le_add_right hHupper 1)
-/


/-
/-- Top-level form of the proposal-to-vote one-step frontier bound. -/
theorem frontier_rise_le_one_between_reads
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hfb: BelowOneThird S rho.honest)
    {t1: Time} {M0: Height} {s: Slot} {Prev End: Block V}
    (hentry: MovingSlotEntryState S rho t1 M0 s Prev End)
    (hs: 0 < s) (hprop: S.E.proposer s ∈ rho.honest)
    (hhor: Protocol.vote_time S.E s ≤ rho.horizon)
    {v: V} (hv: v ∈ rho.honest):
    (Proofs.Optimistic.voteDutyStore S rho v s).h_max ≤
      (proposerDutyStore S rho s).h_max + 1:=
  hentry.frontier_rise_le_one_between_reads
    S adm hfb hs hprop hhor hv
-/


/-
/-- The previous honest vote cone drives the next slot's proposal-free voter
walk through the moving endpoint. Removing the fresh proposal does not remove
any block on the path to `C`, because `C` is below the proposal parent. -/
theorem proposalFreeVoteWalk_passes_of_movingCone
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    {s: Slot} (hs: 0 < s)
    (hpost: S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor: Protocol.confirmation_time S.E s ≤ rho.horizon)
    {C: Block V}
    (hvotes: Proofs.Optimistic.HonestVotesCone S rho s
      (fun X => Block.Preceq C X))
    {w: V} (hw: w ∈ rho.honest)
    (hinputs: GoldfishConeVoteInputs' S rho s C w)
    (hCparent: Block.Preceq C (proposedParent S rho (s + 1))):
    Block.Preceq C
      (Protocol.ghost
        (Proofs.Optimistic.healAnchor S.E S.hc
          (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing)
        (proposalWalkTargetTree S rho (s + 1) w)
        (proposalWalkTargetScore S rho (s + 1) w)
        (proposalWalkTargetEligible S rho (s + 1) w)):= by
  let duty:= Proofs.Optimistic.voteDutyStore S rho w (s + 1)
  let B:= proposedBlock S rho (s + 1)
  let H:= proposedParent S rho (s + 1)
  let tree:= (Proofs.Optimistic.voter_candidate_tree S.E duty.toHealing).erase B
  let votes:= Protocol.voter_view S.E duty.toHealing.toFG.toSG.toGoldfishStore duty.s
  let support:= Protocol.voter_support_view S.E duty.toHealing.toFG.toSG.toGoldfishStore duty.s
  rcases hinputs.rootSide with hrootBelow | hbelowRoot
  · have hpathData:= goldfishCone_pathEligible
      S adm hcom hs hpost hhor hvotes hw
        { candidate:= hrootBelow.2.1
          root:= hrootBelow.1
          anchor:= hinputs.anchor
          path:= hrootBelow.2.2 }
    have hslot: duty.s = s + 1:=
      Proofs.Optimistic.voteDutyStore_slot S rho w (s + 1)
    have hpath: ∀ D: Block V,
        Block.Preceq (Proofs.Optimistic.healAnchor S.E S.hc duty.toHealing) D →
        D ≠ Proofs.Optimistic.healAnchor S.E S.hc duty.toHealing →
        Block.Preceq D C → D ∈ tree:= by
      intro D hanchorD hDne hDC
      have hDfull:= (hpathData.2.2 D hanchorD hDne hDC).1
      have hDneB: D ≠ B:= by
        intro hEq
        subst D
        have hBdepth: (proposedBlock S rho (s + 1)).depth =
            (proposedParent S rho (s + 1)).depth + 1:= by
          simpa only using
            depth_of_parent? (proposedBlock_parent S rho (s + 1))
        have hBdepthLeC:= Block.preceq_depth_le (by
          simpa only [B] using hDC)
        have hCdepthLeH:= Block.preceq_depth_le hCparent
        omega
      exact Finset.mem_erase.mpr ⟨hDneB, by
        simpa only [duty] using hDfull⟩
    have hpass:= goldfish_fork_choice_captures_supporter_majority
      S.E duty.toHealing.σ duty.toHealing.h_max duty.toHealing.T tree
        duty.toHealing.s votes support s
        (Proofs.Optimistic.ConeSupport.sub hpathData.1) hpathData.2.1
        hinputs.anchor (fun _ => hpath)
    simpa only [Protocol.goldfish_fork_choice, duty, B, tree, votes, support,
      Protocol.Store.toHealing, hslot, Nat.add_sub_cancel,
      proposalWalkTargetTree, proposalWalkTargetScore,
      proposalWalkTargetEligible] using hpass
  · have hrootAnchor: Block.Preceq
        (Protocol.get_fg_root duty.toHealing.toFG)
        (Proofs.Optimistic.healAnchor S.E S.hc duty.toHealing):= by
      rw [Proofs.Optimistic.healAnchor_eq_get_sg_root]
      exact StoreFinality.get_fg_root_preceq_get_sg_root
        S.E S.hc duty
    have hanchorGhost: Block.Preceq
        (Proofs.Optimistic.healAnchor S.E S.hc duty.toHealing)
        (Protocol.ghost
          (Proofs.Optimistic.healAnchor S.E S.hc duty.toHealing)
          tree
          (proposalWalkTargetScore S rho (s + 1) w)
          (proposalWalkTargetEligible S rho (s + 1) w)):=
      Protocol.ghost_preceq _ _ _ _
    have hpass: Block.Preceq C
        (Protocol.ghost
          (Proofs.Optimistic.healAnchor S.E S.hc duty.toHealing)
          tree
          (proposalWalkTargetScore S rho (s + 1) w)
          (proposalWalkTargetEligible S rho (s + 1) w)):=
      Block.preceq_trans (Block.preceq_trans (by
        simpa only [duty] using hbelowRoot) hrootAnchor) hanchorGhost
    simpa only [duty, B, tree, proposalWalkTargetTree] using hpass
-/


/-
/-- The moving vote cone supplies the target prefix, and a pivot inside both
duty-store viability bands supplies the frozen suffix. Together they transfer
the next honest proposal walk without a fixed-frontier equality. -/
theorem proposalWalkTransferred_of_movingConeBands
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    {s: Slot} (hs: 0 < s)
    (hpost: S.E.t_GST ≤ Protocol.proposal_time S.E s)
    (hhor: Protocol.confirmation_time S.E s ≤ rho.horizon)
    {pivot: Block V}
    (hvotes: Proofs.Optimistic.HonestVotesCone S rho s
      (fun X => Block.Preceq pivot X))
    (hprop: S.E.proposer (s + 1) ∈ rho.honest)
    {v: V} (hv: v ∈ rho.honest)
    (hvoteHor: Protocol.vote_time S.E (s + 1) ≤ rho.horizon)
    (hpivotParent: Block.Preceq pivot
      (proposedParent S rho (s + 1)))
    (hinputs: GoldfishConeVoteInputs' S rho s pivot v)
    (hband: FrozenProposalSuffixBandInputs S rho (s + 1) pivot v):
    ProposalWalkTransferred S rho (s + 1)
      (proposedBlock S rho (s + 1))
      (proposedParent S rho (s + 1)) v:= by
  have hpostVote: S.E.t_GST ≤ Protocol.vote_time S.E s:=
    hpost.trans (le_of_lt (Protocol.proposal_time_lt_vote_time S.E s))
  have htargetPasses:= proposalFreeVoteWalk_passes_of_movingCone
    S adm hcom hs hpostVote hhor hvotes hv hinputs hpivotParent
  have hpost': S.E.t_GST ≤
      Protocol.proposal_time S.E (s + 1 - 1):= by
    simpa only [Nat.add_sub_cancel] using hpost
  exact proposalWalkTransferred_of_riseLeOne_of_targetPasses
    S adm (Nat.succ_pos s) hpost' hprop hv hvoteHor
      hpivotParent htargetPasses hband
-/


/-
/-- The moving event history closes the one-unit-rise escape in the proposal
transfer. The source duty frontier is bounded by the event-prefix honest
frontier, and a crossing row for the later voter frontier is already below the
same endpoint. Thus the endpoint is in both viability bands, even when the
voter frontier is exactly one unit above the proposer frontier. -/
theorem MovingFrontierChainState.proposalWalkTransferred_of_sourceFloor
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hfb: BelowOneThird S rho.honest)
    {t1: Time} {M0: Height} {n0 i: Nat} {End: Nat → Block V}
    (h: MovingFrontierChainState S rho t1 M0 n0 i End)
    {s: Slot} (hs: 0 < s)
    (hpost: S.E.t_GST ≤ Protocol.proposal_time S.E s)
    (hhor: Protocol.confirmation_time S.E s ≤ rho.horizon)
    (hprop: S.E.proposer (s + 1) ∈ rho.honest)
    (hevent: rho.events[i]? = some
      (Event.tick (S.E.proposer (s + 1))
        (Protocol.proposal_time S.E (s + 1))))
    {v: V} (hv: v ∈ rho.honest)
    (hvoteHor: Protocol.vote_time S.E (s + 1) ≤ rho.horizon)
    (hpivotParent: Block.Preceq (End i)
      (proposedParent S rho (s + 1)))
    (hvotes: Proofs.Optimistic.HonestVotesCone S rho s
      (fun X => Block.Preceq (End i) X))
    (hinputs: GoldfishConeVoteInputs' S rho s (End i) v)
    (hcore: FrozenProposalSuffixCoreInputs S rho (s + 1) (End i) v):
    ProposalWalkTransferred S rho (s + 1)
      (proposedBlock S rho (s + 1))
      (proposedParent S rho (s + 1)) v:= by
  have hmajority: HonestWeightMajority S rho.honest:=
    AlignedRoundLemmas.honestWeightMajority_of_belowOneThird (S:= S) hfb
  have hglobalFloor: honestHMaxBeforeIndex S rho i - 1 ≤
      (derived_state S.E S.cfg (End i)).h:=
    h.frontier_sub_one_le_endpointHeight S adm hmajority
  have hlocal: (rho.stateBefore S i (S.E.proposer (s + 1))).st.h_max ≤
      honestHMaxBeforeIndex S rho i:=
    localHMax_le_honestHMaxBeforeIndex S rho i hprop
  have hstate:= Proofs.Optimistic.stateBefore_tick_eq_stateBeforeTime
    S adm.toScheduleWellFormed hevent
  have hsourceLe: (proposerDutyStore S rho (s + 1)).h_max ≤
      honestHMaxBeforeIndex S rho i:= by
    rw [hstate] at hlocal
    simpa only [proposerDutyStore, Proofs.Optimistic.tickStore,
      Run.storeBeforeTime] using hlocal
  have hsourceBand: (proposerDutyStore S rho (s + 1)).h_max - 1 ≤
      (derived_state S.E S.cfg (End i)).h:=
    (Nat.sub_le_sub_right hsourceLe 1).trans hglobalFloor
  have htargetBand:
      (Proofs.Optimistic.voteDutyStore S rho v (s + 1)).h_max - 1 ≤
        (derived_state S.E S.cfg (End i)).h:=
    h.voteFrontier_sub_one_le_endpointAtProposal S adm hfb hevent hv
  exact proposalWalkTransferred_of_movingConeBands
    S adm hcom hs hpost hhor hvotes hprop hv hvoteHor hpivotParent
      hinputs
      { toFrozenProposalSuffixCoreInputs:= hcore
        sourceBand:= hsourceBand
        targetBand:= htargetBand }
-/


/-
/-- Under a one-step proposal-to-vote frontier bound, either the local
frontier has risen by exactly one or the next honest proposal walk transfers.
The second branch needs only a source-band pivot: if there is no local rise,
the target viability band is no higher than the source band. -/
theorem proposalWalkTransferred_of_riseLeOne
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    {s: Slot} (hs: 0 < s)
    (hpost: S.E.t_GST ≤ Protocol.proposal_time S.E s)
    (hhor: Protocol.confirmation_time S.E s ≤ rho.horizon)
    {pivot: Block V}
    (hvotes: Proofs.Optimistic.HonestVotesCone S rho s
      (fun X => Block.Preceq pivot X))
    (hprop: S.E.proposer (s + 1) ∈ rho.honest)
    {v: V} (hv: v ∈ rho.honest)
    (hvoteHor: Protocol.vote_time S.E (s + 1) ≤ rho.horizon)
    (hpivotParent: Block.Preceq pivot
      (proposedParent S rho (s + 1)))
    (hinputs: GoldfishConeVoteInputs' S rho s pivot v)
    (hcore: FrozenProposalSuffixCoreInputs S rho (s + 1) pivot v)
    (hsourceBand: (proposerDutyStore S rho (s + 1)).h_max - 1 ≤
      (derived_state S.E S.cfg pivot).h)
    (hriseLeOne: (Proofs.Optimistic.voteDutyStore S rho v (s + 1)).h_max ≤
      (proposerDutyStore S rho (s + 1)).h_max + 1):
    ProposalWalkTransferred S rho (s + 1)
        (proposedBlock S rho (s + 1))
        (proposedParent S rho (s + 1)) v ∨
      (Proofs.Optimistic.voteDutyStore S rho v (s + 1)).h_max =
        (proposerDutyStore S rho (s + 1)).h_max + 1:= by
  by_cases hrise: (proposerDutyStore S rho (s + 1)).h_max <
      (Proofs.Optimistic.voteDutyStore S rho v (s + 1)).h_max
  · exact Or.inr
      (Nat.le_antisymm hriseLeOne (Nat.succ_le_iff.mpr hrise))
  · have htargetLe: (Proofs.Optimistic.voteDutyStore S rho v (s + 1)).h_max ≤
        (proposerDutyStore S rho (s + 1)).h_max:= Nat.le_of_not_gt hrise
    have htargetBand:
        (Proofs.Optimistic.voteDutyStore S rho v (s + 1)).h_max - 1 ≤
          (derived_state S.E S.cfg pivot).h:=
      (Nat.sub_le_sub_right htargetLe 1).trans hsourceBand
    exact Or.inl (proposalWalkTransferred_of_movingConeBands
      S adm hcom hs hpost hhor hvotes hprop hv hvoteHor hpivotParent
        hinputs
        { toFrozenProposalSuffixCoreInputs:= hcore
          sourceBand:= hsourceBand
          targetBand:= htargetBand })
-/

/-! ## Named prepared-read adapters -/




end HealingSurface
end Proofs
end DecoupledConsensusModel

end
