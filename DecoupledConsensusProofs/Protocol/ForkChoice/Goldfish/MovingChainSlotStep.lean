module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Schedule.MovingChainFold
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.HeightProgressCompose
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.AdoptionRun

@[expose] public section

/-!
# The moving-chain slot step, assembled

`MovingChainFoldRun` proves the four inputs of
`movingSlotWindowFacts_of_readInputs` separately, each from the slot-entry
state. This module puts them together, so one call turns a slot-entry state
into the window facts of its own slot, and a second turns those into the entry
state of the next slot.

The window endpoint is chosen here: it is the deepest of the entry endpoint and
the slot-`(s-1)` genuine confirmations, which exists because the entry state
already knows those confirmations are compatible with its endpoint.
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

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}

/-- The timing a slot window needs at its confirmation instant, when that
instant is also a Section 7 action. Every clause is a schedule fact about the
round whose action lands there. -/
def MovingSlotActionTiming
    (S : Setup V) (rho : Run V) (t1 : Time) (c : Slot) : Prop :=
  ∀ q : Round, S.a q = Protocol.confirmation_time S.E c →
    0 < q ∧ S.E.t_GST ≤ S.a (q - 1) ∧
      S.hc.Γ_neg1 S.E.Δ q ≤ rho.horizon ∧
      t1 ≤ S.a (q - 1) ∧ S.a (q - 1) ≤ rho.horizon ∧
      S.a (q - 1) < Protocol.proposal_time S.E (c + 1)

private theorem movingFrontierChainStateN_endpoint_mono
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

private theorem movingFrontierChainStateN_initialHeight_le_endpointHeight_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {t1 : Time} {M0 : Height} {n0 i : Nat} {End : Nat → Block V}
    (h : MovingFrontierChainStateN S rho t1 M0 n0 i End)
    {E0 Ei : NamedBlock V}
    (hE0 : E0.erase = End n0) (hEi : Ei.erase = End i)
    (hE0run : RunBlock S rho E0) (hEirun : RunBlock S rho Ei) :
    (Protocol.derive_named S.E S.cfg E0).h ≤
      (Protocol.derive_named S.E S.cfg Ei).h := by
  have hgeom : Block.Preceq E0.erase Ei.erase := by
    simpa only [hE0, hEi] using
      movingFrontierChainStateN_endpoint_mono h
        (Nat.le_refl n0) h.start_le (Nat.le_refl i)
  have hnamed : NamedBlock.Preceq E0 Ei :=
    Protocol.namedPreceq_of_runBlock_erase_preceq adm hE0run hEirun hgeom
  exact Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hnamed

private theorem movingFrontierChainStateN_oldRow_le_endpointHeight_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {t1 : Time} {M0 : Height} {n0 i : Nat} {End : Nat → Block V}
    (h : MovingFrontierChainStateN S rho t1 M0 n0 i End)
    {j : Nat} {a : NamedAttestation V} {time : Time}
    (ha : a.val_index ∈ rho.honest)
    (hevent : rho.events[j]? = some (Event.tick a.val_index time))
    (hemit : Object.attest a ∈
      NamedRun.emittedAt S rho j a.val_index time)
    (hj : j < n0) {hh : Height}
    (hrow : a.height_pair.erase.height? = some hh)
    {E : NamedBlock V} (hE : E.erase = End i) (hErun : RunBlock S rho E) :
    hh ≤ (Protocol.derive_named S.E S.cfg E).h := by
  obtain ⟨E0, hE0, hE0run⟩ :=
    h.endpointRun n0 (Nat.le_refl n0) h.start_le
  exact (h.oldRows_named ha hevent hemit hj hh hrow E0 hE0 hE0run).trans
    (movingFrontierChainStateN_initialHeight_le_endpointHeight_named
      S adm h hE0 hE hE0run hErun)

private theorem movingFrontierChainStateN_gateOnRoot_preceq_of_boundary
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
        rw [hhj]; exact hz)
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
        (movingFrontierChainStateN_endpoint_mono h
          (Nat.le_refl n0) h.start_le (Nat.le_refl i))
    · have hn0j : n0 ≤ j := Nat.le_of_not_gt hj0
      have hJnext : Block.Preceq J.erase (End (j + 1)) :=
        (h.outputs j hn0j hji).targets haHonest hjevent hja
          st.core.h_j st.core.J.root haTarget J hJrun (by rw [hJerase])
      exact Block.preceq_trans hJnext
        (movingFrontierChainStateN_endpoint_mono h
          (hn0j.trans (Nat.le_succ j))
          (Nat.succ_le_iff.mpr hji) (Nat.le_refl i))

private theorem movingFrontierChainStateN_readFrontier_sub_one_le_endpointAtCursor_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {t1 : Time} {M0 : Height} {n0 k : Nat} {End : Nat → Block V}
    (h : MovingFrontierChainStateN S rho t1 M0 n0 k End)
    {s : Slot} {t : Time}
    (hsep : ∀ q : Round, S.a q < t → S.a q < Protocol.proposal_time S.E s)
    (hcursor : strictEventIndex rho (Protocol.proposal_time S.E s) ≤ k)
    {v : V} (_hv : v ∈ rho.honest)
    {E : NamedBlock V} (hE : E.erase = End k) (hErun : RunBlock S rho E) :
    (rho.storeBeforeTime S v t).core.h_max - 1 ≤
      (Protocol.derive_named S.E S.cfg E).h := by
  let targetPre := rho.storeBeforeTime S v t
  change targetPre.core.h_max - 1 ≤
    (Protocol.derive_named S.E S.cfg E).h
  by_contra hnot
  have hhigh : (Protocol.derive_named S.E S.cfg E).h <
      targetPre.core.h_max - 1 :=
    Nat.lt_of_not_ge hnot
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
  have haction : S.a a.round < t := by
    simpa only [← hshape.2] using hta
  have htaProposal : ta < Protocol.proposal_time S.E s := by
    rw [hshape.2]
    exact hsep a.round haction
  have hjk : j < k :=
    (emission_index_lt_beforeTime_prefix
      S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hjevent htaProposal).trans_le
      hcursor
  by_cases hj0 : j < n0
  · exact (not_le_of_gt hhigh)
      (movingFrontierChainStateN_oldRow_le_endpointHeight_named
        S adm h haHon hjevent hja hj0
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
      movingFrontierChainStateN_endpoint_mono h
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

/-- The named read frontier floor at a moving endpoint cursor. -/
theorem MovingFrontierChainStateN.readFrontier_sub_one_le_endpointAtCursor_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {t1 : Time} {M0 : Height} {n0 k : Nat} {End : Nat → Block V}
    (h : MovingFrontierChainStateN S rho t1 M0 n0 k End)
    {s : Slot} {t : Time}
    (hsep : ∀ q : Round, S.a q < t → S.a q < Protocol.proposal_time S.E s)
    (hcursor : strictEventIndex rho (Protocol.proposal_time S.E s) ≤ k)
    {v : V} (hv : v ∈ rho.honest)
    {E : NamedBlock V} (hE : E.erase = End k) (hErun : RunBlock S rho E) :
    (rho.storeBeforeTime S v t).core.h_max - 1 ≤
      (Protocol.derive_named S.E S.cfg E).h :=
  movingFrontierChainStateN_readFrontier_sub_one_le_endpointAtCursor_named
    S adm hfb h hsep hcursor hv hE hErun

/-- Honest previous-round action carriers are below a named moving endpoint. -/
theorem MovingFrontierChainStateN.previousActionCarriersPreceqAtRead
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {t1 : Time} {M0 : Height} {n0 i : Nat} {End : Nat → Block V}
    (h : MovingFrontierChainStateN S rho t1 M0 n0 i End)
    {r : Round} {t : Time}
    (ht1 : t1 ≤ S.a r)
    (hhor : S.a r ≤ rho.horizon)
    (hbefore : S.a r < t)
    (hcursor : strictEventIndex rho t ≤ i) :
    ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u r) (End i) := by
  intro u hu
  obtain ⟨j, hj, hout⟩ :=
    honest_emits_exact_actionAttestationAt S adm hu r hhor
  have hji : j < i :=
    (emission_index_lt_beforeTime_prefix S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hj hbefore).trans_le hcursor
  have hn0j : n0 ≤ j := by
    rw [h.historyStart]
    exact filterBefore_length_le_tickIndex S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hj ht1
  exact Block.preceq_trans ((h.sgCarriers j hn0j hji) hu hj hout)
    (movingFrontierChainStateN_endpoint_mono h
      (hn0j.trans (Nat.le_succ j))
      (Nat.succ_le_iff.mpr hji) (Nat.le_refl i))

private theorem movingChainStep_named_preceq_cases_endpoint
    {A B : NamedBlock V} (h : NamedBlock.Preceq A B) :
    A = B ∨ NamedBlock.Preceq A B.parent := by
  cases B with
  | genesis =>
      left
      simpa only [NamedBlock.Preceq, NamedBlock.preceq, decide_eq_true_eq] using h
  | node parent slot root votes support rows proposer =>
      simpa only [NamedBlock.Preceq, NamedBlock.preceq, NamedBlock.parent,
        Bool.or_eq_true, decide_eq_true_eq] using h

private theorem movingChainStep_named_chain_attestations_own_endpoint
    {A : NamedBlock V} {a : NamedAttestation V}
    (ha : a ∈ A.attestations) :
    a ∈ Protocol.named_chain_attestations A := by
  cases A with
  | genesis => simp [NamedBlock.attestations] at ha
  | node p s r gv gsv rows proposer =>
      exact Finset.mem_union_right _ (List.mem_toFinset.mpr ha)

private theorem movingChainStep_named_chain_attestations_mono_endpoint
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
      rcases movingChainStep_named_preceq_cases_endpoint hAB with rfl | hAp
      · exact Finset.Subset.refl _
      · exact (ih hAp).trans Finset.subset_union_left

private theorem movingChainStep_named_chain_attestations_of_carrier_endpoint
    {carrier D : NamedBlock V} {a : NamedAttestation V}
    (hcarrier : NamedBlock.Preceq carrier D)
    (ha : a ∈ carrier.attestations) :
    a ∈ Protocol.named_chain_attestations D :=
  movingChainStep_named_chain_attestations_mono_endpoint hcarrier
    (movingChainStep_named_chain_attestations_own_endpoint ha)

private theorem movingChainStep_action_time_normal
    (S : Setup V) (q : Round) :
    S.a q = (4 * ((S.hc.opening_slot q : Slot) : Time) + 6) * S.E.Δ := by
  unfold Setup.a Protocol.HealConfig.a slotStart
  ring

private theorem movingChainStep_confirmation_time_normal
    (E : Env V) (s : Slot) :
    Protocol.confirmation_time E s = (4 * (s : Time) + 6) * E.Δ := by
  unfold Protocol.confirmation_time Env.t slotStart
  ring

private theorem movingChainStep_proposal_time_normal
    (E : Env V) (s : Slot) :
    Protocol.proposal_time E s = (4 * (s : Time) + 0) * E.Δ := by
  unfold Protocol.proposal_time Env.t slotStart
  ring

private theorem movingChainStep_action_time_lt_proposal_of_lt_confirmation
    (S : Setup V) {r : Round} {c : Slot}
    (hlt : S.a r < Protocol.confirmation_time S.E c) :
    S.a r < Protocol.proposal_time S.E (c + 1) := by
  rw [movingChainStep_action_time_normal] at hlt ⊢
  rw [movingChainStep_confirmation_time_normal] at hlt
  rw [movingChainStep_proposal_time_normal]
  have hnum : 4 * ((S.hc.opening_slot r : Slot) : Int) + 6 <
      4 * ((c : Slot) : Int) + 6 := by
    by_contra hnot
    exact absurd hlt (not_lt_of_ge
      (Int.mul_le_mul_of_nonneg_right (le_of_not_gt hnot)
        (le_of_lt S.E.Δ_pos)))
  have hnum2 : 4 * ((S.hc.opening_slot r : Slot) : Int) + 6 <
      4 * ((c + 1 : Slot) : Int) + 0 := by
    push_cast at hnum ⊢
    omega
  exact Int.mul_lt_mul_of_pos_right hnum2 S.E.Δ_pos

private theorem movingChainStep_proposal_time_succ_le_confirmation_time
    (E : Env V) (s : Slot) :
    Protocol.proposal_time E (s + 1) ≤ Protocol.confirmation_time E s := by
  rw [movingChainStep_proposal_time_normal,
    movingChainStep_confirmation_time_normal]
  refine Int.mul_le_mul_of_nonneg_right ?_ (le_of_lt E.Δ_pos)
  push_cast
  omega

private theorem movingFrontierChainStateN_readRoot_preceq_endpointAtCursor_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {t1 : Time} {M0 : Height} {n0 k : Nat} {End : Nat → Block V}
    (h : MovingFrontierChainStateN S rho t1 M0 n0 k End)
    {s : Slot} {t : Time}
    (hsep : ∀ q : Round, S.a q < t → S.a q < Protocol.proposal_time S.E s)
    (hcursor : strictEventIndex rho (Protocol.proposal_time S.E s) ≤ k)
    {v : V} (hv : v ∈ rho.honest)
    (hstart : t1 ≤ t)
    {E : NamedBlock V} (hE : E.erase = End k) (hErun : RunBlock S rho E) :
    Block.Preceq (Protocol.get_fg_root
      (rho.storeBeforeTime S v t).core.toHealing.toFG) E.erase := by
  let pre := rho.storeBeforeTime S v t
  have hbelow : pre.core.h_j < pre.core.h_max :=
    NamedJustificationBound.justificationBelowMax_stateBeforeTime S rho t v
  have hmajority : HonestWeightMajority S rho.honest :=
    AlignedRoundLemmas.honestWeightMajority_of_belowOneThird (S := S) hfb
  have hsb : SlashableBound S rho :=
    slashableBound_of_admissible_belowOneThird S adm hfb
  have hendFloor : pre.core.h_max - 1 ≤
      (Protocol.derive_named S.E S.cfg E).h := by
    simpa only [pre] using
      movingFrontierChainStateN_readFrontier_sub_one_le_endpointAtCursor_named
        S adm hfb h hsep hcursor hv hE hErun
  have hn0 : n0 ≤ strictEventIndex rho t := by
    rw [h.historyStart]
    exact strictEventIndex_mono rho hstart
  have hfloorM : M0 ≤ pre.core.h_max := by
    have hfl := h.frontierFloor v hv (strictEventIndex rho t) hn0
    rw [← storeBeforeTime_eq_stateBefore_strictEventIndex
      S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed v t] at hfl
    simpa only [pre] using hfl
  by_cases hgate : pre.core.h_max = pre.core.h_j + 1
  · obtain ⟨C, hCbody, hJ, hhj⟩ :=
      Proofs.Bridges.storeJustificationOnChain_stateBeforeTime S rho t v
    have hCbody' : C ∈ pre.bodies := by simpa only [pre] using hCbody
    have hJpre : (Protocol.derive_named S.E S.cfg C).J = pre.core.J := by
      simpa only [pre, Run.storeBeforeTime] using hJ
    have hhjpre : (Protocol.derive_named S.E S.cfg C).h_j =
        pre.core.h_j := by
      simpa only [pre, Run.storeBeforeTime] using hhj
    have hCbodyN : C ∈
        (rho.stateBefore S (strictEventIndex rho t) v).st.bodies := by
      rw [← storeBeforeTime_eq_stateBefore_strictEventIndex
        S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed v t]
      exact hCbody'
    have hCrun : RunBlock S rho C :=
      Proofs.Bridges.runBlock_of_stateBefore_mem S hv hCbodyN
    have hJmem : pre.core.J ∈ pre.core.T :=
      Proofs.NamedStoreBridge.justifiedInTree_stateBeforeTime S rho t v
    obtain ⟨J, hJbody, hJerase⟩ :=
      Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho t v hJmem
    have hJbodyN : J ∈
        (rho.stateBefore S (strictEventIndex rho t) v).st.bodies := by
      rw [← storeBeforeTime_eq_stateBefore_strictEventIndex
        S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed v t]
      simpa only [pre] using hJbody
    have hJrun : RunBlock S rho J :=
      Proofs.Bridges.runBlock_of_stateBefore_mem S hv hJbodyN
    have hrow : pre.core.h_j ≠ 0 →
        ∃ (a : NamedAttestation V) (ta : Time) (j : Nat),
          a.val_index ∈ rho.honest ∧
          rho.events[j]? = some (Event.tick a.val_index ta) ∧
          Object.attest a ∈ NamedRun.emittedAt S rho j a.val_index ta ∧
          a.height_pair = NamedHeightPair.vote pre.core.h_j pre.core.J.root false ∧
          j < k := by
      intro hz
      have hhjNe : (Protocol.derive_named S.E S.cfg C).h_j ≠ 0 := by
        rw [hhj]
        exact hz
      obtain ⟨J, hJD, hJeraseC, Q, hQ, hwitness⟩ :=
        NamedJustificationCertificates.justification_certificate S.E S.cfg C hhjNe
      obtain ⟨signer, hsignerQ, hsignerHonest⟩ :=
        HonestWeightMajority.exists_honest_member_of_quorum hmajority hQ
      obtain ⟨carrier, a, hcarrier, ha, haSigner, haPair⟩ :=
        hwitness signer hsignerQ
      have haHonest : a.val_index ∈ rho.honest := by
        rw [haSigner]
        exact hsignerHonest
      have haChain : a ∈ Protocol.named_chain_attestations C :=
        movingChainStep_named_chain_attestations_of_carrier_endpoint hcarrier ha
      have hrootJ : J.root = pre.core.J.root := by
        rw [← Proofs.NamedWire.erase_root J, hJeraseC, hJpre]
      have haTarget : a.height_pair =
          NamedHeightPair.vote pre.core.h_j pre.core.J.root false := by
        rw [← hhjpre, ← hrootJ]
        exact haPair
      have hCbodyN' : C ∈
          (rho.stateBefore S (strictEventIndex rho t) v).st.bodies := hCbodyN
      obtain ⟨j, ta, hj, hjevent, hja, _hemit⟩ :=
        honestCarriedAttestation_emittedBeforeIndex S adm hCbodyN' haChain haHonest
      have hta : ta < t := time_lt_of_index_lt_strictEventIndex S
        adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hj hjevent
      have hshape := Proofs.Optimistic.emits_attest_shape S
        (⟨j, hjevent, hja⟩ : rho.emits S a.val_index (Object.attest a) ta)
      have haction : S.a a.round < t := by
        simpa only [← hshape.2] using hta
      have htaProposal : ta < Protocol.proposal_time S.E s := by
        rw [hshape.2]
        exact hsep a.round haction
      have hjk : j < k :=
        (emission_index_lt_beforeTime_prefix S
          adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hjevent htaProposal).trans_le
          hcursor
      exact ⟨a, ta, j, haHonest, hjevent, hja, haTarget, hjk⟩
    have hgateRoot : Block.Preceq
        (Protocol.get_fg_root pre.core.toHealing.toFG) (End k) := by
      exact movingFrontierChainStateN_gateOnRoot_preceq_of_boundary
        (S := S) (rho := rho) (adm := adm) (t1 := t1) (M0 := M0)
        (n0 := n0) (i := k) (End := End) (h := h) (st := pre)
        (C := C) (J := J) hhjpre hJpre hJrun hJerase hfloorM hgate hrow
    simpa only [pre, hE] using hgateRoot
  · obtain ⟨C, hCbody, hCF, _hCheight⟩ :=
      Proofs.Bridges.storeFinalizationOnChain_stateBeforeTime S rho t v
    have hCbody' : C ∈ pre.bodies := by simpa only [pre] using hCbody
    have hCbodyN : C ∈
        (rho.stateBefore S (strictEventIndex rho t) v).st.bodies := by
      rw [← storeBeforeTime_eq_stateBefore_strictEventIndex
        S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed v t]
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
      NamedJustificationBound.noHighJustifications_stateBeforeTime S rho t v
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
    simp only [Protocol.get_fg_root, Protocol.Store.toHealing,
      if_neg (by simpa only [pre] using hgate)]
    simpa only [pre] using hFEnd

private theorem movingFrontierChainStateN_confFrontier_sub_one_le_endpointAtCursor_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {t1 : Time} {M0 : Height} {n0 k : Nat} {End : Nat → Block V}
    (h : MovingFrontierChainStateN S rho t1 M0 n0 k End)
    {c : Slot}
    (hcursor : strictEventIndex rho (Protocol.proposal_time S.E (c + 1)) ≤ k)
    {v : V} (hv : v ∈ rho.honest)
    {E : NamedBlock V} (hE : E.erase = End k)
    (hErun : RunBlock S rho E) :
    (rho.storeBeforeTime S v (Protocol.confirmation_time S.E c)).core.h_max - 1 ≤
      (Protocol.derive_named S.E S.cfg E).h :=
  movingFrontierChainStateN_readFrontier_sub_one_le_endpointAtCursor_named
    S adm hfb h
    (fun _q hq => movingChainStep_action_time_lt_proposal_of_lt_confirmation S hq)
    hcursor hv hE hErun

private theorem movingFrontierChainStateN_confRoot_preceq_endpointAtCursor_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {t1 : Time} {M0 : Height} {n0 k : Nat} {End : Nat → Block V}
    (h : MovingFrontierChainStateN S rho t1 M0 n0 k End)
    {c : Slot}
    (hcursor : strictEventIndex rho (Protocol.proposal_time S.E (c + 1)) ≤ k)
    {v : V} (hv : v ∈ rho.honest)
    (hstart : t1 ≤ Protocol.proposal_time S.E (c + 1))
    {E : NamedBlock V} (hE : E.erase = End k)
    (hErun : RunBlock S rho E) :
    Block.Preceq
      (Protocol.get_fg_root
        (rho.storeBeforeTime S v
          (Protocol.confirmation_time S.E c)).core.toHealing.toFG) E.erase :=
  movingFrontierChainStateN_readRoot_preceq_endpointAtCursor_named S adm hfb h
    (fun _q hq => movingChainStep_action_time_lt_proposal_of_lt_confirmation S hq)
    hcursor hv
    (hstart.trans (movingChainStep_proposal_time_succ_le_confirmation_time S.E c))
    hE hErun

private theorem movingFrontierChainStateN_voteRoot_preceq_endpointAtCursor_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {t1 : Time} {M0 : Height} {n0 k : Nat} {End : Nat → Block V}
    (h : MovingFrontierChainStateN S rho t1 M0 n0 k End)
    {s : Slot}
    (hcursor : strictEventIndex rho (Protocol.proposal_time S.E s) ≤ k)
    {v : V} (hv : v ∈ rho.honest)
    (hstart : t1 ≤ Protocol.proposal_time S.E s)
    {E : NamedBlock V} (hE : E.erase = End k)
    (hErun : RunBlock S rho E) :
    Block.Preceq
      (Protocol.get_fg_root
        (rho.storeBeforeTime S v
          (Protocol.vote_time S.E s)).core.toHealing.toFG) E.erase :=
  movingFrontierChainStateN_readRoot_preceq_endpointAtCursor_named S adm hfb h
    (fun _q hq => Protocol.action_time_lt_proposal_of_lt_vote S hq)
    hcursor hv
    (hstart.trans (le_of_lt (Protocol.proposal_time_lt_vote_time S.E s)))
    hE hErun

private theorem movingFrontierChainStateN_prefix
    {S : Setup V} {rho : Run V} {t1 : Time} {M0 : Height}
    {n0 i : Nat} {End : Nat → Block V}
    (h : MovingFrontierChainStateN S rho t1 M0 n0 i End)
    {m : Nat} (hm : n0 ≤ m) (hmi : m ≤ i) :
    MovingFrontierChainStateN S rho t1 M0 n0 m End := by
  refine
    { historyStart := h.historyStart
      start_le := hm
      endpointRun := ?_
      endpointMono := ?_
      proposalChain := ?_
      genuineConfirmations := ?_
      sgCarriers := ?_
      outputs := ?_
      anchors := ?_
      oldRows_named := h.oldRows_named
      frontierFloor := h.frontierFloor
      boundaryTargets := h.boundaryTargets }
  · intro j hj hjm
    exact h.endpointRun j hj (hjm.trans hmi)
  · intro j hj hjm
    exact h.endpointMono j hj (Nat.lt_of_lt_of_le hjm hmi)
  · intro j hj hjm
    exact h.proposalChain j hj (Nat.lt_of_lt_of_le hjm hmi)
  · intro j hj hjm
    exact h.genuineConfirmations j hj (Nat.lt_of_lt_of_le hjm hmi)
  · intro j hj hjm
    exact h.sgCarriers j hj (Nat.lt_of_lt_of_le hjm hmi)
  · intro j hj hjm
    exact h.outputs j hj (Nat.lt_of_lt_of_le hjm hmi)
  · intro j hj hjm
    exact h.anchors j hj (Nat.lt_of_lt_of_le hjm hmi)

/-! The N cursor bridges are exported for the ceiling fold. The underlying
proofs stay local to this module; these wrappers keep the compatibility cursor
surface unchanged while allowing later N records to use the same route. -/

theorem MovingFrontierChainStateN.endpoint_mono
    {S : Setup V} {rho : Run V} {t1 : Time} {M0 : Height}
    {n0 i : Nat} {End : Nat → Block V}
    (h : MovingFrontierChainStateN S rho t1 M0 n0 i End)
    {j k : Nat} (hj : n0 ≤ j) (hjk : j ≤ k) (hki : k ≤ i) :
    Block.Preceq (End j) (End k) :=
  movingFrontierChainStateN_endpoint_mono h hj hjk hki

theorem MovingFrontierChainStateN.prefix
    {S : Setup V} {rho : Run V} {t1 : Time} {M0 : Height}
    {n0 i : Nat} {End : Nat → Block V}
    (h : MovingFrontierChainStateN S rho t1 M0 n0 i End)
    {m : Nat} (hm : n0 ≤ m) (hmi : m ≤ i) :
    MovingFrontierChainStateN S rho t1 M0 n0 m End :=
  movingFrontierChainStateN_prefix h hm hmi

theorem MovingFrontierChainStateN.readRoot_preceq_endpointAtCursor_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {t1 : Time} {M0 : Height} {n0 k : Nat} {End : Nat → Block V}
    (h : MovingFrontierChainStateN S rho t1 M0 n0 k End)
    {s : Slot} {t : Time}
    (hsep : ∀ q : Round, S.a q < t →
      S.a q < Protocol.proposal_time S.E s)
    (hcursor : strictEventIndex rho (Protocol.proposal_time S.E s) ≤ k)
    {v : V} (hv : v ∈ rho.honest)
    (hstart : t1 ≤ t)
    {E : NamedBlock V} (hE : E.erase = End k)
    (hErun : RunBlock S rho E) :
    Block.Preceq
      (Protocol.get_fg_root
        (rho.storeBeforeTime S v t).core.toHealing.toFG) E.erase :=
  movingFrontierChainStateN_readRoot_preceq_endpointAtCursor_named
    S adm hfb h hsep hcursor hv hstart hE hErun

theorem MovingFrontierChainStateN.confRoot_preceq_endpointAtCursor_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {t1 : Time} {M0 : Height} {n0 k : Nat} {End : Nat → Block V}
    (h : MovingFrontierChainStateN S rho t1 M0 n0 k End)
    {c : Slot}
    (hcursor : strictEventIndex rho (Protocol.proposal_time S.E (c + 1)) ≤ k)
    {v : V} (hv : v ∈ rho.honest)
    (hstart : t1 ≤ Protocol.proposal_time S.E (c + 1))
    {E : NamedBlock V} (hE : E.erase = End k)
    (hErun : RunBlock S rho E) :
    Block.Preceq
      (Protocol.get_fg_root
        (rho.storeBeforeTime S v
          (Protocol.confirmation_time S.E c)).core.toHealing.toFG) E.erase :=
  movingFrontierChainStateN_confRoot_preceq_endpointAtCursor_named
    S adm hfb h (k := k) (c := c) hcursor hv hstart hE hErun

theorem MovingFrontierChainStateN.voteRoot_preceq_endpointAtCursor_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {t1 : Time} {M0 : Height} {n0 k : Nat} {End : Nat → Block V}
    (h : MovingFrontierChainStateN S rho t1 M0 n0 k End)
    {s : Slot}
    (hcursor : strictEventIndex rho (Protocol.proposal_time S.E s) ≤ k)
    {v : V} (hv : v ∈ rho.honest)
    (hstart : t1 ≤ Protocol.proposal_time S.E s)
    {E : NamedBlock V} (hE : E.erase = End k)
    (hErun : RunBlock S rho E) :
    Block.Preceq
      (Protocol.get_fg_root
        (rho.storeBeforeTime S v
          (Protocol.vote_time S.E s)).core.toHealing.toFG) E.erase :=
  movingFrontierChainStateN_voteRoot_preceq_endpointAtCursor_named
    S adm hfb h (k := k) (s := s) hcursor hv hstart hE hErun

theorem MovingFrontierChainStateN.confFrontier_sub_one_le_endpointAtCursor_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {t1 : Time} {M0 : Height} {n0 k : Nat} {End : Nat → Block V}
    (h : MovingFrontierChainStateN S rho t1 M0 n0 k End)
    {c : Slot}
    (hcursor : strictEventIndex rho (Protocol.proposal_time S.E (c + 1)) ≤ k)
    {v : V} (hv : v ∈ rho.honest)
    {E : NamedBlock V} (hE : E.erase = End k)
    (hErun : RunBlock S rho E) :
    (rho.storeBeforeTime S v (Protocol.confirmation_time S.E c)).core.h_max - 1 ≤
      (Protocol.derive_named S.E S.cfg E).h :=
  movingFrontierChainStateN_confFrontier_sub_one_le_endpointAtCursor_named
    S adm hfb h (k := k) (c := c) hcursor hv hE hErun

theorem MovingSlotEntryStateN.prevLe
    {S : Setup V} {rho : Run V} {t1 : Time} {M0 : Height}
    {s : Slot} {Prev End : Block V}
    (h : MovingSlotEntryStateN S rho t1 M0 s Prev End) :
    Block.Preceq Prev End := by
  obtain ⟨EndAt, hhistory, hprev, hEnd⟩ := h.prevEndpoint
  rw [← hprev, ← hEnd]
  exact movingFrontierChainStateN_endpoint_mono hhistory
    (strictEventIndex_mono rho h.startTime)
    (strictEventIndex_le_inclusiveEventIndex rho _) (Nat.le_refl _)


/-- The confirmation outcome at the previous endpoint, over the THREE fields
the proof reads. Both the named entry state and the named pre-entry half carry
them, so both get the fact from this one proof (the corresponding branch). -/
theorem movingSlotPreEntryN_confOutcome_atPrev_core
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {t1 : Time} {M0 : Height} {c : Slot} {Prev End : Block V}
    (hstartTime : t1 ≤ Protocol.proposal_time S.E (c + 1))
    (hprevEndpoint : ∃ EndAt : Nat → Block V,
      MovingFrontierChainStateN S rho t1 M0 (strictEventIndex rho t1)
          (inclusiveEventIndex rho
            (Protocol.proposal_time S.E (c + 1))) EndAt ∧
        EndAt (strictEventIndex rho
          (Protocol.proposal_time S.E (c + 1))) = Prev ∧
        EndAt (inclusiveEventIndex rho
          (Protocol.proposal_time S.E (c + 1))) = End)
    (hprevVotes : NamedHonestVotesCone S rho (c + 1 - 1)
      (fun X => Block.Preceq Prev X))
    (hc : 0 < c)
    {r : Round}
    (hround : S.hc.round_of (c + 1) = r + 1)
    (ht1 : t1 ≤ S.a r)
    (hpostAction : S.E.t_GST ≤ S.a r)
    (hcut : S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon)
    (hpostVote : S.E.t_GST ≤ Protocol.vote_time S.E c)
    (hslotHor : Protocol.confirmation_time S.E c ≤ rho.horizon)
    {w : V} (hw : w ∈ rho.honest) :
    GenuineConfirmationWith
        (NamedProfile.gradeContract
          (confirmationInputRead S rho w c).cache)
        S.E S.hc (Proofs.Optimistic.confStore S rho w c) c
        (movingSlotConfirmationOutput S rho c w) ∧
      Block.Preceq Prev (movingSlotConfirmationOutput S rho c w) := by
  obtain ⟨EndAt, hhistory, hprev, _hEnd⟩ := hprevEndpoint
  set k := strictEventIndex rho (Protocol.proposal_time S.E (c + 1)) with hk
  have hpre : MovingFrontierChainStateN S rho t1 M0
      (strictEventIndex rho t1) k EndAt :=
    movingFrontierChainStateN_prefix hhistory
      (strictEventIndex_mono rho hstartTime)
      (strictEventIndex_le_inclusiveEventIndex rho _)
  have hvotes : NamedHonestVotesCone S rho c
      (fun X => Block.Preceq (EndAt k) X) := by
    rw [hprev]
    simpa only [Nat.add_sub_cancel] using hprevVotes
  have hmajority : HonestWeightMajority S rho.honest :=
    AlignedRoundLemmas.honestWeightMajority_of_belowOneThird (S := S) hfb
  obtain ⟨E0, hE0, hE0run⟩ :=
    hpre.endpointRun k hpre.start_le (Nat.le_refl k)
  have hrootRaw : Block.Preceq
      (Protocol.get_fg_root
        (rho.storeBeforeTime S w
          (Protocol.confirmation_time S.E c)).core.toHealing.toFG) E0.erase :=
    movingFrontierChainStateN_confRoot_preceq_endpointAtCursor_named
      S adm hfb hpre (k := k) (c := c) (Nat.le_refl k) hw
      hstartTime hE0 hE0run
  have hroot : Block.Preceq
      (Protocol.get_fg_root
        (confirmationInputRead S rho w c).st.core.toHealing.toFG) E0.erase := by
    simpa only [confirmationInputRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      Run.storeBeforeTime] using hrootRaw
  have hresolve := Protocol.headsResolveIn_confStore_of_postHealingCone
    S adm hw hpostVote
      ((support_cutoff_le_confirmation_time S.E c).trans hslotHor)
      (by simpa only [confRoot,
        Proofs.Optimistic.confStore_eq_confirmationInputRead, hE0] using hroot) hvotes
  have hpositive : 0 < ((S.E.committee c) ∩ rho.honest).card := by
    have hcc := hcom c
    omega
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hpositive
  obtain ⟨X, hEndX, hXrun, hXemit⟩ :=
    hvotes x (Finset.mem_inter.mp hx).2 (Finset.mem_inter.mp hx).1
  have hXmem : X.erase ∈
      (Proofs.Optimistic.confStore S rho w c).T :=
    Proofs.HealingLemmas.find?_mem
      ((hresolve X.erase ⟨x, (Finset.mem_inter.mp hx).2,
        (Finset.mem_inter.mp hx).1, ⟨X, rfl, hXrun⟩, hXemit⟩).1)
  have hpc : ParentClosed (Proofs.Optimistic.confStore S rho w c) := by
    simpa only [confirmationInputRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      NamedRun.stateBeforeTime] using
      Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho
        (Protocol.confirmation_time S.E c) w
  have hmem : E0.erase ∈ (Proofs.Optimistic.confStore S rho w c).T := by
    apply Proofs.Records.mem_of_preceq ((parentClosed_iff _).mp hpc).2
      E0.erase X.erase hXmem
    simpa only [hE0] using hEndX
  have hFJ : Block.Preceq
      (Proofs.Optimistic.confStore S rho w c).F
      (Proofs.Optimistic.confStore S rho w c).J := by
    simpa only [Proofs.Optimistic.confStore_eq_confirmationInputRead,
      confirmationInputRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      NamedRun.stateBeforeTime] using
      Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime S rho
        (Protocol.confirmation_time S.E c) w
  have hrootConf : Block.Preceq
      (Protocol.get_fg_root
        (Proofs.Optimistic.confStore S rho w c).toHealing.toFG) E0.erase := by
    simpa only [Proofs.Optimistic.confStore_eq_confirmationInputRead] using hroot
  have hrootEndAt : Block.Preceq
      (Protocol.get_fg_root
        (confirmationInputRead S rho w c).st.core.toHealing.toFG)
      (EndAt k) := by
    simpa only [hE0] using hroot
  have hFEnd : Block.Preceq
      (Proofs.Optimistic.confStore S rho w c).F E0.erase :=
    Block.preceq_trans
      (Proofs.Records.preceq_get_fg_root_of_F
        (st := (Proofs.Optimistic.confStore S rho w c).toHealing.toFG) hFJ)
      hrootConf
  obtain ⟨K, hKbody, hKErase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho
      (Protocol.confirmation_time S.E c) w
      (by simpa only [Proofs.Optimistic.confStore_eq_confirmationInputRead,
        confirmationInputRead, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        Run.storeBeforeTime] using hmem)
  have hKrun : RunBlock S rho K := by
    obtain ⟨n, hn, _⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
      (Protocol.confirmation_time S.E c)
    apply Proofs.Bridges.runBlock_of_stateBefore_mem S hw (i := n)
    simpa only [Run.storeBeforeTime, hn] using hKbody
  have hKEnd : K.erase = EndAt k := hKErase.trans hE0
  have hband :
      (rho.storeBeforeTime S w
        (Protocol.confirmation_time S.E c)).core.h_max - 1 ≤
        (Protocol.derive_named S.E S.cfg K).h := by
    exact movingFrontierChainStateN_confFrontier_sub_one_le_endpointAtCursor_named
      S adm hfb hpre (k := k) (c := c) (Nat.le_refl k) hw hKEnd hKrun
  have hsigma :
      (Proofs.Optimistic.confStore S rho w c).σ E0.erase =
        Protocol.derive_named S.E S.cfg K := by
    rw [← hKErase]
    simpa only [Proofs.Optimistic.confStore_eq_confirmationInputRead,
      confirmationInputRead, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      NamedRun.stateBeforeTime] using
      Proofs.NamedStoreBridge.derivedView_stateBeforeTime S rho
        (Protocol.confirmation_time S.E c) w K hKbody
  have hbandStore : (Proofs.Optimistic.confStore S rho w c).h_max - 1 ≤
      ((Proofs.Optimistic.confStore S rho w c).σ E0.erase).h := by
    rw [hsigma]
    exact hband
  have hfull : E0.erase ∈
      Protocol.get_filtered_block_tree
        (Proofs.Optimistic.confStore S rho w c).toHealing.toFG :=
    mem_get_filtered_block_tree_from_of_selfViable
      (Proofs.Optimistic.confStore S rho w c).toHealing.toFG
      (Proofs.Optimistic.confStore S rho w c).T hmem hFEnd hrootConf hbandStore
  have hcandidate : K.erase ∈
      confTree (confirmationInputRead S rho w c).st.core := by
    simpa only [hKErase, confTree, Protocol.get_filtered_block_tree,
      Proofs.Optimistic.confStore_eq_confirmationInputRead] using hfull
  have hread : S.hc.Γ_0 S.E.Δ (r + 1) ≤
      Protocol.confirmation_time S.E c := by
    rw [← Protocol.vote_time_succ_add_delta_eq_confirmation_time S.E c]
    exact (Γ_0_le_vote_time_of_round_eq S hround).trans
      (Int.le_add_of_nonneg_right (le_of_lt S.E.Δ_pos))
  have hbefore : S.a r < Protocol.confirmation_time S.E c :=
    (Int.lt_add_of_pos_right (S.a r) S.E.Δ_pos).trans_le
      ((action_add_delta_le_next_Γ_neg1 S r).trans
        ((le_of_lt (Γ_neg1_lt_Γ_0 S.hc S.E.Δ_pos (r + 1))).trans hread))
  have hactionHor : S.a r ≤ rho.horizon :=
    (le_of_lt (Int.lt_add_of_pos_right (S.a r) S.E.Δ_pos)).trans
      ((action_add_delta_le_next_Γ_neg1 S r).trans hcut)
  have hbeforeProposal : S.a r < Protocol.proposal_time S.E (c + 1) :=
    movingChainStep_action_time_lt_proposal_of_lt_confirmation S hbefore
  have hupper : ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u r) (EndAt k) := by
    intro u hu
    obtain ⟨j, hj, hout⟩ :=
      honest_emits_exact_actionAttestationAt S adm hu r hactionHor
    have hjcursor : j < k :=
      emission_index_lt_beforeTime_prefix S
        adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hj
        hbeforeProposal
    have hn0j : strictEventIndex rho t1 ≤ j :=
      filterBefore_length_le_tickIndex S
        adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hj ht1
    have hcarrier := (hpre.sgCarriers j hn0j hjcursor) hu hj hout
    have hmono := movingFrontierChainStateN_endpoint_mono hpre
      (hn0j.trans (Nat.le_succ j))
      (Nat.succ_le_iff.mpr hjcursor) (Nat.le_refl k)
    exact Block.preceq_trans hcarrier hmono
  have hanchor : Block.Preceq
      (confirmationAnchorAt S rho w c) E0.erase := by
    simpa only [confirmationAnchorAt, hE0] using
      confirmationAnchorAt_preceq_of_previousCarriers S adm hfb hround
        hpostAction hcut hslotHor
        (by simpa only [hE0] using hupper) hw hrootEndAt
  have hKPrev : K.erase = Prev := hKEnd.trans hprev
  have hout := genuineConfirmationAndPreceq_of_postHealingCone
    S adm hcom hc hpostVote hslotHor hw (B := K)
    (by simpa only [hKEnd] using hvotes)
    (by simpa only [hKErase] using hroot)
    (by simpa only [hKErase] using hanchor) hcandidate
  simpa only [movingSlotConfirmationOutput, hKPrev] using hout

/-- Every honest slot-`c` confirmation selection is genuine under the
prepared confirmation contract and lands above the previous endpoint of the
slot-`(c+1)` window for an N entry state. From the core above. -/
theorem MovingSlotEntryStateN.confOutcome_atPrev_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {t1 : Time} {M0 : Height} {c : Slot} {Prev End : Block V}
    (hentry : MovingSlotEntryStateN S rho t1 M0 (c + 1) Prev End)
    (hc : 0 < c)
    {r : Round}
    (hround : S.hc.round_of (c + 1) = r + 1)
    (ht1 : t1 ≤ S.a r)
    (hpostAction : S.E.t_GST ≤ S.a r)
    (hcut : S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon)
    (hpostVote : S.E.t_GST ≤ Protocol.vote_time S.E c)
    (hslotHor : Protocol.confirmation_time S.E c ≤ rho.horizon)
    {w : V} (hw : w ∈ rho.honest) :
    GenuineConfirmationWith
        (NamedProfile.gradeContract
          (confirmationInputRead S rho w c).cache)
        S.E S.hc (Proofs.Optimistic.confStore S rho w c) c
        (movingSlotConfirmationOutput S rho c w) ∧
      Block.Preceq Prev (movingSlotConfirmationOutput S rho c w) :=
  movingSlotPreEntryN_confOutcome_atPrev_core S adm hcom hfb
    hentry.startTime hentry.prevEndpoint hentry.prevVotes hc hround ht1
    hpostAction hcut hpostVote hslotHor hw

#print axioms movingSlotPreEntryN_confOutcome_atPrev_core

/-- Assemble the named facts of a slot window from an N entry state. -/
theorem MovingSlotEntryStateN.windowFacts
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {t1 : Time} {M0 : Height} {c : Slot} {Prev End : Block V}
    (hentry : MovingSlotEntryStateN S rho t1 M0 (c + 1) Prev End)
    (hc : 0 < c)
    {r : Round}
    (hround : S.hc.round_of (c + 1) = r + 1)
    (ht1 : t1 ≤ S.a r)
    (hpostAction : S.E.t_GST ≤ S.a r)
    (hcut : S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon)
    (hpostVote : S.E.t_GST ≤ Protocol.vote_time S.E c)
    (hpostProp : S.E.t_GST ≤ Protocol.proposal_time S.E c)
    (hslotHor : Protocol.confirmation_time S.E c ≤ rho.horizon)
    (htiming : MovingSlotActionTiming S rho t1 c) :
    ∃ Next : Block V,
      MovingSlotFrontierAt S rho c End Next ∧
        NamedMovingSlotWindowFacts S rho (c + 1) End Next := by
  obtain ⟨Next, hfrontier⟩ :=
    movingSlot_existsFrontier S adm hpostProp hslotHor (by
      intro w hw D hD
      simpa only [Nat.add_sub_cancel] using hentry.confCompatible w hw D hD)
  obtain ⟨EndAt, hhistory, hprev, hEnd⟩ := hentry.prevEndpoint
  set k := strictEventIndex rho (Protocol.proposal_time S.E (c + 1)) with hk
  have hcursorHistory : k ≤
      inclusiveEventIndex rho (Protocol.proposal_time S.E (c + 1)) :=
    strictEventIndex_le_inclusiveEventIndex rho _
  have hpre : MovingFrontierChainStateN S rho t1 M0
      (strictEventIndex rho t1) k EndAt :=
    movingFrontierChainStateN_prefix hhistory
      (strictEventIndex_mono rho hentry.startTime) hcursorHistory
  obtain ⟨E0, hE0, hE0run⟩ :=
    hpre.endpointRun k
      (strictEventIndex_mono rho hentry.startTime)
      (Nat.le_refl k)
  have hprevLe : Block.Preceq Prev End := by
    rw [← hprev, ← hEnd]
    exact movingFrontierChainStateN_endpoint_mono hhistory
      (strictEventIndex_mono rho hentry.startTime)
      (strictEventIndex_le_inclusiveEventIndex rho _)
      (Nat.le_refl _)
  have hreadVote : S.hc.Γ_0 S.E.Δ (r + 1) ≤
      Protocol.vote_time S.E (c + 1) :=
    Γ_0_le_vote_time_of_round_eq S hround
  have hbeforeVote : S.a r < Protocol.vote_time S.E (c + 1) :=
    (Int.lt_add_of_pos_right (S.a r) S.E.Δ_pos).trans_le
      ((action_add_delta_le_next_Γ_neg1 S r).trans
        ((le_of_lt (Γ_neg1_lt_Γ_0 S.hc S.E.Δ_pos (r + 1))).trans
          hreadVote))
  have hactionHor : S.a r ≤ rho.horizon :=
    (le_of_lt (Int.lt_add_of_pos_right (S.a r) S.E.Δ_pos)).trans
      ((action_add_delta_le_next_Γ_neg1 S r).trans hcut)
  have hbeforeProposal : S.a r <
      Protocol.proposal_time S.E (c + 1) :=
    Protocol.action_time_lt_proposal_of_lt_vote S hbeforeVote
  have hupper : ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u r) (EndAt k) := by
    intro u hu
    obtain ⟨j, hj, hout⟩ :=
      honest_emits_exact_actionAttestationAt S adm hu r hactionHor
    have hjcursor : j < k :=
      emission_index_lt_beforeTime_prefix S
        adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hj
        hbeforeProposal
    have hn0j : strictEventIndex rho t1 ≤ j :=
      filterBefore_length_le_tickIndex S
        adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hj ht1
    have hcarrier := (hpre.sgCarriers j hn0j hjcursor) hu hj hout
    have hmono := movingFrontierChainStateN_endpoint_mono hpre
      (hn0j.trans (Nat.le_succ j))
      (Nat.succ_le_iff.mpr hjcursor) (Nat.le_refl k)
    exact Block.preceq_trans hcarrier hmono
  have hanchorVote : ∀ w ∈ rho.honest,
      Block.Preceq (voterAnchorAt S rho w (c + 1)) E0.erase := by
    intro w hw
    have hrootVoteRaw : Block.Preceq
        (Protocol.get_fg_root
          (rho.storeBeforeTime S w
            (Protocol.vote_time S.E (c + 1))).core.toHealing.toFG)
        E0.erase := by
      exact movingFrontierChainStateN_voteRoot_preceq_endpointAtCursor_named
        S adm hfb hpre (k := k) (s := c + 1)
        (Nat.le_refl k) hw (by
          exact hentry.startTime)
        hE0 hE0run
    have hrootVote : Block.Preceq
        (Protocol.get_fg_root
          (Proofs.Optimistic.voteDutyStore S rho w (c + 1)).toHealing.toFG)
        E0.erase := by
      simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore, Run.storeBeforeTime] using hrootVoteRaw
    exact voterAnchorAt_preceq_of_previousCarriers S adm hfb hround
      hpostAction hcut
      (by
        have htime : Protocol.vote_time S.E (c + 1) ≤
            Protocol.confirmation_time S.E c := by
          rw [← Protocol.vote_time_succ_add_delta_eq_confirmation_time S.E c]
          exact le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)
        exact htime.trans hslotHor)
      (by
        intro u hu
        simpa only [hE0] using hupper u hu) hw hrootVote
  have hvoteAnchor : ∀ w ∈ rho.honest,
      Block.compatible (voterAnchorAt S rho w (c + 1)) End = true := by
    intro w hw
    have hanchorEnd : Block.Preceq
        (voterAnchorAt S rho w (c + 1)) End :=
      Block.preceq_trans (hanchorVote w hw)
        (by simpa only [hE0, hprev] using hprevLe)
    exact Block.compatible_of_preceq_common hanchorEnd
      (Block.preceq_self End)
  have hconfOut : ∀ w ∈ rho.honest,
      GenuineConfirmationWith
          (NamedProfile.gradeContract
            (confirmationInputRead S rho w c).cache)
          S.E S.hc (Proofs.Optimistic.confStore S rho w c) c
          (movingSlotConfirmationOutput S rho c w) ∧
        Block.Preceq (movingSlotConfirmationOutput S rho c w) Next := by
    intro w hw
    have hrootConfRaw : Block.Preceq
        (Protocol.get_fg_root
          (rho.storeBeforeTime S w
            (Protocol.confirmation_time S.E c)).core.toHealing.toFG)
        E0.erase := by
      exact movingFrontierChainStateN_confRoot_preceq_endpointAtCursor_named
        S adm hfb hpre (k := k) (c := c) (Nat.le_refl k) hw
          hentry.startTime
        hE0 hE0run
    have hvotes : NamedHonestVotesCone S rho c
        (fun X => Block.Preceq (EndAt k) X) := by
      rw [hprev]
      simpa only [Nat.add_sub_cancel] using hentry.prevVotes
    have hrootConf : Block.Preceq
        (Protocol.get_fg_root
          (confirmationInputRead S rho w c).st.core.toHealing.toFG)
        E0.erase := by
      simpa only [confirmationInputRead, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        Run.storeBeforeTime] using hrootConfRaw
    have hresolve := Protocol.headsResolveIn_confStore_of_postHealingCone
      S adm hw hpostVote
        ((support_cutoff_le_confirmation_time S.E c).trans hslotHor)
        (by simpa only [confRoot,
          Proofs.Optimistic.confStore_eq_confirmationInputRead, hE0] using hrootConf)
        hvotes
    have hpositive : 0 < ((S.E.committee c) ∩ rho.honest).card := by
      have hcc := hcom c
      omega
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hpositive
    obtain ⟨X, hEndX, hXrun, hXemit⟩ :=
      hvotes x (Finset.mem_inter.mp hx).2 (Finset.mem_inter.mp hx).1
    have hXmem : X.erase ∈
        (Proofs.Optimistic.confStore S rho w c).T :=
      Proofs.HealingLemmas.find?_mem
        ((hresolve X.erase ⟨x, (Finset.mem_inter.mp hx).2,
          (Finset.mem_inter.mp hx).1, ⟨X, rfl, hXrun⟩, hXemit⟩).1)
    have hpc : ParentClosed (Proofs.Optimistic.confStore S rho w c) := by
      simpa only [confirmationInputRead,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        NamedRun.stateBeforeTime] using
        Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho
          (Protocol.confirmation_time S.E c) w
    have hmem : E0.erase ∈ (Proofs.Optimistic.confStore S rho w c).T := by
      apply Proofs.Records.mem_of_preceq ((parentClosed_iff _).mp hpc).2
        E0.erase X.erase hXmem
      simpa only [hE0] using hEndX
    have hFJ : Block.Preceq
        (Proofs.Optimistic.confStore S rho w c).F
        (Proofs.Optimistic.confStore S rho w c).J := by
      simpa only [Proofs.Optimistic.confStore_eq_confirmationInputRead,
        confirmationInputRead, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        NamedRun.stateBeforeTime] using
        Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime S rho
          (Protocol.confirmation_time S.E c) w
    have hrootConfStore : Block.Preceq
        (Protocol.get_fg_root
          (Proofs.Optimistic.confStore S rho w c).toHealing.toFG) E0.erase := by
      simpa only [Proofs.Optimistic.confStore_eq_confirmationInputRead] using hrootConf
    have hFEnd : Block.Preceq
        (Proofs.Optimistic.confStore S rho w c).F E0.erase :=
      Block.preceq_trans
        (Proofs.Records.preceq_get_fg_root_of_F
          (st := (Proofs.Optimistic.confStore S rho w c).toHealing.toFG) hFJ)
        hrootConfStore
    obtain ⟨K, hKbody, hKErase⟩ :=
      Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho
        (Protocol.confirmation_time S.E c) w
        (by simpa only [Proofs.Optimistic.confStore_eq_confirmationInputRead,
          confirmationInputRead, NamedActionReads.confirmationReadAt,
          NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
          Run.storeBeforeTime] using hmem)
    have hKrun : RunBlock S rho K := by
      obtain ⟨n, hn, _⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S
        adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
        (Protocol.confirmation_time S.E c)
      apply Proofs.Bridges.runBlock_of_stateBefore_mem S hw (i := n)
      simpa only [Run.storeBeforeTime, hn] using hKbody
    have hKEnd : K.erase = EndAt k := hKErase.trans hE0
    have hband :
        (rho.storeBeforeTime S w
          (Protocol.confirmation_time S.E c)).core.h_max - 1 ≤
        (Protocol.derive_named S.E S.cfg K).h := by
      exact movingFrontierChainStateN_confFrontier_sub_one_le_endpointAtCursor_named
        S adm hfb hpre (k := k) (c := c) (Nat.le_refl k) hw hKEnd hKrun
    have hsigma :
        (Proofs.Optimistic.confStore S rho w c).σ E0.erase =
          Protocol.derive_named S.E S.cfg K := by
      rw [← hKErase]
      simpa only [Proofs.Optimistic.confStore_eq_confirmationInputRead,
        confirmationInputRead, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
        NamedRun.stateBeforeTime] using
        Proofs.NamedStoreBridge.derivedView_stateBeforeTime S rho
          (Protocol.confirmation_time S.E c) w K hKbody
    have hbandStore : (Proofs.Optimistic.confStore S rho w c).h_max - 1 ≤
        ((Proofs.Optimistic.confStore S rho w c).σ E0.erase).h := by
      rw [hsigma]
      exact hband
    have hfull : E0.erase ∈
        Protocol.get_filtered_block_tree
          (Proofs.Optimistic.confStore S rho w c).toHealing.toFG :=
      mem_get_filtered_block_tree_from_of_selfViable
        (Proofs.Optimistic.confStore S rho w c).toHealing.toFG
        (Proofs.Optimistic.confStore S rho w c).T hmem hFEnd hrootConfStore hbandStore
    have hcandidate : K.erase ∈
        confTree (confirmationInputRead S rho w c).st.core := by
      simpa only [hKErase, confTree, Protocol.get_filtered_block_tree,
        Proofs.Optimistic.confStore_eq_confirmationInputRead] using hfull
    have hanchorConf : Block.Preceq
        (confirmationAnchorAt S rho w c) E0.erase := by
      exact confirmationAnchorAt_preceq_of_previousCarriers S adm hfb hround
        hpostAction hcut hslotHor
        (by
          intro u hu
          simpa only [hE0] using hupper u hu) hw hrootConf
    have hKPrev : K.erase = Prev := hKEnd.trans hprev
    have hout := genuineConfirmationAndPreceq_of_postHealingCone
      S adm hcom hc hpostVote hslotHor hw (B := K)
      (by simpa only [hKEnd] using hvotes)
      (by simpa only [hKErase] using hrootConf)
      (by simpa only [hKErase] using hanchorConf) hcandidate
    exact ⟨by simpa only [movingSlotConfirmationOutput, hKPrev] using hout.1,
      hfrontier.genuinePreceq w hw _ hout.1⟩
  refine ⟨Next, hfrontier, ?_⟩
  exact movingSlotWindowFacts_of_readInputs S adm hfb
    hfrontier.oldPreceq
    (by simpa only [Nat.add_sub_cancel] using hslotHor)
    hentry.headEq hvoteAnchor hconfOut (by
      intro q hq
      rw [Nat.add_sub_cancel] at hq
      obtain ⟨hq0, hpost, hcutq, ht1q, hhorq, hbeforeq⟩ := htiming q hq
      exact ⟨hq0, hpost, hcutq, by
        intro u hu
        obtain ⟨j, hj, houtq⟩ :=
          honest_emits_exact_actionAttestationAt S adm hu (q - 1) hhorq
        have hjstrict : j <
            strictEventIndex rho (Protocol.proposal_time S.E (c + 1)) :=
          emission_index_lt_beforeTime_prefix S
            adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hj hbeforeq
        have hjcursor : j <
            inclusiveEventIndex rho (Protocol.proposal_time S.E (c + 1)) :=
          Nat.lt_of_lt_of_le hjstrict
            (strictEventIndex_le_inclusiveEventIndex rho _)
        have hn0j : strictEventIndex rho t1 ≤ j :=
          filterBefore_length_le_tickIndex S
            adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hj ht1q
        have hcarrier := (hhistory.sgCarriers j hn0j hjcursor) hu hj houtq
        have hmono := movingFrontierChainStateN_endpoint_mono hhistory
          (hn0j.trans (Nat.le_succ j))
          (Nat.succ_le_iff.mpr hjcursor) (Nat.le_refl _)
        have hfinal : Block.Preceq
            (EndAt (inclusiveEventIndex
              rho (Protocol.proposal_time S.E (c + 1)))) Next := by
          rw [hEnd]
          exact hfrontier.oldPreceq
        exact Block.preceq_trans hcarrier
          (Block.preceq_trans hmono hfinal)⟩)

#print axioms MovingSlotEntryStateN.windowFacts


/-
/-- One call from the slot-entry state to the facts of its own window.

The four inputs of `movingSlotWindowFacts_of_readInputs` are supplied from the
entry state: the head equality is its own field, the vote anchor and the
previous-round carrier ceiling come from the moving history at the strict
proposal cursor, and the confirmations are certified there and then absorbed
into the selected window endpoint. -/
theorem MovingSlotEntryState.windowFacts
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hfb: BelowOneThird S rho.honest)
    {t1: Time} {M0: Height} {c: Slot} {Prev End: Block V}
    (hentry: MovingSlotEntryState S rho t1 M0 (c + 1) Prev End)
    (hc: 0 < c)
    {r: Round}
    (hround: S.hc.round_of (c + 1) = r + 1)
    (ht1: t1 ≤ S.a r)
    (hpostAction: S.E.t_GST ≤ S.a r)
    (hcut: S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon)
    (hpostVote: S.E.t_GST ≤ Protocol.vote_time S.E c)
    (hpostProp: S.E.t_GST ≤ Protocol.proposal_time S.E c)
    (hslotHor: Protocol.confirmation_time S.E c ≤ rho.horizon)
    (htiming: MovingSlotActionTiming S rho t1 c):
    ∃ Next: Block V,
      MovingSlotFrontierAt S rho c End Next ∧
        MovingSlotWindowFacts S rho (c + 1) End Next:= by
  obtain ⟨Next, hfrontier⟩:=
    hentry.existsWindowFrontier S adm hpostProp hslotHor
  refine ⟨Next, hfrontier, ?_⟩
  refine movingSlotWindowFacts_of_readInputs S adm hfb
    hfrontier.oldPreceq
    (by simpa only [Nat.add_sub_cancel] using hslotHor)
    hentry.headEq ?_ ?_ ?_
  · intro w hw
    exact hentry.windowVoteAnchor S adm hcom hfb hround ht1 hpostAction hcut
      hpostVote hslotHor (Block.preceq_self End) w hw
  · exact hentry.windowConfOut S adm hcom hfb hc hround ht1 hpostAction hcut
      hpostVote hslotHor hfrontier
  · intro q hq
    rw [Nat.add_sub_cancel] at hq
    obtain ⟨hq0, hpost, hcutq, ht1q, hhorq, hbeforeq⟩:= htiming q hq
    exact ⟨hq0, hpost, hcutq,
      hentry.carrierCeiling S adm ht1q hhorq hbeforeq hfrontier.oldPreceq⟩
-/

/-! ## The Route A healing leaf

The assembly's healing clause. It is deliberately NOT a `CanonicalSuffixSeed`:
that record's `boundaryStoreSafety` carries
`CanonicalSuffixBoundaryStoreSafety.hmax`, i.e. `honestHMaxAt (a q) ≤ height base`
with `base ⪯ End`, which is ZERO numeric debt at the boundary action. The
moving chain proves the one-unit band and no more, and the one-unit gap is the
truth of the protocol rather than slack in the proof: a mixed target/timeout
quorum advances `h_max` without advancing `h_j` or the chain, and a selectively
delivered off-chain sibling burn keeps `h_max` one above the honest chain. An
honest `+1` carrier proposal before `a_q` can carry the mix itself, so
restricting to honest carriers does not remove it.

The leaf therefore carries the two facts the final theorem actually consumes:
the two-slot handoff at `q`, for the liveness clause, and the canonical suffix
execution at the same `q`, for everything downstream. -/





/-! ## The per-slot endpoint family for the all-rounds floor record

fk15's `MovingChainRoundFloorFor` is indexed by a per-slot family
`End: Slot → Block V` and asks, for an honest slot-`d` proposer, that
`End d ⪯ proposedParent S rho d`. That identifies which of this fold's two
per-slot blocks it means: it is the endpoint at the STRICT cursor of the
slot-`d` proposal instant, this module's `Prev`, and NOT the entry endpoint
`End`, which in an honest-proposer slot IS the slot proposal and so is never
below its own parent.

With that reading the three proposal-side fields are projections:

* `endpointMonotone` is the endpoint chain read at the strict cursors, below;
* `endpointBelowHonestParent d` is exactly the `hparent` input of
  `MovingSlotEntryState.step_honestProposer` at slot `d - 1`, which is what
  makes the transfer go through there;
* `honestProposalAbsorbed d` is `MovingSlotFrontierAt.oldPreceq` at slot `d`:
  the window endpoint dominates the entry endpoint, and in an honest-proposer
  slot the entry endpoint is the proposal itself. -/





/-! ## A genuine confirmation has an honest supporter at its own slot

The same-slot UPPER bound is false: `update_confirmation`'s gate is
`count < 2 * score B` over the reader's OWN view, so a tipped strict majority
lets one honest reader confirm a block that another honest same-slot voter's
head does not extend. What is true, and what visibility needs, is the weaker
existence of one supporter.

The proof is a counting argument that is already in the tree. `GenuineConfirmation`
carries the gate as its `genuine` field, and `Proofs.Optimistic.ConeSupport.not_eligible`
refutes exactly that gate for a block no honest cone vote lies under. So if no
honest slot-`c` voter were above `D`, the cone support built at the confirmation
views would deny the gate that genuineness asserts. -/

omit [Fintype V] in
private theorem off_notInCone_local (B : Block V) :
    Proofs.Optimistic.Off (fun X => ¬ Block.Preceq B X) B := by
  intro X hX
  rw [← Bool.not_eq_true]
  exact hX



/-- The contract-carrying twin of `genuineConfirmation_not_allHonestVotesOff`
(the corresponding branch). Everything after the gate is contract-free; only the step
from the hypothesis to `confEligible … D` reads the contract, and
`update_confirmation_with_live_confirmed` supplies it. The default-contract
form above is unchanged. -/
theorem genuineConfirmation_not_allHonestVotesOff_with
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (contract : Protocol.GradeContract V)
    {c : Slot} (hc : 0 < c)
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E c)
    (hhor : Protocol.confirmation_time S.E c ≤ rho.horizon)
    {v : V} (hv : v ∈ rho.honest)
    (hres : Proofs.Optimistic.HeadsResolveIn S rho c
      (Proofs.Optimistic.confStore S rho v c).T
      (Proofs.Optimistic.confStore S rho v c).timestamp_block)
    {D : Block V}
    (hgenuine : GenuineConfirmationWith contract S.E S.hc
      (Proofs.Optimistic.confStore S rho v c) c D) :
    ¬ NamedHonestVotesCone S rho c
        (fun X => ¬ Block.Preceq D X) := by
  intro hnames
  have hsupport := coneSupport_confVotes_after_gst
    S adm hcom hc hpost hhor hnames hv hres
  have hvalid : Protocol.VoteSetValid S.E c
      (confLate S.E (Proofs.Optimistic.confStore S rho v c) c) := by
    simpa only [Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore] using
      voteSetValid_confLate_stateBeforeTime S
        adm.toNamedAdmissibleCore.toNamedScheduleWellFormed v
        (Protocol.confirmation_time S.E c) c
  have hnot := hsupport.not_eligible hvalid (off_notInCone_local D)
  have hgate : confEligible S.E (Proofs.Optimistic.confStore S rho v c) c D = true := by
    have hlive := update_confirmation_with_live_confirmed contract S.E S.hc
      (Proofs.Optimistic.confStore S rho v c) c
    rw [hgenuine.genuine, if_pos rfl] at hlive
    rw [← hgenuine.selected, hlive]
    exact hgenuine.genuine
  simp only [confEligible, confCount, confScore, decide_eq_true_eq] at hgate
  exact hnot hgate

#print axioms genuineConfirmation_not_allHonestVotesOff_with

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
