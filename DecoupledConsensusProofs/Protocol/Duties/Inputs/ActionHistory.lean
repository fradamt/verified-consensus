module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ActionSourceCore
public import DecoupledConsensusProofs.Protocol.ValidatorClient.FinalityPairCore
public import DecoupledConsensusProofs.Objects.AttestationCanonicality
public import DecoupledConsensusProofs.Execution.EmissionShape
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.IntrinsicEntry
public import DecoupledConsensusProofs.Protocol.ChainState.ProposalBridge

@[expose] public section



namespace DecoupledConsensusModel
namespace Protocol

open Internal
open Execution
open Internal.NamedOutageEntry
open Protocol (derive_named)

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## One attestation-producing event -/

/-- The directional facts made by one honest attestation output at event `i`.

The height clause retains a concrete source block. This is stronger than the
numeric candidate-survival bound and lets a later endpoint extension use only
chain transitivity. -/
structure HonestAttestationOutputPreceqAtIndex
    (S : Setup V) (rho : Run V) (i : Nat) (B : Block V) : Prop where
  targets : ∀ {v : V} {time : Time} {a : NamedAttestation V},
    v ∈ rho.honest →
      rho.events[i]? = some (Event.tick v time) →
      Object.attest a ∈ NamedRun.emittedAt S rho i v time →
      ∀ h target, a.height_pair = NamedHeightPair.vote h target false →
        ∀ X : NamedBlock V, RunBlock S rho X → X.erase.root = target →
          Block.Preceq X.erase B
  confirmed : ∀ {v : V} {time : Time} {a : NamedAttestation V},
    v ∈ rho.honest →
      rho.events[i]? = some (Event.tick v time) →
      Object.attest a ∈ NamedRun.emittedAt S rho i v time →
      ∀ root, a.confirmed = some root →
        ∀ X : NamedBlock V, RunBlock S rho X → X.erase.root = root →
          Block.Preceq X.erase B
  height_gate_sources :
    ∀ {v : V} {time : Time} {a : NamedAttestation V},
      v ∈ rho.honest →
        rho.events[i]? = some (Event.tick v time) →
        Object.attest a ∈ NamedRun.emittedAt S rho i v time →
        ∀ h, a.height_pair.erase.height? = some h →
          ∃ G : NamedBlock V, RunBlock S rho G ∧
            (derive_named S.E S.cfg G).h = h ∧ Block.Preceq G.erase B

/-- Extending the fixed endpoint preserves every fact made by one
attestation-producing event. -/
theorem HonestAttestationOutputPreceqAtIndex.mono
    {S : Setup V} {rho : Run V} {i : Nat} {B C : Block V}
    (h : HonestAttestationOutputPreceqAtIndex S rho i B)
    (hBC : Block.Preceq B C) :
    HonestAttestationOutputPreceqAtIndex S rho i C := by
  refine ⟨?_, ?_, ?_⟩
  · intro v time a hv hi ha height target hpair X hrun hroot
    exact Block.preceq_trans
      (h.targets hv hi ha height target hpair X hrun hroot) hBC
  · intro v time a hv hi ha root hconfirmed X hrun hroot
    exact Block.preceq_trans
      (h.confirmed hv hi ha root hconfirmed X hrun hroot) hBC
  · intro v time a hv hi ha height hheight
    obtain ⟨G, hrun, hGh, hGB⟩ :=
      h.height_gate_sources hv hi ha height hheight
    exact ⟨G, hrun, hGh, Block.preceq_trans hGB hBC⟩

/-- One event has an honest attestation output. This is proof data only; it
does not assume that every tick is an action tick. -/
def HonestAttestationEmissionAtIndex
    (S : Setup V) (rho : Run V) (i : Nat) : Prop :=
  ∃ (v : V) (time : Time) (a : NamedAttestation V),
    v ∈ rho.honest ∧
      rho.events[i]? = some (Event.tick v time) ∧
      Object.attest a ∈ NamedRun.emittedAt S rho i v time

/-- An emitted row at an indexed tick is an emission of that node. -/
theorem emits_of_emittedAt_tick
    (S : Setup V) {rho : Run V} {i : Nat} {v : V} {time : Time}
    {a : NamedAttestation V}
    (hi : rho.events[i]? = some (Event.tick v time))
    (ha : Object.attest a ∈ NamedRun.emittedAt S rho i v time) :
    NamedRun.emits S rho v (Object.attest a) time :=
  ⟨i, hi, ha⟩


/-- Without an honest attestation output, the directional event obligation is
vacuous for every endpoint. -/
theorem honestAttestationOutputPreceqAtIndex_of_no_emission
    (S : Setup V) (rho : Run V) {i : Nat} {B : Block V}
    (hno : ¬ HonestAttestationEmissionAtIndex S rho i) :
    HonestAttestationOutputPreceqAtIndex S rho i B := by
  refine ⟨?_, ?_, ?_⟩
  · intro v time a hv hevent ha
    exact (hno ⟨v, time, a, hv, hevent, ha⟩).elim
  · intro v time a hv hevent ha
    exact (hno ⟨v, time, a, hv, hevent, ha⟩).elim
  · intro v time a hv hevent ha
    exact (hno ⟨v, time, a, hv, hevent, ha⟩).elim

/-! ## Canonical history through an event prefix -/





/-- An emission strictly before `t` has its event witness inside the event
prefix that `stateBeforeTime t` reads. -/
theorem emission_index_lt_beforeTime_prefix
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    {v : V} {time t : Time} {i : Nat}
    (hi : rho.events[i]? = some (Event.tick v time))
    (ht : time < t) :
    i < (rho.events.filter (fun e => decide (e.time < t))).length := by
  by_contra hnot
  have hge : (rho.events.filter (fun e => decide (e.time < t))).length ≤ i :=
    Nat.le_of_not_gt hnot
  have htime := Proofs.Optimistic.le_time_of_index_ge S sch hge hi
  exact (not_le_of_gt ht) htime



/-! ## Exact active-source interface -/

/-- The read one honest round action actually builds its row on: the round's
`actionReadFrom` on the emitter's own state before its tick. This is the read
`Proofs.Optimistic.emits_attest_duty` names. -/
abbrev actionEventRead (S : Setup V) (rho : Run V) (i : Nat) (v : V)
    (r : Round) : NamedNodeState V :=
  actionReadFrom S (rho.stateBefore S i v) r


/-- The actual sources a round action can select, read at that action's own
prepared read and under that read's own contract.

**Named (design note).** The G2 clause is the contract read's own grade-2
selection rather than a raw `Protocol.G2` gate, and the anchor clause is
`get_sg_root_with` at the same contract; both are the values
`Protocol.NamedActions.round_action_with` actually consults. -/
structure HonestRoundActionActiveSourcesPreceqAtIndex
    (S : Setup V) (rho : Run V) (i : Nat) (B : Block V) : Prop where
  live : ∀ {v : V} {time : Time} {a : NamedAttestation V},
    v ∈ rho.honest →
    rho.events[i]? = some (Event.tick v time) →
      Object.attest a ∈ NamedRun.emittedAt S rho i v time →
      Block.Preceq
        (actionEventRead S rho i v a.round).st.core.live_confirmed B
  grade2 : ∀ {v : V} {time : Time} {a : NamedAttestation V},
    v ∈ rho.honest →
    rho.events[i]? = some (Event.tick v time) →
      Object.attest a ∈ NamedRun.emittedAt S rho i v time →
      ∀ Q : Block V,
        Protocol.grade2_block_with
            (NamedProfile.gradeContract (actionEventRead S rho i v a.round).cache)
            S.E S.hc (actionEventRead S rho i v a.round).st.core.toHealing
            (S.hc.round_of (actionEventRead S rho i v a.round).st.core.s) =
          some Q →
        Block.Preceq Q B
  sg_root : ∀ {v : V} {time : Time} {a : NamedAttestation V},
    v ∈ rho.honest →
    rho.events[i]? = some (Event.tick v time) →
      Object.attest a ∈ NamedRun.emittedAt S rho i v time →
      Block.Preceq
        (Protocol.get_sg_root_with
          (NamedProfile.gradeContract (actionEventRead S rho i v a.round).cache)
          S.E S.hc (actionEventRead S rho i v a.round).st.core.toHealing
          (S.hc.round_of (actionEventRead S rho i v a.round).st.core.s)) B

omit [DecidableEq V] [Fintype V] in
private theorem index_of_same_event {alpha : Type} (events : List alpha)
    (hnodup : events.Nodup) {i j : Nat} {e : alpha}
    (hi : events[i]? = some e) (hj : events[j]? = some e) : i = j :=
  (List.getElem?_inj (List.getElem?_eq_some_iff.mp hi).1 hnodup).mp
    (hi.trans hj.symm)

private theorem signedSource_scope
    (S : Setup V) {rho : Run V} {i : Nat} {a : NamedAttestation V}
    {source entry : NamedBlock V} (ha : a.val_index ∈ rho.honest)
    (hs : Internal.NamedJointOutage.SignedSourceAt S rho i a source entry) :
    RunBlock S rho source ∧ RunBlock S rho entry := by
  rcases hs with ⟨_, _, _, hsource, _, hentry, _⟩
  have hpre : source ∈ (NamedRun.stateBefore S rho i a.val_index).st.bodies := hsource
  have hscope := Proofs.NamedRuntime.blockInRun_of_direct S rho
    (Proofs.NamedRuntime.directBlock_of_prefix S rho ha i hpre)
  exact ⟨hscope, Proofs.NamedRuntime.blockInRun_of_ancestor S rho hscope hentry⟩

private theorem named_eq_of_runBlock_root
    (S : Setup V) {rho : Run V} (hadm : Admissible S rho)
    {X Y : NamedBlock V} (hX : RunBlock S rho X) (hY : RunBlock S rho Y)
    (hroot : X.erase.root = Y.erase.root) : X = Y := by
  have hnamedRoot : X.root = Y.root := by
    rw [← Proofs.NamedWire.erase_root X, ← Proofs.NamedWire.erase_root Y]
    exact hroot
  exact hadm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective
    X Y hX hY X Y (Or.inl (Proofs.NamedAncestry.named_self X))
      (Or.inr (Proofs.NamedAncestry.named_self Y)) hnamedRoot

private theorem emittedRound_at_index
    (S : Setup V) {rho : Run V} (hadm : Admissible S rho)
    {i : Nat} {v : V} {time : Time} {a : NamedAttestation V}
    (hi : rho.events[i]? = some (Event.tick v time))
    (ha : Object.attest a ∈ NamedRun.emittedAt S rho i v time) :
    a.round = S.hc.round_of (actionEventRead S rho i v a.round).st.core.s := by
  have hemit := emits_of_emittedAt_tick S hi ha
  obtain ⟨j, hj, _, _, hval, hround, ht, _⟩ :=
    Proofs.NamedOutageInputs.emitted_attestation_stages S rho hemit
  have hji : j = i := index_of_same_event rho.events
    hadm.toNamedAdmissibleCore.nodup (by simpa only [hval, ht] using hj) hi
  subst j
  exact hround

private theorem activeFGSource_preceq
    (S : Setup V) {rho : Run V} {i : Nat} {v : V} {time : Time}
    {a : NamedAttestation V} {B C : Block V}
    (hsources : HonestRoundActionActiveSourcesPreceqAtIndex S rho i B)
    (hv : v ∈ rho.honest)
    (hi : rho.events[i]? = some (Event.tick v time))
    (ha : Object.attest a ∈ NamedRun.emittedAt S rho i v time)
    (hround : a.round = S.hc.round_of (actionEventRead S rho i v a.round).st.core.s)
    (hsource : Proofs.HealingSurface.actionFGSource S
      (actionEventRead S rho i v a.round) = some C) :
    Block.Preceq C B := by
  let n := actionEventRead S rho i v a.round
  let gc := NamedProfile.gradeContract n.cache
  have hsource' : Protocol.fg_source_with gc S.E S.hc n.st.core.toHealing a.round
      (Protocol.grade2_block_with gc S.E S.hc n.st.core.toHealing a.round) = some C := by
    change Protocol.fg_source_with gc S.E S.hc n.st.core.toHealing
      (S.hc.round_of n.st.core.s)
      (Protocol.grade2_block_with gc S.E S.hc n.st.core.toHealing
        (S.hc.round_of n.st.core.s)) = some C at hsource
    rwa [← hround] at hsource
  rw [Protocol.fg_source_with.eq_def] at hsource'
  cases hQ : Protocol.grade2_block_with gc S.E S.hc n.st.core.toHealing a.round with
  | none =>
      simp only [hQ] at hsource'
      cases hsource'
  | some Q =>
      simp only [hQ] at hsource'
      cases hclear : Protocol.deepest_clear (some Q) n.st.core.toHealing.live_confirmed
          ((gc.read S.E S.hc n.st.core.toHealing a.round).clear) with
      | some D =>
          rw [hclear] at hsource'
          have hDC : D = C := Option.some.inj hsource'
          subst C
          exact Block.preceq_trans (Proofs.Engine.deepest_clear_preceq hclear)
            (hsources.live hv hi ha)
      | none =>
          rw [hclear] at hsource'
          have hQC : Q = C := Option.some.inj hsource'
          subst C
          apply hsources.grade2 hv hi ha Q
          change Protocol.grade2_block_with gc S.E S.hc n.st.core.toHealing
            (S.hc.round_of n.st.core.s) = some Q
          rw [← hround]
          exact hQ

private theorem activeSGVote_preceq
    (S : Setup V) {rho : Run V} {i : Nat} {v : V} {time : Time}
    {a : NamedAttestation V} {B : Block V}
    (hsources : HonestRoundActionActiveSourcesPreceqAtIndex S rho i B)
    (hv : v ∈ rho.honest)
    (hi : rho.events[i]? = some (Event.tick v time))
    (ha : Object.attest a ∈ NamedRun.emittedAt S rho i v time)
    (hround : a.round = S.hc.round_of (actionEventRead S rho i v a.round).st.core.s) :
    Block.Preceq
      (Protocol.get_sg_vote_with
        (NamedProfile.gradeContract (actionEventRead S rho i v a.round).cache)
        S.E S.hc (actionEventRead S rho i v a.round).st.core.toHealing a.round
        (Protocol.grade2_block_with
          (NamedProfile.gradeContract (actionEventRead S rho i v a.round).cache)
          S.E S.hc (actionEventRead S rho i v a.round).st.core.toHealing a.round)) B := by
  let n := actionEventRead S rho i v a.round
  let gc := NamedProfile.gradeContract n.cache
  let st := n.st.core.toHealing
  let grades := DecoupledConsensusModel.Protocol.frameGradeRead n.cache S.E S.hc st a.round
  have hsgB := hsources.sg_root hv hi ha
  change Block.Preceq (Protocol.get_sg_root_with gc S.E S.hc st
    (S.hc.round_of n.st.core.s)) B at hsgB
  rw [← hround] at hsgB
  change Block.Preceq (Protocol.currentSGVote st grades) B
  unfold Protocol.currentSGVote
  cases hclear : Protocol.deepest_clear (some grades.anchor) st.live_confirmed
      grades.clear with
  | some C =>
      exact Block.preceq_trans (Proofs.Engine.deepest_clear_preceq hclear)
        (hsources.live hv hi ha)
  | none =>
      cases hQ : grades.Q2 with
      | some Q =>
          apply hsources.grade2 hv hi ha Q
          change Protocol.grade2_block_with gc S.E S.hc st
            (S.hc.round_of n.st.core.s) = some Q
          rw [← hround]
          exact hQ
      | none =>
          by_cases hraw : grades.rawG2
          · simp only [hclear, hQ, if_pos hraw]
            exact Block.preceq_trans
              (Proofs.HealingSurface.fg_root_preceq_get_sg_root_with_frame
                n.cache S.E S.hc st a.round) hsgB
          · simpa only [hclear, hQ, if_neg hraw] using hsgB

/-- The named emission, retained-source, and root-collision bridges discharge
the exact active-source interface. -/
theorem honestAttestationOutputPreceqAtIndex_of_activeSources
    (S : Setup V) {rho : Run V} (hadm : Admissible S rho)
    {i : Nat} {B : Block V}
    (hsources : HonestRoundActionActiveSourcesPreceqAtIndex S rho i B) :
    HonestAttestationOutputPreceqAtIndex S rho i B := by
  refine ⟨?_, ?_, ?_⟩
  · intro v time a hv hi ha h target hpair X hX hroot
    have hemit := emits_of_emittedAt_tick S hi ha
    have hshape := Proofs.Optimistic.emits_attest_shape S hemit
    have hemit' : NamedRun.emits S rho a.val_index
        (Object.attest a) (S.a a.round) := by
      simpa only [hshape.1, hshape.2] using hemit
    obtain ⟨j, source, entry, hsigned, hheight, hentryRoot⟩ :=
      Proofs.NamedIntrinsicEntry.emitted_height_signed_source S rho hemit' hpair
    have hj : rho.events[j]? = some (Event.tick v time) := by
      rw [hshape.2, ← hshape.1]
      exact hsigned.1
    have hji := index_of_same_event rho.events
      hadm.toNamedAdmissibleCore.nodup hj hi
    subst j
    have hround := emittedRound_at_index S hadm hi ha
    have hsource : Proofs.HealingSurface.actionFGSource S
        (actionEventRead S rho i v a.round) = some source.erase := by
      change Protocol.fg_source_with
        (NamedProfile.gradeContract (actionEventRead S rho i v a.round).cache)
        S.E S.hc (actionEventRead S rho i v a.round).st.core.toHealing
        (S.hc.round_of (actionEventRead S rho i v a.round).st.core.s)
        (Protocol.grade2_block_with
          (NamedProfile.gradeContract (actionEventRead S rho i v a.round).cache)
          S.E S.hc (actionEventRead S rho i v a.round).st.core.toHealing
          (S.hc.round_of (actionEventRead S rho i v a.round).st.core.s)) =
            some source.erase
      rw [← hround]
      simpa only [hshape.1] using hsigned.2.2.2.2.1
    have hsourceB := activeFGSource_preceq S hsources hv hi ha hround hsource
    have haHon : a.val_index ∈ rho.honest := by
      simpa only [hshape.1] using hv
    have hscopes := signedSource_scope S haHon hsigned
    have hentryB : Block.Preceq entry.erase B :=
      Block.preceq_trans (Proofs.NamedWire.erase_preceq hsigned.2.2.2.2.2.1) hsourceB
    have hEq : X = entry := named_eq_of_runBlock_root S hadm hX hscopes.2
      (hroot.trans (hentryRoot.symm.trans (Proofs.NamedWire.erase_root entry).symm))
    simpa only [hEq] using hentryB
  · intro v time a hv hi ha root hconfirmed X hX hroot
    have hemit := emits_of_emittedAt_tick S hi ha
    obtain ⟨j, hj, _, hrow, hval, hround, ht, _⟩ :=
      Proofs.NamedOutageInputs.emitted_attestation_stages S rho hemit
    have hji : j = i := index_of_same_event rho.events
      hadm.toNamedAdmissibleCore.nodup (by simpa only [hval, ht] using hj) hi
    subst j
    let n := actionEventRead S rho i v a.round
    let gc := NamedProfile.gradeContract n.cache
    have hselected : a.confirmed = some
        (Protocol.get_sg_vote_with gc S.E S.hc n.st.core.toHealing a.round
          (Protocol.grade2_block_with gc S.E S.hc n.st.core.toHealing a.round)).root := by
      rw [← hrow]
      rfl
    have hselectedB := activeSGVote_preceq S hsources hv hi ha hround
    have hinv := Proofs.NamedOutageInputs.action_read_invariant S rho i v a.round
    have hmem := Proofs.NamedConfirmationMembership.sg_head_mem n.cache
      S.E S.hc S.cfg n.st hinv
    have hcoh : Proofs.NamedStore.Coherent S.E S.cfg n.st := hinv.1.1
    rw [hcoh.1] at hmem
    obtain ⟨Y, hY, hYerase⟩ := Finset.mem_image.mp hmem
    have hpre : Y ∈ (NamedRun.stateBefore S rho i v).st.bodies := hY
    have hYrun : RunBlock S rho Y := Proofs.NamedRuntime.blockInRun_of_direct S rho
      (Proofs.NamedRuntime.directBlock_of_prefix S rho hv i hpre)
    rw [← hround] at hYerase
    have hYroot : X.erase.root = Y.erase.root := by
      have hselectedRoot : root =
          (Protocol.get_sg_vote_with gc S.E S.hc n.st.core.toHealing a.round
            (Protocol.grade2_block_with gc S.E S.hc n.st.core.toHealing
              a.round)).root := Option.some.inj (hconfirmed.symm.trans hselected)
      exact hroot.trans (hselectedRoot.trans (congrArg Block.root hYerase).symm)
    have hEq := named_eq_of_runBlock_root S hadm hX hYrun hYroot
    rw [hEq, hYerase]
    exact hselectedB
  · intro v time a hv hi ha h hheight
    have hemit := emits_of_emittedAt_tick S hi ha
    cases hp : a.height_pair with
    | empty =>
        rw [hp] at hheight
        simp [NamedHeightPair.erase, HeightPair.height?] at hheight
    | vote height target timeout =>
        rw [hp] at hheight
        have hheq : height = h := by
          cases timeout <;>
            simpa [NamedHeightPair.erase, HeightPair.height?] using hheight
        subst h
        have hshape := Proofs.Optimistic.emits_attest_shape S hemit
        have hemit' : NamedRun.emits S rho a.val_index
            (Object.attest a) (S.a a.round) := by
          simpa only [hshape.1, hshape.2] using hemit
        obtain ⟨j, source, entry, hsigned, hsourceHeight, -⟩ :=
          Proofs.NamedIntrinsicEntry.emitted_height_signed_source S rho hemit' hp
        have hj : rho.events[j]? = some (Event.tick v time) := by
          rw [hshape.2, ← hshape.1]
          exact hsigned.1
        have hji := index_of_same_event rho.events
          hadm.toNamedAdmissibleCore.nodup hj hi
        subst j
        have hround := emittedRound_at_index S hadm hi ha
        have hsource : Proofs.HealingSurface.actionFGSource S
            (actionEventRead S rho i v a.round) = some source.erase := by
          change Protocol.fg_source_with
            (NamedProfile.gradeContract (actionEventRead S rho i v a.round).cache)
            S.E S.hc (actionEventRead S rho i v a.round).st.core.toHealing
            (S.hc.round_of (actionEventRead S rho i v a.round).st.core.s)
            (Protocol.grade2_block_with
              (NamedProfile.gradeContract (actionEventRead S rho i v a.round).cache)
              S.E S.hc (actionEventRead S rho i v a.round).st.core.toHealing
              (S.hc.round_of (actionEventRead S rho i v a.round).st.core.s)) =
                some source.erase
          rw [← hround]
          simpa only [hshape.1] using hsigned.2.2.2.2.1
        have hsourceB := activeFGSource_preceq S hsources hv hi ha hround hsource
        have haHon : a.val_index ∈ rho.honest := by
          simpa only [hshape.1] using hv
        exact ⟨source, (signedSource_scope S haHon hsigned).1,
          hsourceHeight, hsourceB⟩



#print axioms honestAttestationOutputPreceqAtIndex_of_no_emission
#print axioms honestAttestationOutputPreceqAtIndex_of_activeSources
#print axioms emission_index_lt_beforeTime_prefix

end Protocol
end DecoupledConsensusModel

end
