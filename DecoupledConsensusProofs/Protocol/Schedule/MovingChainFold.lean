module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.MovingChainTransfer
public import DecoupledConsensusProofs.Protocol.Grades.MovingChainDispatch
public import DecoupledConsensusProofs.Protocol.Schedule.RecoveryConeConfirmation
public import DecoupledConsensusProofs.Protocol.Grades.ProposalWalkComposition
public import DecoupledConsensusProofs.Protocol.Schedule.WeakProcessedTree
public import DecoupledConsensusProofs.Protocol.ChainState.EntryHeight
public import DecoupledConsensusProofs.Execution.EmissionShape
public import DecoupledConsensusProofs.Protocol.ChainState.ProposalBridge

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! # Moving-frontier slot-fold steps
The moving-chain state records, at every event, the honest proposal-chain
observations, the honest genuine confirmations, the honest Section 7 SG
carriers, the honest attestation outputs and the honest read anchors. A slot
fold must therefore dispatch each event of a slot window on the duty instant of
its tick.
`publicTime_slotWindow_cases` makes the dispatch total: a tick inside the
window `(t_s, t_{s+1}]` happens at the vote duty, the support cutoff, the view
freeze or the next proposal, and nowhere else.
One endpoint step is given for each of those instants. Every instant
separation is discharged here, so a caller only supplies the facts that are
genuinely event-local:
* the proposal step needs nothing beyond the previous endpoint being below the
  proposal parent, and moves the endpoint exactly to the new proposal;
* the view-freeze step needs nothing at all and keeps the endpoint;
* the vote step needs the voter's head sandwiched and its read anchor
  compatible;
* the confirmation step needs the genuine confirmation, the SG carrier when
  the instant is also a Section 7 action, the attestation output and the
  confirmation read anchor.
The proposal event is the only place the public sandwich forces the endpoint
up: a proposal tick emits no attestation, selects no confirmation and reads no
anchor, so the proposed block is the exact next endpoint.
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

/-! ## Duty-instant separations inside one slot -/

/-- The proposal instant of a slot is strictly before its support cutoff. -/
private theorem proposal_time_lt_support_cutoff (E : Env V) (s : Slot) :
    Protocol.proposal_time E s < Protocol.support_cutoff E s := by
  have hvote : Protocol.proposal_time E s < Protocol.vote_time E s :=
    Protocol.proposal_time_lt_vote_time E s
  have hcut : Protocol.vote_time E s < Protocol.support_cutoff E s := by
    rw [← Proofs.Optimistic.vote_time_add_delta]
    exact Int.lt_add_of_pos_right _ E.Δ_pos
  exact hvote.trans hcut

/-- No confirmation evaluation happens at a proposal instant. The evaluation
of slot `s'` is the support cutoff of slot `s' + 1`, which is strictly after
the proposal instant of that slot. -/
private theorem confirmation_time_ne_proposal_time (E : Env V) (s' s : Slot)
    (heq : Protocol.confirmation_time E s' = Protocol.proposal_time E s) :
    False := by
  have hslot : s' + 1 = s := by
    have hcongr := congrArg E.slotOf heq
    rwa [Proofs.Optimistic.slotOf_confirmation_time,
      Proofs.Optimistic.slotOf_proposal_time] at hcongr
  have hcut : Protocol.support_cutoff E (s' + 1) =
      Protocol.proposal_time E (s' + 1) := by
    rw [← Protocol.confirmation_time_eq_support_cutoff_succ, hslot]
    exact heq
  exact absurd hcut.symm (ne_of_lt (proposal_time_lt_support_cutoff E (s' + 1)))

/-- No Goldfish vote duty happens at a proposal instant. -/
private theorem vote_time_ne_proposal_time (E : Env V) (s' s : Slot)
    (heq : Protocol.vote_time E s' = Protocol.proposal_time E s) :
    False := by
  have hslot : s' = s := by
    have hcongr := congrArg E.slotOf heq
    rwa [Proofs.Optimistic.slotOf_vote_time, Proofs.Optimistic.slotOf_proposal_time] at hcongr
  subst hslot
  exact absurd heq.symm (ne_of_lt (Protocol.proposal_time_lt_vote_time E s'))

/-- No Section 7 action instant is a proposal instant. -/
private theorem action_time_ne_proposal_time
    (S : Setup V) (q : Round) (s : Slot)
    (heq : S.a q = Protocol.proposal_time S.E s) :
    False := by
  have hslot : S.E.slotOf (S.a q) = s := by
    rw [heq]
    exact Proofs.Optimistic.slotOf_proposal_time S.E s
  exact (Proofs.Optimistic.a_ne_proposal_time S (rfl : S.a q = S.hc.a S.E.Δ q))
    (by rw [hslot]; exact heq)

/-! ## Slot-relative normal form for the duty instants

Every duty instant is `(4 * slot + offset) * Δ`. Two instants agree exactly
when their normalised offsets agree, so each separation below is one `omega`
fact about residues mod four. -/

private theorem proposal_time_normal (E : Env V) (s : Slot) :
    Protocol.proposal_time E s = (4 * (s : Time) + 0) * E.Δ := by
  unfold Protocol.proposal_time Env.t slotStart
  ring

private theorem vote_time_normal (E : Env V) (s : Slot) :
    Protocol.vote_time E s = (4 * (s : Time) + 1) * E.Δ := by
  unfold Protocol.vote_time Env.t slotStart
  ring

private theorem support_cutoff_normal (E : Env V) (s : Slot) :
    Protocol.support_cutoff E s = (4 * (s : Time) + 2) * E.Δ := by
  unfold Protocol.support_cutoff Env.t slotStart
  ring

private theorem view_freeze_normal (E : Env V) (s : Slot) :
    Protocol.view_freeze E s = (4 * (s : Time) + 3) * E.Δ := by
  unfold Protocol.view_freeze Env.t slotStart
  ring

private theorem confirmation_time_normal (E : Env V) (s : Slot) :
    Protocol.confirmation_time E s = (4 * (s : Time) + 6) * E.Δ := by
  unfold Protocol.confirmation_time Env.t slotStart
  ring

private theorem action_time_normal (S : Setup V) (q : Round) :
    S.a q = (4 * ((S.hc.opening_slot q : Slot) : Time) + 6) * S.E.Δ := by
  unfold Setup.a Protocol.HealConfig.a slotStart
  ring

/-- Two normalised instants with incompatible offsets are distinct. -/
private theorem slotInstant_ne (E : Env V) (a b : Slot) (m n : Int)
    (hmod : ∀ x y : Int, 4 * x + m ≠ 4 * y + n) :
    (4 * (a : Time) + m) * E.Δ ≠ (4 * (b : Time) + n) * E.Δ := by
  intro heq
  exact hmod (a : Time) (b : Time)
    (mul_right_cancel₀ (ne_of_gt E.Δ_pos) heq)

/-- The four public instants of one slot window. Ticks happen only at public
times, so this makes a slot-window event fold total. -/
theorem publicTime_slotWindow_cases (S : Setup V) {t : Time} {s : Slot}
    (hpub : PublicTime S t)
    (hlow : Protocol.proposal_time S.E s < t)
    (hhigh : t ≤ Protocol.proposal_time S.E (s + 1)) :
    t = Protocol.vote_time S.E s ∨
      t = Protocol.support_cutoff S.E s ∨
      t = Protocol.view_freeze S.E s ∨
      t = Protocol.proposal_time S.E (s + 1) := by
  obtain ⟨k, rfl⟩ := hpub
  rw [proposal_time_normal] at hlow hhigh
  have hlow' : 4 * (s : Time) + 0 < (k : Time) := by
    by_contra hnot
    exact absurd hlow (not_lt_of_ge
      (Int.mul_le_mul_of_nonneg_right (le_of_not_gt hnot)
        (le_of_lt S.E.Δ_pos)))
  have hhigh' : (k : Time) ≤ 4 * ((s + 1 : Slot) : Time) + 0 := by
    by_contra hnot
    exact absurd hhigh (not_le_of_gt
      (Int.mul_lt_mul_of_pos_right (lt_of_not_ge hnot) S.E.Δ_pos))
  have hlowI : 4 * (s : Int) + 0 < (k : Int) := hlow'
  have hhighI : (k : Int) ≤ 4 * ((s + 1 : Nat) : Int) + 0 := hhigh'
  have hk : 4 * (s : Time) + 1 = (k : Time) ∨
      4 * (s : Time) + 2 = (k : Time) ∨
      4 * (s : Time) + 3 = (k : Time) ∨
      4 * (s : Time) + 4 = (k : Time) := by
    show 4 * (s : Int) + 1 = (k : Int) ∨ 4 * (s : Int) + 2 = (k : Int) ∨
      4 * (s : Int) + 3 = (k : Int) ∨ 4 * (s : Int) + 4 = (k : Int)
    omega
  rcases hk with hkv | hkc | hkf | hkp
  · exact Or.inl (by rw [vote_time_normal, ← hkv])
  · exact Or.inr (Or.inl (by rw [support_cutoff_normal, ← hkc]))
  · exact Or.inr (Or.inr (Or.inl (by rw [view_freeze_normal, ← hkf])))
  · refine Or.inr (Or.inr (Or.inr ?_))
    rw [proposal_time_normal, ← hkp]
    push_cast
    ring

omit [DecidableEq V] [Fintype V] in
private theorem tick_node_time_eq_of_same_index
    {rho : Run V} {i : Nat} {v w : V} {t u : Time}
    (h₁ : rho.events[i]? = some (Event.tick v t))
    (h₂ : rho.events[i]? = some (Event.tick w u)) : v = w ∧ t = u := by
  simpa using Option.some.inj (h₁.symm.trans h₂)

/-! ## The honest proposal endpoint step -/

/-- Lowering the left end of a proposal-chain sandwich. -/
private theorem proposalChainObservationsSandwichedAtIndex_mono_left
    {S : Setup V} {rho : Run V} {i : Nat} {A A' B : Block V}
    (h : ProposalChainObservationsSandwichedAtIndex S rho i A B)
    (hA : Block.Preceq A' A) :
    ProposalChainObservationsSandwichedAtIndex S rho i A' B := by
  intro stage C hstage hobs
  exact ⟨Block.preceq_trans hA (h stage C hstage hobs).1,
    (h stage C hstage hobs).2⟩

private theorem proposedParent_preceq_proposedBlockAt
    (S : Setup V) (rho : Run V) (s : Slot) {P : NamedBlock V}
    (hP : proposedBlockAt S rho s = some P) :
    Block.Preceq (proposedParent S rho s) P.erase := by
  obtain ⟨p, hp, hparent⟩ := proposedBlockAt_parent S rho s hP
  rw [← hparent]
  cases P with
  | genesis => simp only [NamedBlock.parent?, reduceCtorEq] at hp
  | node parent slot root votes support rows proposer =>
      simp only [NamedBlock.parent?, Option.some.injEq] at hp
      subst hp
      apply Protocol.preceq_of_parent?
      rfl

private theorem proposalStageBlockAtIndex_parent_local
    (S : Setup V) (rho : Run V) (i : Nat) (v : V) (t : Time) {B : NamedBlock V}
    (hB : proposalStageBlockAtIndex S rho i v t = some B) :
    ∃ p : NamedBlock V, NamedBlock.parent? B = some p ∧
      p.erase = proposalStageHeadAtIndex S rho i v t := by
  simp only [proposalStageBlockAtIndex, proposalStageHeadAtIndex,
    Proofs.NamedActions.proposal_shared_read] at hB ⊢
  rw [Option.map_eq_some_iff] at hB
  obtain ⟨p, hp, hBeq⟩ := hB
  subst hBeq
  exact ⟨p, rfl, (Proofs.NamedActions.parent_body_spec _ _ p hp).2⟩


/-- Advance the moving chain across one tick at a proposal instant.

A proposal instant is not a vote duty, not a confirmation evaluation and not a
Section 7 action instant. The event therefore selects no genuine confirmation,
carries no SG block, emits no attestation and reads no anchor. The only
possible event-local facts are the proposal parent and the proposed block, and
they occur only at the tick of the slot's own proposer.

Every honest node ticks at a proposal instant, so the proposer condition is a
hypothesis rather than a side condition: a tick by any other honest node, and
every tick of a Byzantine-proposer slot, discharges it vacuously and keeps the
endpoint. -/
theorem movingEventFacts_proposalInstant
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {i : Nat} {u : V} {s : Slot}
    (hevent : rho.events[i]? = some
      (Event.tick u (Protocol.proposal_time S.E s)))
    {Before Next : Block V}
    (hproposer : S.E.proposer s = (S.node u).val_index →
      Block.Preceq Before (proposedParent S rho s) ∧
        ∃ P : NamedBlock V, proposedBlockAt S rho s = some P ∧
          Block.Preceq P.erase Next) :
    ProposalChainObservationsSandwichedAtIndex S rho i Before Next ∧
      GenuineConfirmationsPreceqAtIndex S rho i Next ∧
      HonestActionSGCarriersPreceqAtIndex S rho i Next ∧
      HonestAttestationOutputPreceqAtIndex S rho i Next ∧
      ReadAnchorsAtIndex S rho i Next := by
  have hslotEq : S.E.slotOf (Protocol.proposal_time S.E s) = s :=
    Proofs.Optimistic.slotOf_proposal_time S.E s
  have htickPair : ∀ {w : V} {t : Time},
      rho.events[i]? = some (Event.tick w t) →
        w = u ∧ t = Protocol.proposal_time S.E s := by
    intro w t hw
    have heq : Event.tick w t = Event.tick u (Protocol.proposal_time S.E s) :=
      Option.some.inj (hw.symm.trans hevent)
    cases heq
    exact ⟨rfl, rfl⟩
  have hproposal : ProposalChainObservationsSandwichedAtIndex
      S rho i Before Next := by
    intro stage B hstage hobs
    cases hobs with
    | @proposalParent v t _ hevt hactive =>
        obtain ⟨rfl, rfl⟩ := htickPair hevt
        have hactiveSlot := hactive.2.2
        rw [hslotEq] at hactiveSlot
        obtain ⟨hlow, P, hP, hhigh⟩ := hproposer hactiveSlot
        have hblk := proposalStageBlockAtIndex_eq_proposedBlock
          S adm hevt hactive
        rw [hslotEq] at hblk
        have hcomputed := hblk.trans hP
        obtain ⟨p, hp, hpe⟩ := proposalStageBlockAtIndex_parent_local
          S rho i _ _ hcomputed
        obtain ⟨p', hp', hpe'⟩ := proposedBlockAt_parent S rho s hP
        have hpp : p = p' := Option.some.inj (hp.symm.trans hp')
        have hpar := hpe.symm.trans
          ((congrArg NamedBlock.erase hpp).trans hpe')
        rw [hpar]
        exact ⟨hlow, Block.preceq_trans
          (proposedParent_preceq_proposedBlockAt S rho s hP) hhigh⟩
    | proposedBlock _ hevt hactive computed =>
        obtain ⟨rfl, rfl⟩ := htickPair hevt
        have hactiveSlot := hactive.2.2
        rw [hslotEq] at hactiveSlot
        obtain ⟨hlow, P, hP, hhigh⟩ := hproposer hactiveSlot
        have hblk := proposalStageBlockAtIndex_eq_proposedBlock
          S adm hevt hactive
        rw [hslotEq] at hblk
        have hP' : proposedBlockAt S rho s = some _ :=
          hblk.symm.trans computed
        have hBP : P = _ := Option.some.inj (hP.symm.trans hP')
        subst P
        exact ⟨Block.preceq_trans hlow
          (proposedParent_preceq_proposedBlockAt S rho s hP'), hhigh⟩
    | voteHead _ hevt hactive _ _ =>
        obtain ⟨rfl, rfl⟩ := htickPair hevt
        have hvote := hactive.2
        rw [hslotEq] at hvote
        exact (vote_time_ne_proposal_time S.E s s hvote.symm).elim
    | confirmationOutput =>
        simp only [ProposalChainStage] at hstage
        omega
    | actionHead =>
        simp only [ProposalChainStage] at hstage
        omega
  have hconfirmations : GenuineConfirmationsPreceqAtIndex S rho i Next := by
    intro w _hw C hC
    obtain ⟨s', hevt, _hgenuine⟩ := hC
    exact (confirmation_time_ne_proposal_time S.E s' s
      (htickPair hevt).2).elim
  have hsg : HonestActionSGCarriersPreceqAtIndex S rho i Next := by
    intro w q a _hw hevt _ha
    exact (action_time_ne_proposal_time S q s (htickPair hevt).2).elim
  have hnoEmission : ¬ HonestAttestationEmissionAtIndex S rho i := by
    rintro ⟨w, time, a, _hw, hevt, ha⟩
    have hemits : rho.emits S w (Object.attest a) time := ⟨i, hevt, ha⟩
    have hshape := Proofs.Optimistic.emits_attest_shape S hemits
    exact action_time_ne_proposal_time S a.round s
      (hshape.2.symm.trans (htickPair hevt).2)
  have hout : HonestAttestationOutputPreceqAtIndex S rho i Next :=
    honestAttestationOutputPreceqAtIndex_of_no_emission S rho hnoEmission
  have hanchors : ReadAnchorsAtIndex S rho i Next := by
    refine { voteCompatible := ?_, confirmationCompatible := ?_ }
    · intro w s' _hw hevt
      exact (vote_time_ne_proposal_time S.E s' s (htickPair hevt).2).elim
    · intro w s' _hw hevt
      exact (confirmation_time_ne_proposal_time S.E s' s
        (htickPair hevt).2).elim
  exact ⟨hproposal, hconfirmations, hsg, hout, hanchors⟩



/-! ## The view-freeze and vote endpoint steps -/

/-- The view freeze makes no honest observation.

`t_s + 3Δ` is a tick instant, but no `on_tick` branch fires there: it is not a
proposal instant, not a Goldfish vote duty, not a confirmation evaluation and
not a Section 7 action. The moving endpoint is therefore unchanged. -/
theorem movingEventFacts_viewFreeze
    (S : Setup V) {rho : Run V} {i : Nat} {Next : Block V}
    {w : V} {s : Slot}
    (hevent : rho.events[i]? = some
      (Event.tick w (Protocol.view_freeze S.E s))) :
    ProposalChainObservationsSandwichedAtIndex S rho i Next Next ∧
      GenuineConfirmationsPreceqAtIndex S rho i Next ∧
      HonestActionSGCarriersPreceqAtIndex S rho i Next ∧
      HonestAttestationOutputPreceqAtIndex S rho i Next ∧
      ReadAnchorsAtIndex S rho i Next := by
  have htickTime : ∀ {u : V} {t : Time},
      rho.events[i]? = some (Event.tick u t) →
        t = Protocol.view_freeze S.E s := by
    intro u t hu
    exact (tick_node_time_eq_of_same_index hu hevent).2
  have hproposalNe : ∀ s' : Slot,
      Protocol.view_freeze S.E s ≠ Protocol.proposal_time S.E s' := by
    intro s'
    rw [view_freeze_normal, proposal_time_normal]
    exact slotInstant_ne S.E s s' 3 0 (by intro x y; omega)
  have hvoteNe : ∀ s' : Slot,
      Protocol.view_freeze S.E s ≠ Protocol.vote_time S.E s' := by
    intro s'
    rw [view_freeze_normal, vote_time_normal]
    exact slotInstant_ne S.E s s' 3 1 (by intro x y; omega)
  have hconfNe : ∀ s' : Slot,
      Protocol.confirmation_time S.E s' ≠ Protocol.view_freeze S.E s := by
    intro s'
    rw [view_freeze_normal, confirmation_time_normal]
    exact slotInstant_ne S.E s' s 6 3 (by intro x y; omega)
  have hactionNe : ∀ q : Round,
      S.a q ≠ Protocol.view_freeze S.E s := by
    intro q
    rw [view_freeze_normal, action_time_normal]
    exact slotInstant_ne S.E (S.hc.opening_slot q) s 6 3 (by intro x y; omega)
  have hproposal : ProposalChainObservationsSandwichedAtIndex
      S rho i Next Next := by
    intro stage B hstage hobs
    cases hobs with
    | proposalParent _ hevt hactive =>
        obtain rfl := htickTime hevt
        exact absurd hactive.2.1 (hproposalNe _)
    | proposedBlock _ hevt hactive =>
        obtain rfl := htickTime hevt
        exact absurd hactive.2.1 (hproposalNe _)
    | voteHead _ hevt hactive _ _ =>
        obtain rfl := htickTime hevt
        exact absurd hactive.2 (hvoteNe _)
    | confirmationOutput =>
        simp only [ProposalChainStage] at hstage
        omega
    | actionHead =>
        simp only [ProposalChainStage] at hstage
        omega
  have hconfirmations : GenuineConfirmationsPreceqAtIndex S rho i Next := by
    intro u _hu C hC
    obtain ⟨s', hevt, _hgenuine⟩ := hC
    exact absurd (htickTime hevt) (hconfNe s')
  have hsg : HonestActionSGCarriersPreceqAtIndex S rho i Next := by
    intro u q a _hu hevt _ha
    exact absurd (htickTime hevt) (hactionNe q)
  have hnoEmission : ¬ HonestAttestationEmissionAtIndex S rho i := by
    rintro ⟨u, time, a, _hu, hevt, ha⟩
    have hemits : rho.emits S u (Object.attest a) time := ⟨i, hevt, ha⟩
    have hshape := Proofs.Optimistic.emits_attest_shape S hemits
    exact hactionNe a.round (hshape.2.symm.trans (htickTime hevt))
  have hout : HonestAttestationOutputPreceqAtIndex S rho i Next :=
    honestAttestationOutputPreceqAtIndex_of_no_emission S rho hnoEmission
  have hanchors : ReadAnchorsAtIndex S rho i Next := by
    refine { voteCompatible := ?_, confirmationCompatible := ?_ }
    · intro u s' _hu hevt
      exact absurd (htickTime hevt) (fun heq => hvoteNe s' heq.symm)
    · intro u s' _hu hevt
      exact absurd (htickTime hevt) (hconfNe s')
  exact ⟨hproposal, hconfirmations, hsg, hout, hanchors⟩



/-- Named event facts for an honest Goldfish vote tick. -/
private theorem movingEventFacts_vote_at_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {i : Nat} {w : V} {s : Slot}
    (hevent : rho.events[i]? = some
      (Event.tick w (Protocol.vote_time S.E s)))
    {Next : Block V}
    (hhead : S.E.proposer s ∈ rho.honest →
      Block.Preceq Next (voteDutyHead S rho w s) ∧
        Block.Preceq (voteDutyHead S rho w s) Next)
    (hanchor : Block.compatible (voterAnchorAt S rho w s) Next = true) :
    ProposalChainObservationsSandwichedAtIndex S rho i Next Next ∧
      NamedGenuineConfirmationsPreceqAtIndex S rho i Next ∧
      HonestActionSGCarriersPreceqAtIndex S rho i Next ∧
      HonestAttestationOutputPreceqAtIndex S rho i Next ∧
      NamedReadAnchorsAtIndex S rho i Next := by
  have hslotEq : S.E.slotOf (Protocol.vote_time S.E s) = s :=
    Proofs.Optimistic.slotOf_vote_time S.E s
  have htickPair : ∀ {u : V} {t : Time},
      rho.events[i]? = some (Event.tick u t) →
        u = w ∧ t = Protocol.vote_time S.E s := by
    intro u t hu
    exact tick_node_time_eq_of_same_index hu hevent
  have hproposalNe : ∀ s' : Slot,
      Protocol.vote_time S.E s ≠ Protocol.proposal_time S.E s' := by
    intro s'
    rw [vote_time_normal, proposal_time_normal]
    exact slotInstant_ne S.E s s' 1 0 (by intro x y; omega)
  have hconfNe : ∀ s' : Slot,
      Protocol.confirmation_time S.E s' ≠ Protocol.vote_time S.E s := by
    intro s'
    rw [vote_time_normal, confirmation_time_normal]
    exact slotInstant_ne S.E s' s 6 1 (by intro x y; omega)
  have hactionNe : ∀ q : Round,
      S.a q ≠ Protocol.vote_time S.E s := by
    intro q
    rw [vote_time_normal, action_time_normal]
    exact slotInstant_ne S.E (S.hc.opening_slot q) s 6 1 (by intro x y; omega)
  have hproposal : ProposalChainObservationsSandwichedAtIndex
      S rho i Next Next := by
    intro stage B hstage hobs
    cases hobs with
    | proposalParent _ hevt hactive =>
        obtain ⟨rfl, rfl⟩ := htickPair hevt
        exact absurd hactive.2.1 (hproposalNe _)
    | proposedBlock _ hevt hactive =>
        obtain ⟨rfl, rfl⟩ := htickPair hevt
        exact absurd hactive.2.1 (hproposalNe _)
    | voteHead _ hevt hactive hproposerHonest _ =>
        obtain ⟨rfl, rfl⟩ := htickPair hevt
        have hproposerSlot : S.E.proposer s ∈ rho.honest := by
          simpa only [hslotEq] using hproposerHonest
        rw [voteStageHeadAtIndex_eq_voteDutyHead S adm hevt hactive, hslotEq]
        exact hhead hproposerSlot
    | confirmationOutput =>
        simp only [ProposalChainStage] at hstage
        omega
    | actionHead =>
        simp only [ProposalChainStage] at hstage
        omega
  have hconfirmations : NamedGenuineConfirmationsPreceqAtIndex
      S rho i Next := by
    intro u _hu C hC
    obtain ⟨s', hevt, _hgenuine⟩ := hC
    exact absurd (htickPair hevt).2 (hconfNe s')
  have hsg : HonestActionSGCarriersPreceqAtIndex S rho i Next := by
    intro u q a _hu hevt _ha
    exact absurd (htickPair hevt).2 (hactionNe q)
  have hnoEmission : ¬ HonestAttestationEmissionAtIndex S rho i := by
    rintro ⟨u, time, a, _hu, hevt, ha⟩
    have hemits : rho.emits S u (Object.attest a) time := ⟨i, hevt, ha⟩
    have hshape := Proofs.Optimistic.emits_attest_shape S hemits
    exact hactionNe a.round (hshape.2.symm.trans (htickPair hevt).2)
  have hout : HonestAttestationOutputPreceqAtIndex S rho i Next :=
    honestAttestationOutputPreceqAtIndex_of_no_emission S rho hnoEmission
  have hanchors : NamedReadAnchorsAtIndex S rho i Next := by
    refine { voteCompatible := ?_, confirmationCompatible := ?_ }
    · intro u s' _hu hevt
      obtain ⟨rfl, hteq⟩ := htickPair hevt
      have hs' : s' = s := by
        have hcongr := congrArg S.E.slotOf hteq
        rwa [Proofs.Optimistic.slotOf_vote_time, Proofs.Optimistic.slotOf_vote_time]
          at hcongr
      subst hs'
      exact hanchor
    · intro u s' _hu hevt
      exact absurd (htickPair hevt).2 (hconfNe s')
  exact ⟨hproposal, hconfirmations, hsg, hout, hanchors⟩


/-- Named event facts for an honest confirmation tick. -/
private theorem movingEventFacts_confirmation_at_named
    (S : Setup V) {rho : Run V} {i : Nat} {w : V} {s : Slot}
    (hevent : rho.events[i]? = some
      (Event.tick w (Protocol.confirmation_time S.E s)))
    {Next : Block V}
    (hgenuine : ∀ C : Block V,
      GenuineConfirmationWith
        (NamedProfile.gradeContract
          (confirmationInputRead S rho w s).cache)
        S.E S.hc (Proofs.Optimistic.confStore S rho w s) s C →
        Block.Preceq C Next)
    (hcarrier : ∀ q : Round,
      S.a q = Protocol.confirmation_time S.E s →
        Block.Preceq (actionSGBlockAt S rho w q) Next)
    (hout : HonestAttestationOutputPreceqAtIndex S rho i Next)
    (hanchor : Block.compatible
      (confirmationAnchorAt S rho w s) Next = true) :
    ProposalChainObservationsSandwichedAtIndex S rho i Next Next ∧
      NamedGenuineConfirmationsPreceqAtIndex S rho i Next ∧
      HonestActionSGCarriersPreceqAtIndex S rho i Next ∧
      HonestAttestationOutputPreceqAtIndex S rho i Next ∧
      NamedReadAnchorsAtIndex S rho i Next := by
  have htickPair : ∀ {u : V} {t : Time},
      rho.events[i]? = some (Event.tick u t) →
        u = w ∧ t = Protocol.confirmation_time S.E s := by
    intro u t hu
    exact tick_node_time_eq_of_same_index hu hevent
  have hslotEq : ∀ s' : Slot,
      Protocol.confirmation_time S.E s' = Protocol.confirmation_time S.E s →
        s' = s := by
    intro s' heq
    have hcongr := congrArg S.E.slotOf heq
    rw [Proofs.Optimistic.slotOf_confirmation_time,
      Proofs.Optimistic.slotOf_confirmation_time] at hcongr
    exact Nat.add_right_cancel hcongr
  have hproposalNe : ∀ s' : Slot,
      Protocol.confirmation_time S.E s ≠ Protocol.proposal_time S.E s' := by
    intro s'
    rw [confirmation_time_normal, proposal_time_normal]
    exact slotInstant_ne S.E s s' 6 0 (by intro x y; omega)
  have hvoteNe : ∀ s' : Slot,
      Protocol.confirmation_time S.E s ≠ Protocol.vote_time S.E s' := by
    intro s'
    rw [confirmation_time_normal, vote_time_normal]
    exact slotInstant_ne S.E s s' 6 1 (by intro x y; omega)
  have hproposal : ProposalChainObservationsSandwichedAtIndex
      S rho i Next Next := by
    intro stage B hstage hobs
    cases hobs with
    | proposalParent _ hevt hactive =>
        obtain ⟨rfl, rfl⟩ := htickPair hevt
        exact absurd hactive.2.1 (hproposalNe _)
    | proposedBlock _ hevt hactive =>
        obtain ⟨rfl, rfl⟩ := htickPair hevt
        exact absurd hactive.2.1 (hproposalNe _)
    | voteHead _ hevt hactive _ _ =>
        obtain ⟨rfl, rfl⟩ := htickPair hevt
        exact absurd hactive.2 (hvoteNe _)
    | confirmationOutput =>
        simp only [ProposalChainStage] at hstage
        omega
    | actionHead =>
        simp only [ProposalChainStage] at hstage
        omega
  have hconfirmations : NamedGenuineConfirmationsPreceqAtIndex
      S rho i Next := by
    intro u _hu C hC
    obtain ⟨s', hevt, hgen⟩ := hC
    obtain ⟨rfl, hteq⟩ := htickPair hevt
    have hss : s' = s := hslotEq s' hteq
    subst hss
    exact hgenuine C hgen
  have hsg : HonestActionSGCarriersPreceqAtIndex S rho i Next := by
    intro u q a _hu hevt _ha
    obtain ⟨rfl, hteq⟩ := htickPair hevt
    exact hcarrier q hteq
  have hanchors : NamedReadAnchorsAtIndex S rho i Next := by
    refine { voteCompatible := ?_, confirmationCompatible := ?_ }
    · intro u s' _hu hevt
      exact absurd (htickPair hevt).2 (fun heq => hvoteNe s' heq.symm)
    · intro u s' _hu hevt
      obtain ⟨rfl, hteq⟩ := htickPair hevt
      have hss : s' = s := hslotEq s' hteq
      subst hss
      exact hanchor
  exact ⟨hproposal, hconfirmations, hsg, hout, hanchors⟩

/-! ## Folding an interval on which the endpoint is constant -/


/-! ## The slot window

The window of slot `s` is the event interval `[incl(t_s), incl(t_{s+1}))`. Its
ticks happen at the four instants of `publicTime_slotWindow_cases`. The prefix
`[incl(t_s), incl(t_s + 3Δ))` carries the slot-`s` vote duty, the slot-`(s-1)`
confirmation evaluation and the view freeze; the tail carries the slot-`(s+1)`
proposal alone. -/

private theorem vote_time_le_view_freeze (E : Env V) (s : Slot) :
    Protocol.vote_time E s ≤ Protocol.view_freeze E s := by
  rw [vote_time_normal, view_freeze_normal]
  exact Int.mul_le_mul_of_nonneg_right (by omega) (le_of_lt E.Δ_pos)

private theorem support_cutoff_le_view_freeze (E : Env V) (s : Slot) :
    Protocol.support_cutoff E s ≤ Protocol.view_freeze E s := by
  rw [support_cutoff_normal, view_freeze_normal]
  exact Int.mul_le_mul_of_nonneg_right (by omega) (le_of_lt E.Δ_pos)

private theorem vote_time_lt_support_cutoff (E : Env V) (s : Slot) :
    Protocol.vote_time E s < Protocol.support_cutoff E s := by
  rw [vote_time_normal, support_cutoff_normal]
  exact Int.mul_lt_mul_of_pos_right (by omega) E.Δ_pos

private theorem proposal_time_le_view_freeze (E : Env V) (s : Slot) :
    Protocol.proposal_time E s ≤ Protocol.view_freeze E s := by
  rw [proposal_time_normal, view_freeze_normal]
  exact Int.mul_le_mul_of_nonneg_right (by omega) (le_of_lt E.Δ_pos)

private theorem view_freeze_lt_proposal_time_succ (E : Env V) (s : Slot) :
    Protocol.view_freeze E s < Protocol.proposal_time E (s + 1) := by
  rw [view_freeze_normal, proposal_time_normal]
  refine Int.mul_lt_mul_of_pos_right ?_ E.Δ_pos
  have hcast : ((s + 1 : Nat) : Int) = (s : Int) + 1 := by push_cast; ring
  rw [hcast]
  omega

/-- The support cutoff of slot `s` is the confirmation evaluation of the
previous slot: `t_s + 2Δ = t_{s-1} + 6Δ`. -/
theorem support_cutoff_eq_confirmation_time_pred (E : Env V) {s : Slot}
    (hs : 0 < s) :
    Protocol.support_cutoff E s = Protocol.confirmation_time E (s - 1) := by
  have hsucc : s - 1 + 1 = s := Nat.succ_pred_eq_of_pos hs
  rw [Protocol.confirmation_time_eq_support_cutoff_succ, hsucc]

/-- An event at or after the inclusive cursor of `t0` happens strictly after
`t0`. -/
private theorem eventTime_gt_of_inclusive_le
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    {t0 : Time} {j : Nat} {e : Event V}
    (hj : inclusiveEventIndex rho t0 ≤ j)
    (hget : rho.events[j]? = some e) :
    t0 < e.time := by
  have hfalse := Proofs.Optimistic.filter_false_of_index_ge S sch _
    (Proofs.Optimistic.downward_le t0)
    (by simpa only [inclusiveEventIndex] using hj) hget
  simpa only [decide_eq_false_iff_not, not_le] using hfalse

/-- An event strictly before the inclusive cursor of `t0` happens at or before
`t0`. -/
private theorem eventTime_le_of_lt_inclusive
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    {t0 : Time} {j : Nat} {e : Event V}
    (hj : j < inclusiveEventIndex rho t0)
    (hget : rho.events[j]? = some e) :
    e.time ≤ t0 := by
  have htrue := Proofs.Optimistic.filter_true_of_index_lt S sch _
    (Proofs.Optimistic.downward_le t0)
    (by simpa only [inclusiveEventIndex] using hj) hget
  simpa only [decide_eq_true_eq] using htrue


/-! The compatibility `MovingSlotWindowFacts` above is still consumed by the erased
event-indexed moving-chain interface. Its confirmation and confirmation-anchor
fields cannot be filled from a prepared named read: the prepared contract is
not definitionally `Protocol.GradeContract.current`. Keep that interface
stable and state the named replacement with the read's contract and anchor. -/

/-- Event-local facts for a moving window at a prepared named read. -/
structure NamedMovingSlotWindowFacts
    (S : Setup V) (rho : Run V) (s : Slot) (End Next : Block V) : Prop where
  endLe : Block.Preceq End Next
  voteHead : S.E.proposer s ∈ rho.honest → ∀ w ∈ rho.honest,
    voteDutyHead S rho w s = End
  voteAnchor : ∀ w ∈ rho.honest,
    Block.compatible (voterAnchorAt S rho w s) End = true
  confirmed : ∀ w ∈ rho.honest, ∀ C : Block V,
    GenuineConfirmationWith
      (NamedProfile.gradeContract
        (confirmationInputRead S rho w (s - 1)).cache)
      S.E S.hc (Proofs.Optimistic.confStore S rho w (s - 1)) (s - 1) C →
      Block.Preceq C Next
  carrier : ∀ w ∈ rho.honest, ∀ q : Round,
    S.a q = Protocol.confirmation_time S.E (s - 1) →
      Block.Preceq (actionSGBlockAt S rho w q) Next
  outputs : ∀ (j : Nat) (w : V), w ∈ rho.honest →
    rho.events[j]? = some
        (Event.tick w (Protocol.confirmation_time S.E (s - 1))) →
      HonestAttestationOutputPreceqAtIndex S rho j Next
  confAnchorCompatible : ∀ w ∈ rho.honest,
    Block.compatible
      (confirmationAnchorAt S rho w (s - 1)) Next = true

private theorem movingEventFacts_of_no_tick_named
    (S : Setup V) (rho : Run V) {i : Nat} (Next : Block V)
    (hno : ∀ (w : V) (t : Time),
      rho.events[i]? ≠ some (Event.tick w t)) :
    ProposalChainObservationsSandwichedAtIndex S rho i Next Next ∧
      NamedGenuineConfirmationsPreceqAtIndex S rho i Next ∧
      HonestActionSGCarriersPreceqAtIndex S rho i Next ∧
      HonestAttestationOutputPreceqAtIndex S rho i Next ∧
      NamedReadAnchorsAtIndex S rho i Next := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro stage B hstage hobs
    cases hobs with
    | proposalParent _ hevent _ => exact absurd hevent (hno _ _)
    | proposedBlock _ hevent _ => exact absurd hevent (hno _ _)
    | voteHead _ hevent _ _ _ => exact absurd hevent (hno _ _)
    | confirmationOutput _ hevent _ => exact absurd hevent (hno _ _)
    | actionHead _ hevent _ => exact absurd hevent (hno _ _)
  · intro v _hv C hC
    obtain ⟨s, hevent, _⟩ := hC
    exact absurd hevent (hno _ _)
  · intro v q a _hv hevent _ha
    exact absurd hevent (hno _ _)
  · refine honestAttestationOutputPreceqAtIndex_of_no_emission S rho ?_
    rintro ⟨v, time, a, _hv, hevent, _ha⟩
    exact absurd hevent (hno _ _)
  · refine { voteCompatible := ?_, confirmationCompatible := ?_ }
    · intro v s _hv hevent
      exact absurd hevent (hno _ _)
    · intro v s _hv hevent
      exact absurd hevent (hno _ _)

private theorem movingEventFacts_viewFreeze_at_named
    (S : Setup V) {rho : Run V} {i : Nat} {Next : Block V}
    {w : V} {s : Slot}
    (hevent : rho.events[i]? = some
      (Event.tick w (Protocol.view_freeze S.E s))) :
    ProposalChainObservationsSandwichedAtIndex S rho i Next Next ∧
      NamedGenuineConfirmationsPreceqAtIndex S rho i Next ∧
      HonestActionSGCarriersPreceqAtIndex S rho i Next ∧
      HonestAttestationOutputPreceqAtIndex S rho i Next ∧
      NamedReadAnchorsAtIndex S rho i Next := by
  obtain ⟨hproposal, _hconfirmations, hsg, hout, _hanchors⟩ :=
    movingEventFacts_viewFreeze S hevent
  have htickTime : ∀ {u : V} {t : Time},
      rho.events[i]? = some (Event.tick u t) →
        t = Protocol.view_freeze S.E s := by
    intro u t hu
    exact (tick_node_time_eq_of_same_index hu hevent).2
  have hvoteNe : ∀ s' : Slot,
      Protocol.view_freeze S.E s ≠ Protocol.vote_time S.E s' := by
    intro s'
    rw [view_freeze_normal, vote_time_normal]
    exact slotInstant_ne S.E s s' 3 1 (by intro x y; omega)
  have hconfNe : ∀ s' : Slot,
      Protocol.confirmation_time S.E s' ≠ Protocol.view_freeze S.E s := by
    intro s'
    rw [view_freeze_normal, confirmation_time_normal]
    exact slotInstant_ne S.E s' s 6 3 (by intro x y; omega)
  have hconfirmations : NamedGenuineConfirmationsPreceqAtIndex
      S rho i Next := by
    intro u _hu C hC
    obtain ⟨s', hevt, _hgen⟩ := hC
    exact absurd (htickTime hevt) (hconfNe s')
  have hanchors : NamedReadAnchorsAtIndex S rho i Next := by
    refine { voteCompatible := ?_, confirmationCompatible := ?_ }
    · intro u s' _hu hevt
      exact absurd (htickTime hevt) (fun heq => hvoteNe s' heq.symm)
    · intro u s' _hu hevt
      exact absurd (htickTime hevt) (hconfNe s')
  exact ⟨hproposal, hconfirmations, hsg, hout, hanchors⟩

/-- Named facts for every event of the VOTE phase of a slot window. -/
theorem movingEventFacts_vote_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {s : Slot} {End Next : Block V}
    (hfacts : NamedMovingSlotWindowFacts S rho s End Next)
    {j : Nat}
    (hlow : inclusiveEventIndex rho (Protocol.proposal_time S.E s) ≤ j)
    (hhigh : j < strictEventIndex rho (Protocol.support_cutoff S.E s)) :
    ProposalChainObservationsSandwichedAtIndex S rho j End End ∧
      NamedGenuineConfirmationsPreceqAtIndex S rho j End ∧
      HonestActionSGCarriersPreceqAtIndex S rho j End ∧
      HonestAttestationOutputPreceqAtIndex S rho j End ∧
      NamedReadAnchorsAtIndex S rho j End := by
  cases hev : rho.events[j]? with
  | none =>
      refine movingEventFacts_of_no_tick_named S rho End ?_
      intro w t htick
      rw [hev] at htick
      simp only [reduceCtorEq] at htick
  | some e =>
      cases e with
      | deliver v o t =>
          refine movingEventFacts_of_no_tick_named S rho End ?_
          intro w t' htick
          rw [hev] at htick
          simp only [Option.some.injEq, reduceCtorEq] at htick
      | tick u t =>
          have hmem : Event.tick u t ∈ rho.events := List.mem_of_getElem? hev
          have hpub : PublicTime S t := adm.tick_public u t hmem
          have hgt : Protocol.proposal_time S.E s < t :=
            eventTime_gt_of_inclusive_le
              S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hlow hev
          have hlt : t < Protocol.support_cutoff S.E s := by
            have htrue := Proofs.Optimistic.filter_true_of_index_lt
              S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed _
              (Proofs.Optimistic.downward_lt (Protocol.support_cutoff S.E s))
              (by simpa only [strictEventIndex] using hhigh) hev
            simpa only [decide_eq_true_eq, Event.time] using htrue
          have hhonest : u ∈ rho.honest := by
            simpa only [Event.node] using adm.honest_only _ hmem
          rcases publicTime_slotWindow_cases S hpub hgt
            (le_of_lt (lt_of_lt_of_le hlt
              ((support_cutoff_le_view_freeze S.E s).trans
                (le_of_lt (view_freeze_lt_proposal_time_succ S.E s)))))
            with ht | ht | ht | ht
          · subst ht
            refine movingEventFacts_vote_at_named S adm hev ?_
              (hfacts.voteAnchor u hhonest)
            intro hp
            rw [hfacts.voteHead hp u hhonest]
            exact ⟨Block.preceq_self _, Block.preceq_self _⟩
          · exact absurd (ht ▸ hlt) (lt_irrefl _)
          · exact absurd (ht ▸ hlt)
              (not_lt_of_ge (support_cutoff_le_view_freeze S.E s))
          · exact absurd (ht ▸ hlt) (not_lt_of_ge
              (le_of_lt (lt_of_le_of_lt (support_cutoff_le_view_freeze S.E s)
                (view_freeze_lt_proposal_time_succ S.E s))))

/-- Named facts for every event of the CONFIRMATION phase of a slot window. -/
theorem movingEventFacts_confirmation_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {s : Slot} (hs : 0 < s) {End Next : Block V}
    (hfacts : NamedMovingSlotWindowFacts S rho s End Next)
    {j : Nat}
    (hlow : strictEventIndex rho (Protocol.support_cutoff S.E s) ≤ j)
    (hhigh : j < inclusiveEventIndex rho (Protocol.view_freeze S.E s)) :
    ProposalChainObservationsSandwichedAtIndex S rho j Next Next ∧
      NamedGenuineConfirmationsPreceqAtIndex S rho j Next ∧
      HonestActionSGCarriersPreceqAtIndex S rho j Next ∧
      HonestAttestationOutputPreceqAtIndex S rho j Next ∧
      NamedReadAnchorsAtIndex S rho j Next := by
  have hcut := support_cutoff_eq_confirmation_time_pred S.E hs
  cases hev : rho.events[j]? with
  | none =>
      refine movingEventFacts_of_no_tick_named S rho Next ?_
      intro w t htick
      rw [hev] at htick
      simp only [reduceCtorEq] at htick
  | some e =>
      cases e with
      | deliver v o t =>
          refine movingEventFacts_of_no_tick_named S rho Next ?_
          intro w t' htick
          rw [hev] at htick
          simp only [Option.some.injEq, reduceCtorEq] at htick
      | tick u t =>
          have hmem : Event.tick u t ∈ rho.events := List.mem_of_getElem? hev
          have hpub : PublicTime S t := adm.tick_public u t hmem
          have hge : Protocol.support_cutoff S.E s ≤ t := by
            have hres := Proofs.Optimistic.le_time_of_index_ge
              S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
              (by simpa only [strictEventIndex] using hlow) hev
            simpa only [Event.time] using hres
          have hle : t ≤ Protocol.view_freeze S.E s :=
            eventTime_le_of_lt_inclusive
              S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hhigh hev
          have hhonest : u ∈ rho.honest := by
            simpa only [Event.node] using adm.honest_only _ hmem
          have hgt : Protocol.proposal_time S.E s < t :=
            lt_of_lt_of_le (proposal_time_lt_support_cutoff S.E s) hge
          rcases publicTime_slotWindow_cases S hpub hgt
            (hle.trans (le_of_lt (view_freeze_lt_proposal_time_succ S.E s)))
            with ht | ht | ht | ht
          · exact absurd (ht ▸ hge)
              (not_le_of_gt (vote_time_lt_support_cutoff S.E s))
          · rw [hcut] at ht
            subst ht
            exact movingEventFacts_confirmation_at_named S hev
              (hfacts.confirmed u hhonest)
              (fun q hq => hfacts.carrier u hhonest q hq)
              (hfacts.outputs j u hhonest hev)
              (hfacts.confAnchorCompatible u hhonest)
          · subst ht
            exact movingEventFacts_viewFreeze_at_named S hev
          · exact absurd (ht ▸ hle)
              (not_le_of_gt (view_freeze_lt_proposal_time_succ S.E s))

/-- Named facts for a proposal tick. -/
private theorem movingEventFacts_proposalInstant_at_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {i : Nat} {u : V} {s : Slot}
    (hevent : rho.events[i]? = some
      (Event.tick u (Protocol.proposal_time S.E s)))
    {Before Next : Block V}
    (hproposer : S.E.proposer s = (S.node u).val_index →
      Block.Preceq Before (proposedParent S rho s) ∧
        ∃ P : NamedBlock V, proposedBlockAt S rho s = some P ∧
          Block.Preceq P.erase Next) :
    ProposalChainObservationsSandwichedAtIndex S rho i Before Next ∧
      NamedGenuineConfirmationsPreceqAtIndex S rho i Next ∧
      HonestActionSGCarriersPreceqAtIndex S rho i Next ∧
      HonestAttestationOutputPreceqAtIndex S rho i Next ∧
      NamedReadAnchorsAtIndex S rho i Next := by
  obtain ⟨hproposal, _hconfirmations, hsg, hout, _hanchors⟩ :=
    movingEventFacts_proposalInstant S adm hevent hproposer
  have htickTime : ∀ {v : V} {t : Time},
      rho.events[i]? = some (Event.tick v t) →
        t = Protocol.proposal_time S.E s := by
    intro v t hevent'
    exact (tick_node_time_eq_of_same_index hevent' hevent).2
  have hconfirmations : NamedGenuineConfirmationsPreceqAtIndex
      S rho i Next := by
    intro v _hv C hC
    obtain ⟨s', hevent', _hgen⟩ := hC
    have htime := htickTime hevent'
    exact (confirmation_time_ne_proposal_time S.E s' s htime).elim
  have hanchors : NamedReadAnchorsAtIndex S rho i Next := by
    refine { voteCompatible := ?_, confirmationCompatible := ?_ }
    · intro v s' _hv hevent'
      have htime := htickTime hevent'
      exact (vote_time_ne_proposal_time S.E s' s htime).elim
    · intro v s' _hv hevent'
      have htime := htickTime hevent'
      exact (confirmation_time_ne_proposal_time S.E s' s htime).elim
  exact ⟨hproposal, hconfirmations, hsg, hout, hanchors⟩

private theorem MovingFrontierChainStateN.succ_of_eventFacts_named
    {S : Setup V} {rho : Run V} {t1 : Time} {M0 : Height}
    {n0 i : Nat} {End : Nat → Block V}
    (h : MovingFrontierChainStateN S rho t1 M0 n0 i End)
    (Next : Block V)
    (hEndNext : Block.Preceq (End i) Next)
    (hNextRun : ∃ E : NamedBlock V, E.erase = Next ∧ RunBlock S rho E)
    (hproposal : ProposalChainObservationsSandwichedAtIndex
      S rho i (End i) Next)
    (hconfirmations : NamedGenuineConfirmationsPreceqAtIndex S rho i Next)
    (hsg : HonestActionSGCarriersPreceqAtIndex S rho i Next)
    (hout : HonestAttestationOutputPreceqAtIndex S rho i Next)
    (hanchors : NamedReadAnchorsAtIndex S rho i Next) :
    ∃ End' : Nat → Block V,
      (∀ j, j ≤ i → End' j = End j) ∧
      End' (i + 1) = Next ∧
      MovingFrontierChainStateN S rho t1 M0 n0 (i + 1) End' := by
  let End' : Nat → Block V := fun j =>
    if j = i + 1 then Next else End j
  refine ⟨End', ?_, ?_, ?_⟩
  · intro j hji
    have hjne : j ≠ i + 1 := by omega
    simp only [End', if_neg hjne]
  · simp only [End', if_pos rfl]
  · refine
      { historyStart := h.historyStart
        start_le := h.start_le.trans (Nat.le_succ i)
        endpointRun := ?_
        endpointMono := ?_
        proposalChain := ?_
        genuineConfirmations := ?_
        sgCarriers := ?_
        outputs := ?_
        anchors := ?_
        oldRows_named := by
          have hn0ne : n0 ≠ i + 1 :=
            Nat.ne_of_lt (h.start_le.trans_lt (Nat.lt_succ_self i))
          intro j a time ha hevent hemit hj hh hrow E hE hErun
          have hE' : E.erase = End n0 := by
            simpa only [End', if_neg hn0ne] using hE
          simpa only [End', if_neg hn0ne] using
            h.oldRows_named ha hevent hemit hj hh hrow E hE' hErun
        frontierFloor := h.frontierFloor
        boundaryTargets := by
          have hn0ne : n0 ≠ i + 1 := by
            have hn0le : n0 ≤ i := h.start_le
            omega
          simpa only [End', if_neg hn0ne] using h.boundaryTargets }
    · intro j hj hjupper
      by_cases hji : j = i + 1
      · subst j
        simpa only [End', if_pos rfl] using hNextRun
      · have hjold : j ≤ i := by omega
        simpa only [End', if_neg hji] using h.endpointRun j hj hjold
    · intro j hj hjupper
      by_cases hji : j = i
      · subst j
        have hine : i ≠ i + 1 := by omega
        simp only [End', if_neg hine, if_pos rfl]
        exact hEndNext
      · have hjold : j < i := by omega
        have hjne : j ≠ i + 1 := by omega
        have hjsne : j + 1 ≠ i + 1 := by omega
        simpa only [End', if_neg hjne, if_neg hjsne] using
          h.endpointMono j hj hjold
    · intro j hj hjupper
      by_cases hji : j = i
      · subst j
        have hine : i ≠ i + 1 := by omega
        simpa only [End', if_neg hine, if_pos rfl] using hproposal
      · have hjold : j < i := by omega
        have hjne : j ≠ i + 1 := by omega
        have hjsne : j + 1 ≠ i + 1 := by omega
        simpa only [End', if_neg hjne, if_neg hjsne] using
          h.proposalChain j hj hjold
    · intro j hj hjupper
      by_cases hji : j = i
      · subst j
        simpa only [End', if_pos rfl] using hconfirmations
      · have hjold : j < i := by omega
        have hjsne : j + 1 ≠ i + 1 := by omega
        simpa only [End', if_neg hjsne] using
          h.genuineConfirmations j hj hjold
    · intro j hj hjupper
      by_cases hji : j = i
      · subst j
        simpa only [End', if_pos rfl] using hsg
      · have hjold : j < i := by omega
        have hjsne : j + 1 ≠ i + 1 := by omega
        simpa only [End', if_neg hjsne] using h.sgCarriers j hj hjold
    · intro j hj hjupper
      by_cases hji : j = i
      · subst j
        simpa only [End', if_pos rfl] using hout
      · have hjold : j < i := by omega
        have hjsne : j + 1 ≠ i + 1 := by omega
        simpa only [End', if_neg hjsne] using h.outputs j hj hjold
    · intro j hj hjupper
      by_cases hji : j = i
      · subst j
        simpa only [End', if_pos rfl] using hanchors
      · have hjold : j < i := by omega
        have hjsne : j + 1 ≠ i + 1 := by omega
        simpa only [End', if_neg hjsne] using h.anchors j hj hjold

private theorem MovingFrontierChainStateN.through_constantEndpoint_named
    (S : Setup V) {rho : Run V}
    {t1 : Time} {M0 : Height} {n0 c : Nat} {End : Nat → Block V}
    (h : MovingFrontierChainStateN S rho t1 M0 n0 c End)
    {Next : Block V}
    (hle : Block.Preceq (End c) Next)
    (hrun : ∃ E : NamedBlock V, E.erase = Next ∧ RunBlock S rho E)
    {m : Nat} (hcm : c ≤ m)
    (hfacts : ∀ j, c ≤ j → j < m →
      ProposalChainObservationsSandwichedAtIndex S rho j Next Next ∧
        NamedGenuineConfirmationsPreceqAtIndex S rho j Next ∧
        HonestActionSGCarriersPreceqAtIndex S rho j Next ∧
        HonestAttestationOutputPreceqAtIndex S rho j Next ∧
        NamedReadAnchorsAtIndex S rho j Next) :
    ∃ End' : Nat → Block V,
      (∀ j, j ≤ c → End' j = End j) ∧
      (∀ j, c < j → End' j = Next) ∧
      MovingFrontierChainStateN S rho t1 M0 n0 m End' := by
  classical
  let End' : Nat → Block V := fun j => if j ≤ c then End j else Next
  have hlow : ∀ j, j ≤ c → End' j = End j := by
    intro j hj
    simp only [End', if_pos hj]
  have hhigh : ∀ j, c < j → End' j = Next := by
    intro j hj
    simp only [End', if_neg (Nat.not_le_of_gt hj)]
  refine ⟨End', hlow, hhigh, ?_⟩
  refine
    { historyStart := h.historyStart
      start_le := h.start_le.trans hcm
      endpointRun := ?_
      endpointMono := ?_
      proposalChain := ?_
      genuineConfirmations := ?_
      sgCarriers := ?_
      outputs := ?_
      anchors := ?_
      oldRows_named := by
        rw [hlow n0 h.start_le]
        exact h.oldRows_named
      frontierFloor := h.frontierFloor
      boundaryTargets := by
        rw [hlow n0 h.start_le]
        exact h.boundaryTargets }
  · intro j hj _
    by_cases hjc : j ≤ c
    · rw [hlow j hjc]
      exact h.endpointRun j hj hjc
    · rw [hhigh j (Nat.lt_of_not_ge hjc)]
      exact hrun
  · intro j hj _
    by_cases hjc : j < c
    · rw [hlow j (Nat.le_of_lt hjc), hlow (j + 1) (Nat.succ_le_of_lt hjc)]
      exact h.endpointMono j hj hjc
    · by_cases hjeq : j = c
      · subst hjeq
        rw [hlow j (Nat.le_refl j), hhigh (j + 1) (Nat.lt_succ_self j)]
        exact hle
      · have hcj : c < j := by omega
        rw [hhigh j hcj, hhigh (j + 1) (hcj.trans (Nat.lt_succ_self j))]
        exact Block.preceq_self _
  · intro j hj hjm
    by_cases hjc : j < c
    · rw [hlow j (Nat.le_of_lt hjc), hlow (j + 1) (Nat.succ_le_of_lt hjc)]
      exact h.proposalChain j hj hjc
    · have hcj : c ≤ j := Nat.le_of_not_gt hjc
      rw [hhigh (j + 1) (Nat.lt_succ_of_le hcj)]
      by_cases hjeq : j = c
      · subst hjeq
        rw [hlow j (Nat.le_refl j)]
        exact proposalChainObservationsSandwichedAtIndex_mono_left
          (hfacts j hcj hjm).1 hle
      · rw [hhigh j (by omega)]
        exact (hfacts j hcj hjm).1
  · intro j hj hjm
    by_cases hjc : j < c
    · rw [hlow (j + 1) (Nat.succ_le_of_lt hjc)]
      exact h.genuineConfirmations j hj hjc
    · have hcj : c ≤ j := Nat.le_of_not_gt hjc
      rw [hhigh (j + 1) (Nat.lt_succ_of_le hcj)]
      exact (hfacts j hcj hjm).2.1
  · intro j hj hjm
    by_cases hjc : j < c
    · rw [hlow (j + 1) (Nat.succ_le_of_lt hjc)]
      exact h.sgCarriers j hj hjc
    · have hcj : c ≤ j := Nat.le_of_not_gt hjc
      rw [hhigh (j + 1) (Nat.lt_succ_of_le hcj)]
      exact (hfacts j hcj hjm).2.2.1
  · intro j hj hjm
    by_cases hjc : j < c
    · rw [hlow (j + 1) (Nat.succ_le_of_lt hjc)]
      exact h.outputs j hj hjc
    · have hcj : c ≤ j := Nat.le_of_not_gt hjc
      rw [hhigh (j + 1) (Nat.lt_succ_of_le hcj)]
      exact (hfacts j hcj hjm).2.2.2.1
  · intro j hj hjm
    by_cases hjc : j < c
    · rw [hlow (j + 1) (Nat.succ_le_of_lt hjc)]
      exact h.anchors j hj hjc
    · have hcj : c ≤ j := Nat.le_of_not_gt hjc
      rw [hhigh (j + 1) (Nat.lt_succ_of_le hcj)]
      exact (hfacts j hcj hjm).2.2.2.2

/-- Public wrapper for the named constant-endpoint extension used by the N
entry producers. -/
theorem MovingFrontierChainStateN.through_constantEndpoint_named_public
    (S : Setup V) {rho : Run V}
    {t1 : Time} {M0 : Height} {n0 c : Nat} {End : Nat → Block V}
    (h : MovingFrontierChainStateN S rho t1 M0 n0 c End)
    {Next : Block V}
    (hle : Block.Preceq (End c) Next)
    (hrun : ∃ E : NamedBlock V, E.erase = Next ∧ RunBlock S rho E)
    {m : Nat} (hcm : c ≤ m)
    (hfacts : ∀ j, c ≤ j → j < m →
      ProposalChainObservationsSandwichedAtIndex S rho j Next Next ∧
        NamedGenuineConfirmationsPreceqAtIndex S rho j Next ∧
        HonestActionSGCarriersPreceqAtIndex S rho j Next ∧
        HonestAttestationOutputPreceqAtIndex S rho j Next ∧
        NamedReadAnchorsAtIndex S rho j Next) :
    ∃ End' : Nat → Block V,
      (∀ j, j ≤ c → End' j = End j) ∧
      (∀ j, c < j → End' j = Next) ∧
      MovingFrontierChainStateN S rho t1 M0 n0 m End' := by
  exact MovingFrontierChainStateN.through_constantEndpoint_named
    S h hle hrun hcm hfacts

#print axioms MovingFrontierChainStateN.through_constantEndpoint_named_public

private theorem MovingFrontierChainStateN.succ_proposalInstant_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {t1 : Time} {M0 : Height} {n0 i : Nat} {End : Nat → Block V}
    (h : MovingFrontierChainStateN S rho t1 M0 n0 i End)
    {u : V} {s : Slot}
    (hevent : rho.events[i]? = some
      (Event.tick u (Protocol.proposal_time S.E s)))
    {Next : Block V}
    (hEndNext : Block.Preceq (End i) Next)
    (hNextRun : ∃ E : NamedBlock V, E.erase = Next ∧ RunBlock S rho E)
    (hproposer : S.E.proposer s = (S.node u).val_index →
      Block.Preceq (End i) (proposedParent S rho s) ∧
        ∃ P : NamedBlock V, proposedBlockAt S rho s = some P ∧
          Block.Preceq P.erase Next) :
    ∃ End' : Nat → Block V,
      (∀ j, j ≤ i → End' j = End j) ∧
      End' (i + 1) = Next ∧
      MovingFrontierChainStateN S rho t1 M0 n0 (i + 1) End' := by
  obtain ⟨hproposal, hconfirmations, hsg, hout, hanchors⟩ :=
    movingEventFacts_proposalInstant_at_named S adm hevent hproposer
  exact h.succ_of_eventFacts_named Next hEndNext hNextRun
    hproposal hconfirmations hsg hout hanchors



omit [DecidableEq V] [Fintype V] in
/-- The inclusive cursor of an earlier instant is at most the strict cursor of
a later one. -/
private theorem inclusive_le_strict_of_lt
    (rho : Run V) {t0 t1 : Time} (hlt : t0 < t1) :
    inclusiveEventIndex rho t0 ≤ strictEventIndex rho t1 := by
  unfold inclusiveEventIndex strictEventIndex
  exact (List.monotone_filter_right rho.events (fun e he => by
    simp only [decide_eq_true_eq] at he ⊢
    exact lt_of_le_of_lt he hlt)).length_le

/-- A tick inside a closed time window separates the strict cursor of its left
end from the inclusive cursor of its right end. -/
private theorem strict_lt_inclusive_of_tick_mem
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    {v : V} {t t0 t1 : Time}
    (htick : Event.tick v t ∈ rho.events)
    (hlow : t0 ≤ t) (hhigh : t ≤ t1) :
    strictEventIndex rho t0 < inclusiveEventIndex rho t1 := by
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp htick
  have hleft : strictEventIndex rho t0 ≤ i := by
    by_contra hnot
    have htrue := Proofs.Optimistic.filter_true_of_index_lt S sch _
      (Proofs.Optimistic.downward_lt t0)
      (by simpa only [strictEventIndex] using Nat.lt_of_not_ge hnot) hi
    simp only [decide_eq_true_eq, Event.time] at htrue
    exact absurd htrue (not_lt_of_ge hlow)
  have hright : i < inclusiveEventIndex rho t1 := by
    by_contra hnot
    have hgt := eventTime_gt_of_inclusive_le S sch
      (Nat.le_of_not_gt hnot) hi
    simp only [Event.time] at hgt
    exact absurd hhigh (not_le_of_gt hgt)
  exact hleft.trans_lt hright

/-- The confirmation instant of the slot-`s` window is strictly before the
inclusive view-freeze cursor. -/
theorem strictSupportCutoff_lt_inclusiveViewFreeze
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {s : Slot} {v : V} (hv : v ∈ rho.honest)
    (hhor : Protocol.support_cutoff S.E s ≤ rho.horizon) :
    strictEventIndex rho (Protocol.support_cutoff S.E s) <
      inclusiveEventIndex rho (Protocol.view_freeze S.E s) := by
  have htick : Event.tick v (Protocol.support_cutoff S.E s) ∈ rho.events :=
    adm.tick_total v hv (Protocol.support_cutoff S.E s)
      (Protocol.publicTime_support_cutoff S s)
      (le_of_lt (lt_of_le_of_lt (Proofs.Optimistic.vote_time_nonneg S.E s)
        (vote_time_lt_support_cutoff S.E s))) hhor
  exact strict_lt_inclusive_of_tick_mem S
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed htick
    (le_refl _) (support_cutoff_le_view_freeze S.E s)

/-- Cross a named moving chain across the prefix of one slot window. -/
theorem through_slotWindowPrefix_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {t1 : Time} {M0 : Height} {n0 : Nat} {End : Nat → Block V}
    {s : Slot} (hs : 0 < s)
    (h : MovingFrontierChainStateN S rho t1 M0 n0
      (inclusiveEventIndex rho (Protocol.proposal_time S.E s)) End)
    {EndB Next : Block V}
    (hEndB : End (inclusiveEventIndex rho (Protocol.proposal_time S.E s))
      = EndB)
    (hrunE : ∃ E : NamedBlock V, E.erase = EndB ∧ RunBlock S rho E)
    (hrunN : ∃ E : NamedBlock V, E.erase = Next ∧ RunBlock S rho E)
    (hfacts : NamedMovingSlotWindowFacts S rho s EndB Next)
    {v : V} (hv : v ∈ rho.honest)
    (hhor : Protocol.support_cutoff S.E s ≤ rho.horizon) :
    ∃ End' : Nat → Block V,
      (∀ j, j ≤ inclusiveEventIndex rho (Protocol.proposal_time S.E s) →
        End' j = End j) ∧
      End' (inclusiveEventIndex rho (Protocol.view_freeze S.E s)) = Next ∧
      MovingFrontierChainStateN S rho t1 M0 n0
        (inclusiveEventIndex rho (Protocol.view_freeze S.E s)) End' := by
  set cs := inclusiveEventIndex rho (Protocol.proposal_time S.E s) with hcs
  set cd := strictEventIndex rho (Protocol.support_cutoff S.E s) with hcd
  set cf := inclusiveEventIndex rho (Protocol.view_freeze S.E s) with hcf
  have hcscd : cs ≤ cd :=
    inclusive_le_strict_of_lt rho (proposal_time_lt_support_cutoff S.E s)
  have hcdcf : cd < cf :=
    strictSupportCutoff_lt_inclusiveViewFreeze S adm hv hhor
  obtain ⟨End1, hlow1, hhigh1, hstate1⟩ :=
    h.through_constantEndpoint_named S
      (by rw [hEndB]; exact Block.preceq_self _)
      hrunE hcscd (by
      intro j hj hjm
      exact movingEventFacts_vote_named S adm hfacts hj hjm)
  have hEnd1cd : End1 cd = EndB := by
    by_cases hlt : cs < cd
    · exact hhigh1 cd hlt
    · have hEq : cd = cs := Nat.le_antisymm (Nat.le_of_not_gt hlt) hcscd
      rw [hEq, hlow1 cs (Nat.le_refl cs), hEndB]
  obtain ⟨End2, hlow2, hhigh2, hstate2⟩ :=
    hstate1.through_constantEndpoint_named S
      (by rw [hEnd1cd]; exact hfacts.endLe)
      hrunN (Nat.le_of_lt hcdcf) (by
      intro j hj hjm
      exact movingEventFacts_confirmation_named S adm hs hfacts hj hjm)
  refine ⟨End2, ?_, hhigh2 cf hcdcf, hstate2⟩
  intro j hj
  rw [hlow2 j (hj.trans hcscd), hlow1 j hj]


/-! ## The proposal tail of a slot window -/

omit [DecidableEq V] [Fintype V] in
/-- An event index is determined by its event. -/
private theorem eventIndex_unique
    {rho : Run V} (hnodup : rho.events.Nodup) {i j : Nat} {e : Event V}
    (hi : rho.events[i]? = some e) (hj : rho.events[j]? = some e) :
    i = j := by
  obtain ⟨hiLen, hie⟩ := List.getElem?_eq_some_iff.mp hi
  obtain ⟨hjLen, hje⟩ := List.getElem?_eq_some_iff.mp hj
  have hfin : (⟨i, hiLen⟩ : Fin rho.events.length) = ⟨j, hjLen⟩ :=
    (List.nodup_iff_injective_getElem.mp hnodup) (by simp only [hie, hje])
  simpa using congrArg Fin.val hfin






private theorem movingSlotWindowTail_eventFacts_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {s : Slot} {Before Next : Block V}
    (hBN : Block.Preceq Before Next)
    {j : Nat}
    (hproposer : ∀ u : V, u ∈ rho.honest →
      rho.events[j]? = some
          (Event.tick u (Protocol.proposal_time S.E (s + 1))) →
      S.E.proposer (s + 1) = (S.node u).val_index →
        Block.Preceq Before (proposedParent S rho (s + 1)) ∧
          ∃ P : NamedBlock V, proposedBlockAt S rho (s + 1) = some P ∧
            Block.Preceq P.erase Next)
    (hlow : inclusiveEventIndex rho (Protocol.view_freeze S.E s) ≤ j)
    (hhigh : j <
      inclusiveEventIndex rho (Protocol.proposal_time S.E (s + 1))) :
    ProposalChainObservationsSandwichedAtIndex S rho j Before Next ∧
      NamedGenuineConfirmationsPreceqAtIndex S rho j Next ∧
      HonestActionSGCarriersPreceqAtIndex S rho j Next ∧
      HonestAttestationOutputPreceqAtIndex S rho j Next ∧
      NamedReadAnchorsAtIndex S rho j Next := by
  have hweaken : ∀ h :
      ProposalChainObservationsSandwichedAtIndex S rho j Next Next ∧
        NamedGenuineConfirmationsPreceqAtIndex S rho j Next ∧
        HonestActionSGCarriersPreceqAtIndex S rho j Next ∧
        HonestAttestationOutputPreceqAtIndex S rho j Next ∧
        NamedReadAnchorsAtIndex S rho j Next,
      ProposalChainObservationsSandwichedAtIndex S rho j Before Next ∧
        NamedGenuineConfirmationsPreceqAtIndex S rho j Next ∧
        HonestActionSGCarriersPreceqAtIndex S rho j Next ∧
        HonestAttestationOutputPreceqAtIndex S rho j Next ∧
        NamedReadAnchorsAtIndex S rho j Next := by
    rintro ⟨hp, hrest⟩
    exact ⟨proposalChainObservationsSandwichedAtIndex_mono_left hp hBN, hrest⟩
  cases hev : rho.events[j]? with
  | none =>
      refine hweaken (movingEventFacts_of_no_tick_named S rho Next ?_)
      intro w t htick
      rw [hev] at htick
      simp only [reduceCtorEq] at htick
  | some e =>
      cases e with
      | deliver v o t =>
          refine hweaken (movingEventFacts_of_no_tick_named S rho Next ?_)
          intro w t' htick
          rw [hev] at htick
          simp only [Option.some.injEq, reduceCtorEq] at htick
      | tick u t =>
          have hmem : Event.tick u t ∈ rho.events :=
            List.mem_of_getElem? hev
          have hpub : PublicTime S t := adm.tick_public u t hmem
          have hgt : Protocol.view_freeze S.E s < t :=
            eventTime_gt_of_inclusive_le S
              adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hlow hev
          have hle : t ≤ Protocol.proposal_time S.E (s + 1) :=
            eventTime_le_of_lt_inclusive S
              adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hhigh hev
          have hhonest : u ∈ rho.honest := by
            simpa only [Event.node] using adm.honest_only _ hmem
          have hgtProposal : Protocol.proposal_time S.E s < t :=
            lt_of_le_of_lt (proposal_time_le_view_freeze S.E s) hgt
          rcases publicTime_slotWindow_cases S hpub hgtProposal hle
            with ht | ht | ht | ht
          · exact absurd (ht ▸ hgt)
              (not_lt_of_ge (vote_time_le_view_freeze S.E s))
          · exact absurd (ht ▸ hgt)
              (not_lt_of_ge (support_cutoff_le_view_freeze S.E s))
          · exact absurd (ht ▸ hgt) (lt_irrefl _)
          · subst ht
            exact movingEventFacts_proposalInstant_at_named S adm hev
              (hproposer u hhonest hev)

/-- Public wrapper for the named tail event-facts producer used by the N
history producer. -/
theorem movingSlotWindowTail_eventFacts_named_public
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {s : Slot} {Before Next : Block V}
    (hBN : Block.Preceq Before Next)
    {j : Nat}
    (hproposer : ∀ u : V, u ∈ rho.honest →
      rho.events[j]? = some
          (Event.tick u (Protocol.proposal_time S.E (s + 1))) →
      S.E.proposer (s + 1) = (S.node u).val_index →
        Block.Preceq Before (proposedParent S rho (s + 1)) ∧
          ∃ P : NamedBlock V, proposedBlockAt S rho (s + 1) = some P ∧
            Block.Preceq P.erase Next)
    (hlow : inclusiveEventIndex rho (Protocol.view_freeze S.E s) ≤ j)
    (hhigh : j <
      inclusiveEventIndex rho (Protocol.proposal_time S.E (s + 1))) :
    ProposalChainObservationsSandwichedAtIndex S rho j Before Next ∧
      NamedGenuineConfirmationsPreceqAtIndex S rho j Next ∧
      HonestActionSGCarriersPreceqAtIndex S rho j Next ∧
      HonestAttestationOutputPreceqAtIndex S rho j Next ∧
      NamedReadAnchorsAtIndex S rho j Next := by
  exact movingSlotWindowTail_eventFacts_named S adm hBN hproposer hlow hhigh

#print axioms movingSlotWindowTail_eventFacts_named_public

/-! ## The slot step -/



theorem MovingFrontierChainStateN.through_slotWindow_byzantineProposer_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {t1 : Time} {M0 : Height} {n0 : Nat} {End : Nat → Block V}
    {s : Slot} (hs : 0 < s)
    (h : MovingFrontierChainStateN S rho t1 M0 n0
      (inclusiveEventIndex rho (Protocol.proposal_time S.E s)) End)
    {EndB Next : Block V}
    (hEndB : End (inclusiveEventIndex rho (Protocol.proposal_time S.E s))
      = EndB)
    (hrunE : ∃ E : NamedBlock V, E.erase = EndB ∧ RunBlock S rho E)
    (hrunN : ∃ E : NamedBlock V, E.erase = Next ∧ RunBlock S rho E)
    (hfacts : NamedMovingSlotWindowFacts S rho s EndB Next)
    (hbyz : S.E.proposer (s + 1) ∉ rho.honest)
    {v : V} (hv : v ∈ rho.honest)
    (hhorSC : Protocol.support_cutoff S.E s ≤ rho.horizon) :
    ∃ End' : Nat → Block V,
      (∀ j, j ≤ inclusiveEventIndex rho (Protocol.proposal_time S.E s) →
        End' j = End j) ∧
      (∀ j, inclusiveEventIndex rho (Protocol.view_freeze S.E s) ≤ j →
        End' j = Next) ∧
      MovingFrontierChainStateN S rho t1 M0 n0
        (inclusiveEventIndex rho (Protocol.proposal_time S.E (s + 1)))
        End' := by
  obtain ⟨End1, hlow1, hval1, hstate1⟩ :=
    through_slotWindowPrefix_named S adm hs h hEndB hrunE hrunN hfacts hv hhorSC
  have hproposer : ∀ (j : Nat) (u : V), u ∈ rho.honest →
      rho.events[j]? = some
          (Event.tick u (Protocol.proposal_time S.E (s + 1))) →
      S.E.proposer (s + 1) = (S.node u).val_index →
        Block.Preceq Next (proposedParent S rho (s + 1)) ∧
          ∃ P : NamedBlock V, proposedBlockAt S rho (s + 1) = some P ∧
            Block.Preceq P.erase Next := by
    intro _j u hu _hev heq
    rw [S.node_val_index u] at heq
    exact absurd (heq ▸ hu) hbyz
  obtain ⟨End2, hlow2, hhigh2, hstate2⟩ :=
    hstate1.through_constantEndpoint_named S
      (by rw [hval1]; exact Block.preceq_self _) hrunN
      (inclusiveEventIndex_mono rho
        (le_of_lt (view_freeze_lt_proposal_time_succ S.E s))) (by
      intro j hj hjm
      exact movingSlotWindowTail_eventFacts_named S adm (Block.preceq_self Next)
        (hproposer j) hj hjm)
  refine ⟨End2, ?_, ?_, hstate2⟩
  · intro j hj
    rw [hlow2 j (hj.trans (inclusive_le_strict_of_lt rho
      (proposal_time_lt_support_cutoff S.E s) |>.trans
        (Nat.le_of_lt (strictSupportCutoff_lt_inclusiveViewFreeze
          S adm hv hhorSC)))), hlow1 j hj]
  · intro j hj
    rcases Nat.eq_or_lt_of_le hj with heq | hlt
    · rw [← heq, hlow2 _ (Nat.le_refl _), hval1]
    · exact hhigh2 j hlt

theorem MovingFrontierChainStateN.through_slotWindow_honestProposer_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {t1 : Time} {M0 : Height} {n0 : Nat} {End : Nat → Block V}
    {s : Slot} (hs : 0 < s)
    (h : MovingFrontierChainStateN S rho t1 M0 n0
      (inclusiveEventIndex rho (Protocol.proposal_time S.E s)) End)
    {EndB Next : Block V}
    (hEndB : End (inclusiveEventIndex rho (Protocol.proposal_time S.E s))
      = EndB)
    (hrunE : ∃ E : NamedBlock V, E.erase = EndB ∧ RunBlock S rho E)
    (hrunN : ∃ E : NamedBlock V, E.erase = Next ∧ RunBlock S rho E)
    (hfacts : NamedMovingSlotWindowFacts S rho s EndB Next)
    (hprop : S.E.proposer (s + 1) ∈ rho.honest)
    (hhor : Protocol.proposal_time S.E (s + 1) ≤ rho.horizon)
    (hparent : Block.Preceq Next (proposedParent S rho (s + 1)))
    {v : V} (hv : v ∈ rho.honest)
    (hhorSC : Protocol.support_cutoff S.E s ≤ rho.horizon) :
    ∃ P : NamedBlock V, proposedBlockAt S rho (s + 1) = some P ∧
      ∃ End' : Nat → Block V,
        (∀ j, j ≤ inclusiveEventIndex rho (Protocol.proposal_time S.E s) →
          End' j = End j) ∧
        End' (strictEventIndex rho (Protocol.proposal_time S.E (s + 1))) =
          Next ∧
        End' (inclusiveEventIndex rho (Protocol.proposal_time S.E (s + 1))) =
          P.erase ∧
        MovingFrontierChainStateN S rho t1 M0 n0
          (inclusiveEventIndex rho (Protocol.proposal_time S.E (s + 1)))
          End' := by
  classical
  obtain ⟨P, hP⟩ := proposedBlockAt_isSome S rho (s + 1)
  set cf := inclusiveEventIndex rho (Protocol.view_freeze S.E s) with hcf
  set cn := inclusiveEventIndex rho (Protocol.proposal_time S.E (s + 1))
    with hcn
  set sn := strictEventIndex rho (Protocol.proposal_time S.E (s + 1))
    with hsn
  have hPrun : RunBlock S rho P :=
    proposedBlockAt_blockInRun_of_admissible S adm.toNamedAdmissibleCore
      (s + 1) (Nat.succ_pos s) hprop hhor hP
  have hNextP : Block.Preceq Next P.erase :=
    Block.preceq_trans hparent
      (proposedParent_preceq_proposedBlockAt S rho (s + 1) hP)
  obtain ⟨End1, hlow1, hval1, hstate1⟩ :=
    through_slotWindowPrefix_named S adm hs h hEndB hrunE hrunN hfacts hv hhorSC
  have hpemit : NamedRun.emits S rho (S.E.proposer (s + 1))
      (.block P) (Protocol.proposal_time S.E (s + 1)) :=
    (Proofs.Optimistic.proposalTick S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed (s + 1)
      (Nat.succ_pos s) hprop hhor hP).2
  obtain ⟨p, hpevent, _hpblock⟩ := hpemit
  have hcfsn : cf ≤ sn :=
    inclusive_le_strict_of_lt rho (view_freeze_lt_proposal_time_succ S.E s)
  have hsnp : sn ≤ p := by
    by_contra hnot
    have htrue := Proofs.Optimistic.filter_true_of_index_lt S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed _
      (Proofs.Optimistic.downward_lt (Protocol.proposal_time S.E (s + 1)))
      (by simpa only [strictEventIndex] using Nat.lt_of_not_ge hnot) hpevent
    simp only [decide_eq_true_eq, Event.time] at htrue
    exact lt_irrefl _ htrue
  have hcfp : cf ≤ p := hcfsn.trans hsnp
  have hpcn : p < cn := by
    by_contra hnot
    have hgt := eventTime_gt_of_inclusive_le S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
      (Nat.le_of_not_gt hnot) hpevent
    simp only [Event.time] at hgt
    exact lt_irrefl _ hgt
  have hpUnique : ∀ (j : Nat) (u : V), u ∈ rho.honest →
      rho.events[j]? = some
          (Event.tick u (Protocol.proposal_time S.E (s + 1))) →
      S.E.proposer (s + 1) = (S.node u).val_index → j = p := by
    intro j u _hu hev heq
    rw [S.node_val_index u] at heq
    subst heq
    exact eventIndex_unique adm.nodup hev hpevent
  obtain ⟨End2, hlow2, hhigh2, hstate2⟩ :=
    hstate1.through_constantEndpoint_named S
      (by rw [hval1]; exact Block.preceq_self _) hrunN hcfp (by
      intro j hj hjp
      refine movingSlotWindowTail_eventFacts_named S adm
        (Block.preceq_self Next) ?_ hj (hjp.trans hpcn)
      intro u hu hev heq
      exact absurd (hpUnique j u hu hev heq) (Nat.ne_of_lt hjp))
  have hEnd2p : End2 p = Next := by
    rcases Nat.eq_or_lt_of_le hcfp with heq | hlt
    · rw [← heq, hlow2 _ (Nat.le_refl _), hval1]
    · exact hhigh2 p hlt
  obtain ⟨End3, hlow3, hval3, hstate3⟩ :=
    hstate2.succ_proposalInstant_named S adm hpevent
      (by rw [hEnd2p]; exact hNextP) ⟨P, rfl, hPrun⟩ (fun _ =>
        ⟨by rw [hEnd2p]; exact hparent, P, hP,
          Block.preceq_self _⟩)
  obtain ⟨End4, hlow4, hhigh4, hstate4⟩ :=
    hstate3.through_constantEndpoint_named S
      (by rw [hval3]; exact Block.preceq_self _) ⟨P, rfl, hPrun⟩
      (Nat.succ_le_of_lt hpcn) (by
      intro j hj hjn
      refine movingSlotWindowTail_eventFacts_named S adm
        (Block.preceq_self P.erase) ?_ (hcfp.trans (Nat.le_of_succ_le hj)) hjn
      intro u hu hev heq
      exact absurd (hpUnique j u hu hev heq) (by omega))
  refine ⟨P, hP, End4, ?_, ?_, ?_, hstate4⟩
  · intro j hj
    have hjcf : j ≤ cf :=
      hj.trans ((inclusive_le_strict_of_lt rho
        (proposal_time_lt_support_cutoff S.E s)).trans
        (Nat.le_of_lt (strictSupportCutoff_lt_inclusiveViewFreeze
          S adm hv hhorSC)))
    rw [hlow4 j (hjcf.trans (Nat.le_succ_of_le hcfp)),
      hlow3 j (hjcf.trans hcfp), hlow2 j hjcf, hlow1 j hj]
  · rw [hlow4 sn (hsnp.trans (Nat.le_succ p)), hlow3 sn hsnp]
    rcases Nat.eq_or_lt_of_le hcfsn with heq | hlt
    · rw [← heq, hlow2 _ (Nat.le_refl _), hval1]
    · exact hhigh2 sn hlt
  · by_cases hcase : p + 1 < cn
    · rw [hhigh4 cn hcase]
    · have hcneq : cn = p + 1 := by omega
      rw [hcneq, hlow4 (p + 1) (Nat.le_refl _), hval3]

/-! ## The slot step at the entry-state level -/

private theorem proposal_time_lt_succ (E : Env V) (s : Slot) :
    Protocol.proposal_time E s < Protocol.proposal_time E (s + 1) :=
  lt_of_le_of_lt (proposal_time_le_view_freeze E s)
    (view_freeze_lt_proposal_time_succ E s)



/-- A named transferred proposal walk identifies the prepared vote-duty head
with the erased named proposal. -/
theorem voteDutyHead_eq_proposedBlock_of_transferred
    (S : Setup V) {rho : Run V} {s : Slot} {v : V}
    {tree₀ : Finset (Block V)} {P : NamedBlock V}
    (hP : proposedBlockAt S rho s = some P)
    (h : Proofs.Optimistic.NamedVoteStoreExtends S rho v s tree₀
      (proposedParent S rho s) P) :
    voteDutyHead S rho v s = P.erase := by
  change Internal.voterHeadAt S rho v s = P.erase
  exact Protocol.voterHeadAt_eq_proposedBlockAt_of_namedVoteStoreExtends
    S hP h

#print axioms voteDutyHead_eq_proposedBlock_of_transferred







/-! The read-time activity proof needs the global one-unit endpoint floor. The
old theorem has an erased `derived_state` conclusion, so this private named
version keeps the endpoint witness throughout. -/

/-! The selected FG root at a read is below a named endpoint at the cursor. -/






/-- The named honest-proposer step for the N moving-chain entry. -/
theorem MovingSlotEntryStateN.step_honestProposer_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {t1 : Time} {M0 : Height} {s : Slot} {Prev End : Block V}
    (hs : 0 < s)
    (hentry : MovingSlotEntryStateN S rho t1 M0 s Prev End)
    {Next : Block V}
    (hrun : ∃ E : NamedBlock V, E.erase = Next ∧ RunBlock S rho E)
    (hfacts : NamedMovingSlotWindowFacts S rho s End Next)
    (hprop : S.E.proposer (s + 1) ∈ rho.honest)
    (hhor : Protocol.proposal_time S.E (s + 1) ≤ rho.horizon)
    (hhorSC : Protocol.support_cutoff S.E s ≤ rho.horizon)
    (hparent : Block.Preceq Next (proposedParent S rho (s + 1)))
    {v : V} (hv : v ∈ rho.honest)
    {P : NamedBlock V} (hP : proposedBlockAt S rho (s + 1) = some P)
    (hprevVotes : NamedHonestVotesCone S rho s
      (fun X => Block.Preceq Next X))
    (hvotes : NamedHonestVotesCone S rho (s + 1)
      (fun X => Block.Preceq P.erase X))
    (hheadEq : ∀ w ∈ rho.honest, ∃ tree₀ : Finset (Block V),
      Proofs.Optimistic.NamedVoteStoreExtends S rho w (s + 1) tree₀
        (proposedParent S rho (s + 1)) P)
    (hconf : ∀ w ∈ rho.honest, ∀ D : Block V,
      GenuineConfirmationWith
        (NamedProfile.gradeContract
          (confirmationInputRead S rho w s).cache)
        S.E S.hc (Proofs.Optimistic.confStore S rho w s) s D →
        Block.compatible D P.erase = true) :
    MovingSlotEntryStateN S rho t1 M0 (s + 1) Next P.erase := by
  obtain ⟨EndAt, hhistory, _hprev, hEndAt⟩ := hentry.prevEndpoint
  have hrunE : ∃ E : NamedBlock V, E.erase = End ∧ RunBlock S rho E := by
    rw [← hEndAt]
    exact hhistory.endpointRun _ hhistory.start_le (Nat.le_refl _)
  obtain ⟨P0, hP0, End', hlow', hstrict', hval', hstate'⟩ :=
    hhistory.through_slotWindow_honestProposer_named S adm hs hEndAt hrunE
      hrun hfacts hprop hhor hparent hv hhorSC
  have hP0eq : P0 = P := proposedBlockAt_unique S rho (s + 1) hP0 hP
  subst P0
  exact
    { startTime := hentry.startTime.trans
        (le_of_lt (proposal_time_lt_succ S.E s))
      prevEndpoint := ⟨End', hstate', hstrict', hval'⟩
      prevVotes := by simpa only [Nat.add_sub_cancel] using hprevVotes
      votes := hvotes
      headEq := fun _ w hw => by
        obtain ⟨tree₀, hstore⟩ := hheadEq w hw
        exact voteDutyHead_eq_proposedBlock_of_transferred S hP hstore
      confCompatible := by simpa only [Nat.add_sub_cancel] using hconf }

#print axioms MovingSlotEntryStateN.step_honestProposer_named

/-- The named Byzantine-proposer step for the N moving-chain entry. -/
theorem MovingSlotEntryStateN.step_byzantineProposer_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {t1 : Time} {M0 : Height} {s : Slot} {Prev End : Block V}
    (hs : 0 < s)
    (hentry : MovingSlotEntryStateN S rho t1 M0 s Prev End)
    {Next : Block V}
    (hrun : ∃ E : NamedBlock V, E.erase = Next ∧ RunBlock S rho E)
    (hfacts : NamedMovingSlotWindowFacts S rho s End Next)
    (hbyz : S.E.proposer (s + 1) ∉ rho.honest)
    {v : V} (hv : v ∈ rho.honest)
    (hhorSC : Protocol.support_cutoff S.E s ≤ rho.horizon)
    (hprevVotes : NamedHonestVotesCone S rho s
      (fun X => Block.Preceq Next X))
    (hvotes : NamedHonestVotesCone S rho (s + 1)
      (fun X => Block.Preceq Next X))
    (hconf : ∀ w ∈ rho.honest, ∀ D : Block V,
      GenuineConfirmationWith
        (NamedProfile.gradeContract
          (confirmationInputRead S rho w s).cache)
        S.E S.hc (Proofs.Optimistic.confStore S rho w s) s D →
        Block.compatible D Next = true) :
    MovingSlotEntryStateN S rho t1 M0 (s + 1) Next Next := by
  obtain ⟨EndAt, hhistory, _hprev, hEndAt⟩ := hentry.prevEndpoint
  have hrunE : ∃ E : NamedBlock V, E.erase = End ∧ RunBlock S rho E := by
    rw [← hEndAt]
    exact hhistory.endpointRun _ hhistory.start_le (Nat.le_refl _)
  obtain ⟨End', hlow', hhigh', hstate'⟩ :=
    hhistory.through_slotWindow_byzantineProposer_named S adm hs hEndAt hrunE
      hrun hfacts hbyz hv hhorSC
  have hfreezeStrict :
      inclusiveEventIndex rho (Protocol.view_freeze S.E s) ≤
        strictEventIndex rho (Protocol.proposal_time S.E (s + 1)) :=
    inclusive_le_strict_of_lt rho (view_freeze_lt_proposal_time_succ S.E s)
  exact
    { startTime := hentry.startTime.trans
        (le_of_lt (proposal_time_lt_succ S.E s))
      prevEndpoint := ⟨End', hstate', hhigh' _ hfreezeStrict,
        hhigh' _ (hfreezeStrict.trans
          (strictEventIndex_le_inclusiveEventIndex rho _))⟩
      prevVotes := by simpa only [Nat.add_sub_cancel] using hprevVotes
      votes := hvotes
      headEq := fun hp => absurd hp hbyz
      confCompatible := by simpa only [Nat.add_sub_cancel] using hconf }

#print axioms MovingSlotEntryStateN.step_byzantineProposer_named

/-! ## Producing the window facts -/

/-
The byte-exact erased declaration is retained for audit. The live named
restatement follows it.

/-- Assemble `MovingSlotWindowFacts` from four per-read inputs.

The confirmation instant of the window is `t_s + 2Δ = confirmation_time (s-1)`.
When it is also a Section 7 action instant, the SG carrier, the attestation
outputs and the confirmation anchor all come from
`movingEventFacts_action_of_previousCarrierCeiling`, whose only history input is
The previous-round carrier ceiling. When it is not an action instant no
attestation is emitted there at all, and the same three obligations are free.

The four inputs are the protocol content of the window:

* `hheadEq` — in an honest-proposer slot the walk transfers, so every honest
  head is the endpoint;
* `hvoteAnchor` — every honest slot-`s` vote anchor is compatible with it;
* `hconfOut` — every honest slot-`(s-1)` confirmation selection is genuine and
  lands below the endpoint;
* `hcarrierCeiling` — at an action instant, every honest previous-round SG
  carrier is below the endpoint. -/
theorem movingSlotWindowFacts_of_readInputs
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hfb: BelowOneThird S rho.honest)
    {s: Slot} {End Next: Block V}
    (hle: Block.Preceq End Next)
    (hhor: Protocol.confirmation_time S.E (s - 1) ≤ rho.horizon)
    (hheadEq: S.E.proposer s ∈ rho.honest → ∀ w ∈ rho.honest,
      voteDutyHead S rho w s = End)
    (hvoteAnchor: ∀ w ∈ rho.honest,
      Block.compatible (Proofs.Optimistic.healAnchor S.E S.hc
        (Proofs.Optimistic.voteDutyStore S rho w s).toHealing) End = true)
    (hconfOut: ∀ w ∈ rho.honest,
      GenuineConfirmation (contract:= Protocol.GradeContract.current) S.E S.hc
          (Proofs.Optimistic.confStore S rho w (s - 1)) (s - 1)
          (movingSlotConfirmationOutput S rho (s - 1) w) ∧
        Block.Preceq (movingSlotConfirmationOutput S rho (s - 1) w) Next)
    (hcarrierCeiling: ∀ q: Round,
      S.a q = Protocol.confirmation_time S.E (s - 1) →
        0 < q ∧ S.E.t_GST ≤ S.a (q - 1) ∧
          S.hc.Γ_neg1 S.E.Δ q ≤ rho.horizon ∧
          ∀ u ∈ rho.honest,
            Block.Preceq (actionSGBlockAt S rho u (q - 1)) Next):
    MovingSlotWindowFacts S rho s End Next:= by
  classical
  have hconfNext: ∀ w ∈ rho.honest, ∀ C: Block V,
      GenuineConfirmation (contract:= Protocol.GradeContract.current) S.E S.hc
          (Proofs.Optimistic.confStore S rho w (s - 1)) (s - 1) C →
        Block.Preceq C Next:= by
    intro w hw C hC
    have hCeq: C = movingSlotConfirmationOutput S rho (s - 1) w:= by
      simpa only [movingSlotConfirmationOutput] using hC.selected.symm
    rw [hCeq]
    exact (hconfOut w hw).2
  have hopening: ∀ q: Round,
      S.a q = Protocol.confirmation_time S.E (s - 1) →
        S.hc.opening_slot q = s - 1:= by
    intro q hq
    have hslot:= congrArg S.E.slotOf
      ((Protocol.a_eq_confirmation_time S.hc S.E q).symm.trans hq)
    rw [Proofs.Optimistic.slotOf_confirmation_time,
      Proofs.Optimistic.slotOf_confirmation_time] at hslot
    exact Nat.add_right_cancel hslot
  refine
    { endLe:= hle
      voteHead:= hheadEq
      voteAnchor:= hvoteAnchor
      confirmed:= hconfNext
      carrier:= ?_
      outputs:= ?_
      confAnchorCompatible:= ?_ }
  · intro w hw q hq
    obtain ⟨hq0, hpost, hcut, hupper⟩:= hcarrierCeiling q hq
    have hslot:= hopening q hq
    obtain ⟨j, hj, _hout⟩:=
      honest_emits_exact_actionAttestationAt
        S adm hw q (hq ▸ hhor)
    exact (movingEventFacts_action_of_previousCarrierCeiling
      S adm hfb hq0 hpost hcut hw hj
      (by simpa only [hslot] using (hconfOut w hw).1)
      hupper (by simpa only [hslot] using (hconfOut w hw).2)).1
  · intro j w hw hev
    by_cases haction: ∃ q: Round,
        S.a q = Protocol.confirmation_time S.E (s - 1)
    · obtain ⟨q, hq⟩:= haction
      obtain ⟨hq0, hpost, hcut, hupper⟩:= hcarrierCeiling q hq
      have hslot:= hopening q hq
      rw [← hq] at hev
      exact (movingEventFacts_action_of_previousCarrierCeiling
        S adm hfb hq0 hpost hcut hw hev
        (by simpa only [hslot] using (hconfOut w hw).1)
        hupper (by simpa only [hslot] using (hconfOut w hw).2)).2.2.2.1
    · refine honestAttestationOutputPreceqAtIndex_of_no_emission S rho ?_
      rintro ⟨u, time, a, _hu, hevu, ha⟩
      have hteq: time = Protocol.confirmation_time S.E (s - 1):=
        (Event.tick.inj (Option.some.inj (hevu.symm.trans hev))).2
      have hemits: rho.emits S u (Object.attest a) time:= ⟨j, hevu, ha⟩
      have hshape:= Proofs.Optimistic.emits_attest_shape S hemits
      exact haction ⟨a.round, hshape.2.symm.trans hteq⟩
  · intro w hw
    exact Block.compatible_of_preceq_common
      (Block.preceq_trans
        (confAnchor_preceq_of_genuineConfirmation S.E S.hc
          (Proofs.Optimistic.confStore S rho w (s - 1)) (s - 1) _
          (hconfOut w hw).1)
        (hconfOut w hw).2)
      (Block.preceq_self Next)
-/



/-- Assemble the named moving-window facts from the four read inputs.
The confirmation field uses the confirming read's prepared contract, and the
anchor field uses that same read's named confirmation anchor. The previous
`MovingSlotWindowFacts` constructor remains available for the compatibility event
interface; this theorem is its named replacement. -/
theorem movingSlotWindowFacts_of_readInputs
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {s : Slot} {End Next : Block V}
    (hle : Block.Preceq End Next)
    (hhor : Protocol.confirmation_time S.E (s - 1) ≤ rho.horizon)
    (hheadEq : S.E.proposer s ∈ rho.honest → ∀ w ∈ rho.honest,
      voteDutyHead S rho w s = End)
    (hvoteAnchor : ∀ w ∈ rho.honest,
      Block.compatible (voterAnchorAt S rho w s) End = true)
    (hconfOut : ∀ w ∈ rho.honest,
      GenuineConfirmationWith
        (NamedProfile.gradeContract
          (confirmationInputRead S rho w (s - 1)).cache)
        S.E S.hc
          (Proofs.Optimistic.confStore S rho w (s - 1)) (s - 1)
          (movingSlotConfirmationOutput S rho (s - 1) w) ∧
        Block.Preceq (movingSlotConfirmationOutput S rho (s - 1) w) Next)
    (hcarrierCeiling : ∀ q : Round,
      S.a q = Protocol.confirmation_time S.E (s - 1) →
        0 < q ∧ S.E.t_GST ≤ S.a (q - 1) ∧
          S.hc.Γ_neg1 S.E.Δ q ≤ rho.horizon ∧
          ∀ u ∈ rho.honest,
            Block.Preceq (actionSGBlockAt S rho u (q - 1)) Next) :
    NamedMovingSlotWindowFacts S rho s End Next := by
  classical
  have hconfNext : ∀ w ∈ rho.honest, ∀ C : Block V,
      GenuineConfirmationWith
        (NamedProfile.gradeContract
          (confirmationInputRead S rho w (s - 1)).cache)
        S.E S.hc (Proofs.Optimistic.confStore S rho w (s - 1)) (s - 1) C →
        Block.Preceq C Next := by
    intro w hw C hC
    have hCeq : C = movingSlotConfirmationOutput S rho (s - 1) w := by
      simpa only [movingSlotConfirmationOutput] using hC.selected.symm
    rw [hCeq]
    exact (hconfOut w hw).2
  have hopening : ∀ q : Round,
      S.a q = Protocol.confirmation_time S.E (s - 1) →
        S.hc.opening_slot q = s - 1 := by
    intro q hq
    have hslot := congrArg S.E.slotOf
      ((Protocol.a_eq_confirmation_time S.hc S.E q).symm.trans hq)
    rw [Proofs.Optimistic.slotOf_confirmation_time,
      Proofs.Optimistic.slotOf_confirmation_time] at hslot
    exact Nat.add_right_cancel hslot
  have hconfAnchor : ∀ w ∈ rho.honest,
      Block.compatible
        (confirmationAnchorAt S rho w (s - 1)) Next = true := by
    intro w hw
    let contract := NamedProfile.gradeContract
      (confirmationInputRead S rho w (s - 1)).cache
    have hD := (hconfOut w hw).1
    have hselected := hD.selected
    rw [Protocol.update_confirmation_with_live_confirmed,
      if_pos hD.genuine] at hselected
    have hwalk : Protocol.confWalkWith contract S.E S.hc
        (Proofs.Optimistic.confStore S rho w (s - 1)) (s - 1) =
        movingSlotConfirmationOutput S rho (s - 1) w := by
      simpa only [contract, movingSlotConfirmationOutput] using hselected
    have hfloor : Block.Preceq
        (Protocol.confAnchorWith contract S.E S.hc
          (Proofs.Optimistic.confStore S rho w (s - 1)))
        (Protocol.confWalkWith contract S.E S.hc
          (Proofs.Optimistic.confStore S rho w (s - 1)) (s - 1)) :=
      Protocol.ghost_preceq
        (Protocol.confAnchorWith contract S.E S.hc
          (Proofs.Optimistic.confStore S rho w (s - 1)))
        (Protocol.confTree
          (Proofs.Optimistic.confStore S rho w (s - 1)))
        (Protocol.confScore S.E
          (Proofs.Optimistic.confStore S rho w (s - 1)) (s - 1))
        (Protocol.confEligible S.E
          (Proofs.Optimistic.confStore S rho w (s - 1)) (s - 1))
    rw [hwalk] at hfloor
    have hanchor : Block.Preceq
        (confirmationAnchorAt S rho w (s - 1))
        (movingSlotConfirmationOutput S rho (s - 1) w) := by
      simpa only [confirmationAnchorAt, namedConfirmationAnchor,
        Protocol.confAnchorWith, contract,
        Proofs.Optimistic.confStore_eq_confirmationInputRead] using hfloor
    exact Block.compatible_of_preceq_common
      (Block.preceq_trans hanchor (hconfOut w hw).2)
      (Block.preceq_self Next)
  refine
    { endLe := hle
      voteHead := hheadEq
      voteAnchor := hvoteAnchor
      confirmed := hconfNext
      carrier := ?_
      outputs := ?_
      confAnchorCompatible := hconfAnchor }
  · intro w hw q hq
    obtain ⟨hq0, hpost, hcut, hupper⟩ := hcarrierCeiling q hq
    have hslot := hopening q hq
    obtain ⟨j, hj, _hout⟩ :=
      honest_emits_exact_actionAttestationAt S adm hw q (hq ▸ hhor)
    have htime : Protocol.confirmation_time S.E (s - 1) = S.a q := hq.symm
    have hD : GenuineConfirmationWith
        (NamedProfile.gradeContract
          (NamedActionReads.confirmationReadAt S rho w (S.a q)).cache)
        S.E S.hc (Proofs.Optimistic.confStore S rho w (S.hc.opening_slot q))
          (S.hc.opening_slot q) (movingSlotConfirmationOutput S rho (s - 1) w) := by
      simpa only [confirmationInputRead, htime, hslot] using (hconfOut w hw).1
    exact (movingEventFacts_action_of_previousCarrierCeiling_named
      S adm hfb hq0 hpost hcut hw hj hD hupper
      (by simpa only [hslot] using (hconfOut w hw).2)).1
  · intro j w hw hev
    by_cases haction : ∃ q : Round,
        S.a q = Protocol.confirmation_time S.E (s - 1)
    · obtain ⟨q, hq⟩ := haction
      obtain ⟨hq0, hpost, hcut, hupper⟩ := hcarrierCeiling q hq
      have hslot := hopening q hq
      rw [← hq] at hev
      obtain ⟨_, hj, _hout⟩ := honest_emits_exact_actionAttestationAt
        S adm hw q (hq ▸ hhor)
      have htime : Protocol.confirmation_time S.E (s - 1) = S.a q := hq.symm
      have hD : GenuineConfirmationWith
          (NamedProfile.gradeContract
            (NamedActionReads.confirmationReadAt S rho w (S.a q)).cache)
          S.E S.hc (Proofs.Optimistic.confStore S rho w (S.hc.opening_slot q))
            (S.hc.opening_slot q) (movingSlotConfirmationOutput S rho (s - 1) w) := by
        simpa only [confirmationInputRead, htime, hslot] using (hconfOut w hw).1
      exact (movingEventFacts_action_of_previousCarrierCeiling_named
        S adm hfb hq0 hpost hcut hw hev hD hupper
        (by simpa only [hslot] using (hconfOut w hw).2)).2.2
    · refine honestAttestationOutputPreceqAtIndex_of_no_emission S rho ?_
      rintro ⟨u, time, a, _hu, hevu, ha⟩
      have hteq : time = Protocol.confirmation_time S.E (s - 1) :=
        (NamedEvent.tick.inj (Option.some.inj (hevu.symm.trans hev))).2
      have hemits : rho.emits S u (Object.attest a) time := ⟨j, hevu, ha⟩
      have hshape := Proofs.Optimistic.emits_attest_shape S hemits
      exact haction ⟨a.round, hshape.2.symm.trans hteq⟩

#print axioms movingSlotWindowFacts_of_readInputs


/-! ## Candidate-tree membership of an absorbed confirmation

The frozen candidate tree of a vote duty is
`get_filtered_block_tree_from st.toFG (voter_processed_block_tree …)`: the
processed blocks above `F` that are above the selected root and have a
processed descendant of state height at least `h_max - 1`. A block already at
that height is its own viability witness, so membership needs only visibility
and position. This is the same argument the moving state uses for its own
endpoint at a full-store read. -/

omit [Fintype V] in
/-- A visible block at the local viability height, above the finalized block
and above the selected root, is in the filtered tree drawn from any processed
set containing it. -/
theorem mem_get_filtered_block_tree_from_of_selfViable
    (st : Protocol.FGStore V) (blocks : Finset (Block V)) {A : Block V}
    (hmem : A ∈ blocks)
    (hF : Block.Preceq st.F A)
    (hroot : Block.Preceq (Protocol.get_fg_root st) A)
    (hheight : st.h_max - 1 ≤ (st.σ A).h) :
    A ∈ Protocol.get_filtered_block_tree_from st blocks := by
  simp only [Protocol.get_filtered_block_tree_from,
    Protocol.viable_tree, Protocol.finalized_descendants,
    Protocol.viable, Finset.mem_filter, decide_eq_true_eq]
  exact ⟨⟨⟨hmem, hF⟩, A, hmem, Block.preceq_self _, hheight⟩, hroot⟩

/-- The absorbed named confirmation reaches the next prepared vote head when
the endpoint already supplies the local height band. -/
theorem genuineConfirmation_preceq_nextVoteDutyHead_of_endpointBand
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v w : V} (hv : v ∈ rho.honest) (hw : w ∈ rho.honest)
    {s : Slot}
    (hpost : S.E.t_GST ≤ Protocol.proposal_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    {End : Block V} {B : NamedBlock V}
    (hgenuine : GenuineConfirmationWith
      (NamedProfile.gradeContract (confirmationInputRead S rho v s).cache)
      S.E S.hc (Proofs.Optimistic.confStore S rho v s) s B.erase)
    (hEndB : Block.Preceq End B.erase)
    (hanchorEnd : Block.Preceq
      (voterAnchorAt S rho w (s + 1)) End)
    (hprocessed : B.erase ∈ Protocol.voter_processed_block_tree S.E
      (voteDutyRead S rho w (s + 1)).st.core.toHealing.toFG.toSG.toGoldfishStore
      (voteDutyRead S rho w (s + 1)).st.core.s)
    (hband : (voteDutyRead S rho w (s + 1)).st.core.h_max - 1 ≤
      ((voteDutyRead S rho w (s + 1)).st.core.σ B.erase).h) :
    Block.Preceq B.erase (voterHeadAt S rho w (s + 1)) := by
  let read := voteDutyRead S rho w (s + 1)
  let target := read.st.core.toHealing
  let targetContract := NamedProfile.gradeContract read.cache
  let confContract := NamedProfile.gradeContract
    (confirmationInputRead S rho v s).cache
  have hslot : read.st.core.s = s + 1 := by
    simpa only [read] using Proofs.Optimistic.voteDutyRead_slot S rho w (s + 1)
  have hslotHealing : target.s = s + 1 := by
    simpa only [target, Protocol.Store.toHealing] using hslot
  have hrootAnchor : Block.Preceq
      (Protocol.get_fg_root target.toFG)
      (voterAnchorAt S rho w (s + 1)) :=
    NamedOutageClosure.fg_root_preceq_anchor S.E S.hc target
      (S.hc.round_of target.s)
      (DecoupledConsensusModel.Protocol.readFrame read.cache target
        (S.hc.round_of target.s)).g1
  have hrootBRead : Block.Preceq
      (Protocol.get_fg_root target.toFG) B.erase :=
    Block.preceq_trans hrootAnchor (Block.preceq_trans hanchorEnd hEndB)
  have hrootB : Block.Preceq
      (Protocol.get_fg_root
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG) B.erase := by
    simpa only [read, voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore] using hrootBRead
  have htransport := Protocol.adoptionTransport_B_after_gst S adm hv hw
    hpost hhor hrootB
  have htransportRead : AdoptionTransport
      (Proofs.Optimistic.confStore S rho v s).T target.T
      (confVotes S.E (Proofs.Optimistic.confStore S rho v s) s)
      (confLate S.E (Proofs.Optimistic.confStore S rho v s) s)
      (Protocol.voter_view S.E target.toFG.toSG.toGoldfishStore target.s)
      (Protocol.voter_support_view S.E target.toFG.toSG.toGoldfishStore target.s) B.erase := by
    change AdoptionTransport (Proofs.Optimistic.confStore S rho v s).T
      read.st.core.toHealing.T
      (confVotes S.E (Proofs.Optimistic.confStore S rho v s) s)
      (confLate S.E (Proofs.Optimistic.confStore S rho v s) s)
      (Protocol.voter_view S.E read.st.core.toHealing.toFG.toSG.toGoldfishStore read.st.core.s)
      (Protocol.voter_support_view S.E read.st.core.toHealing.toFG.toSG.toGoldfishStore read.st.core.s)
      B.erase
    rw [hslot]
    change AdoptionTransport (Proofs.Optimistic.confStore S rho v s).T
      (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).T
      (confVotes S.E (Proofs.Optimistic.confStore S rho v s) s)
      (confLate S.E (Proofs.Optimistic.confStore S rho v s) s)
      (Protocol.voter_view S.E
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG.toSG.toGoldfishStore (s + 1))
      (Protocol.voter_support_view S.E
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG.toSG.toGoldfishStore (s + 1))
      B.erase
    exact htransport
  have hsub : Protocol.voter_support_view S.E target.toFG.toSG.toGoldfishStore target.s ⊆
      Protocol.voter_view S.E target.toFG.toSG.toGoldfishStore target.s := by
    obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S
      adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
        (Protocol.vote_time S.E (s + 1))
    apply Protocol.voter_support_view_subset S.E
    intro C hC
    apply Proofs.Optimistic.carried_support_subset_of_mem_T S adm w n
    simpa only [target, read, voteDutyRead, Protocol.Store.toHealing,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      hn] using hC
  have hN := confNumerator S.E (Proofs.Optimistic.confStore S rho v s) s
  have hDwalk : B.erase = confWalkWith confContract S.E S.hc
      (Proofs.Optimistic.confStore S rho v s) s := by
    rw [← hgenuine.selected, update_confirmation_with_live_confirmed,
      if_pos hgenuine.genuine]
  have hEligible : Protocol.voters_count S.E
      (confLate S.E (Proofs.Optimistic.confStore S rho v s) s) s <
      2 * Protocol.goldfish_score S.E
        (Proofs.Optimistic.confStore S rho v s).T
        (confVotes S.E (Proofs.Optimistic.confStore S rho v s) s)
        (confVotes S.E (Proofs.Optimistic.confStore S rho v s) s) s B.erase := by
    have h := hgenuine.genuine
    rw [← hDwalk] at h
    simpa only [confEligible, confCount, confScore,
      decide_eq_true_eq] using h
  have hFroot : Block.Preceq target.F
      (Protocol.get_fg_root target.toFG) :=
    Proofs.Records.preceq_get_fg_root_of_F (st := target.toFG) (by
      simpa only [read, voteDutyRead,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
        (Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime S rho
          (Protocol.vote_time S.E (s + 1)) w))
  have hprocessedOld : B.erase ∈
      Protocol.voter_processed_block_tree S.E
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.toFG.toSG.toGoldfishStore
        (Proofs.Optimistic.voteDutyStore S rho w (s + 1)).toHealing.s := by
    simpa only [read, voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore] using hprocessed
  have hancestor : ∀ C : Block V, Block.Preceq C B.erase →
      C ∈ Protocol.voter_processed_block_tree S.E target.toFG.toSG.toGoldfishStore target.s := by
    intro C hCB
    have hC := WeakGoldfish.ancestorProcessed_of_voterProcessed
      S adm.toNamedAdmissibleCore hw hprocessedOld C hCB
    simpa only [read, voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock,
      Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore] using hC
  have hmem : ∀ C : Block V,
      Block.Preceq (Protocol.get_fg_root target.toFG) C →
      Block.Preceq C B.erase → C ∈ voterCandidateTreeAt S rho w (s + 1) := by
    intro C hrootC hCB
    change C ∈ Protocol.get_filtered_block_tree_from target.toFG
      (Protocol.voter_processed_block_tree S.E target.toFG.toSG.toGoldfishStore target.s)
    simp only [Protocol.get_filtered_block_tree_from,
      Protocol.viable_tree, Protocol.finalized_descendants,
      Protocol.viable, Finset.mem_filter, decide_eq_true_eq]
    exact ⟨⟨⟨hancestor C hCB, Block.preceq_trans hFroot hrootC⟩,
      B.erase, hprocessed, hCB, hband⟩, hrootC⟩
  have hcompatible : Block.compatible
      (Protocol.get_sg_root_with targetContract S.E S.hc target
        (S.hc.round_of target.s)) B.erase = true := by
    change Block.compatible (voterAnchorAt S rho w (s + 1)) B.erase = true
    exact Block.compatible_of_preceq_common
      (Block.preceq_trans hanchorEnd hEndB) (Block.preceq_self B.erase)
  have hpath : Block.Preceq (voterAnchorAt S rho w (s + 1)) B.erase →
      ∀ C : Block V,
        Block.Preceq (voterAnchorAt S rho w (s + 1)) C →
        C ≠ voterAnchorAt S rho w (s + 1) →
        Block.Preceq C B.erase → C ∈ voterCandidateTreeAt S rho w (s + 1) := by
    intro _ C hAC _ hCB
    exact hmem C (Block.preceq_trans hrootAnchor hAC) hCB
  have hhead : Block.Preceq B.erase
      (Protocol.get_head_in_tree_with_layer targetContract S.E S.hc target
        (voterCandidateTreeAt S rho w (s + 1))
        (Protocol.voter_view S.E target.toFG.toSG.toGoldfishStore target.s)
        (Protocol.voter_support_view S.E target.toFG.toSG.toGoldfishStore target.s) s) := by
    rw [Proofs.Optimistic.get_head_in_tree_split_with]
    exact Protocol.goldfish_fork_choice_captures_of_confirmation
      S.E target.σ target.h_max
      (Proofs.Optimistic.confStore S rho v s).T target.T
      (voterCandidateTreeAt S rho w (s + 1)) target.s
      (confEarly S.E (Proofs.Optimistic.confStore S rho v s) s)
      (confLate S.E (Proofs.Optimistic.confStore S rho v s) s)
      (confVotes S.E (Proofs.Optimistic.confStore S rho v s) s)
      (Protocol.voter_view S.E target.toFG.toSG.toGoldfishStore target.s)
      (Protocol.voter_support_view S.E target.toFG.toSG.toGoldfishStore target.s)
      s hN htransportRead hEligible hsub hcompatible hpath
  rw [voterHeadAt_eq_get_head_with_anchor S rho w (s + 1)]
  simpa only [targetContract, target, read, hslot, hslotHealing,
    Nat.add_sub_cancel] using hhead









/-! ## The root at a confirmation read is below the previous endpoint

A crossing row visible at the slot-`c` confirmation evaluation was emitted at a
Section 7 action instant, and the latest action instant strictly below
`t_c + 6Δ` is `t_{c-1} + 6Δ = t_{c+1} - 2Δ`, which is before the slot-`(c+1)`
proposal. So every such row is already inside the moving history at the strict
proposal cursor, and both the frontier band and the selected root are bounded
by the endpoint there — the `Prev` of the slot-`(c+1)` entry state. No rise
bound and no honest-proposer premise is used. -/
















/-! ## Certifying the window's confirmations against the previous endpoint -/











#print axioms publicTime_slotWindow_cases
#print axioms movingEventFacts_proposalInstant
#print axioms movingEventFacts_viewFreeze
#print axioms movingEventFacts_vote_named
#print axioms movingEventFacts_confirmation_named
#print axioms strictSupportCutoff_lt_inclusiveViewFreeze
#print axioms through_slotWindowPrefix_named
#print axioms MovingFrontierChainStateN.through_slotWindow_byzantineProposer_named
#print axioms MovingFrontierChainStateN.through_slotWindow_honestProposer_named
#print axioms mem_get_filtered_block_tree_from_of_selfViable
#print axioms genuineConfirmation_preceq_nextVoteDutyHead_of_endpointBand

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
