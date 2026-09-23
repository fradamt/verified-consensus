module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Schedule.MovingChainNextEntry
public import DecoupledConsensusProofs.Protocol.ChainState.ProposalBridge

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Iterating the slot step

One slot step is `MovingSlotEntryState.windowFacts` followed by
`stepHonest` or `stepByzantine`. Iterating it needs one thing the entry state
does not carry: a per-slot FAMILY of endpoints, with the facts of the slots
already passed. The moving history inside a state is an existential witness
and a later state's witness is a different function, so the family is built
here instead, by extension, and the facts are carried with it.

`MovingSlotFoldAt S rho t1 M0 s0 s F End` is the loop invariant: the fold has
reached slot `s` from `s0`, the family `F` gives the pre-proposal endpoint of
every slot in `[s0, s]`, and the three slot-indexed facts of fk15's floor
record hold on that range. `F s` is the current state's `Prev` and `End` its
entry endpoint.
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

private theorem nat_not_succ_succ_le (c : Nat) : ¬ (c + 1 + 1 ≤ c + 1) := by
  omega

private theorem nat_le_of_lt_succ' {d c : Nat} (h : d < c + 1 + 1) :
    d ≤ c + 1 := by omega

private theorem nat_shift_succ (c n : Nat) :
    c + 1 + 1 + n = c + 1 + (n + 1) := by omega

private theorem nat_lt_shift {j c n : Nat} (h : j < c + 1 + n) :
    j < c + (n + 1) := by omega


private theorem nat_not_add_two_le_succ (d : Nat) : ¬ (d + 2 ≤ d + 1) := by
  omega

private theorem nat_eq_of_succ_le_succ_of_lt_succ {d c : Nat}
    (hge : c + 1 ≤ d + 1) (hlt : d + 1 < c + 1 + 1) : d = c :=
  Nat.le_antisymm (Nat.le_of_succ_le_succ (Nat.le_of_lt_succ hlt))
    (Nat.le_of_succ_le_succ hge)


/-- The named loop invariant of the slot fold.

This is the additive prepared twin of `MovingSlotFoldAt`. Its entry and
history use the named moving-chain records, and its confirmation field uses
the contract carried by the named confirmation input. -/
structure MovingSlotFoldAtN
    (S : Setup V) (rho : Run V) (t1 : Time) (M0 : Height)
    (s0 s : Slot) (F : Slot → Block V) (End : Block V) : Prop where
  base : s0 ≤ s
  entry : MovingSlotEntryStateN S rho t1 M0 s (F s) End
  /-- In an honest-proposer slot the entry endpoint IS the slot proposal. -/
  endpointProposal : S.E.proposer s ∈ rho.honest →
    ∃ P : NamedBlock V, proposedBlockAt S rho s = some P ∧ End = P.erase
  /-- `endpointMonotone`, on the range reached. -/
  mono : ∀ d e : Slot, s0 ≤ d → d ≤ e → e ≤ s →
    Block.Preceq (F d) (F e)
  /-- `endpointBelowHonestParent`, on the range reached. -/
  parent : ∀ d : Slot, s0 ≤ d → d ≤ s → S.E.proposer d ∈ rho.honest →
    Block.Preceq (F d) (proposedParent S rho d)
  /-- The named honest proposal is absorbed by the next endpoint. -/
  absorbed : ∀ d : Slot, s0 ≤ d → d < s → S.E.proposer d ∈ rho.honest →
    ∃ P : NamedBlock V, proposedBlockAt S rho d = some P ∧
      Block.Preceq P.erase (F (d + 1))
  /-- The slot's own honest vote cone, above the next window endpoint. -/
  windowCone : ∀ d : Slot, s0 ≤ d → d < s →
    NamedHonestVotesCone S rho d (fun X => Block.Preceq (F (d + 1)) X)
  /-- Named honest confirmation outputs are genuine and absorbed. -/
  confAbsorbed : ∀ d : Slot, s0 ≤ d → d + 1 < s → ∀ u ∈ rho.honest,
    GenuineConfirmationWith
        (NamedProfile.gradeContract (confirmationInputRead S rho u d).cache)
        S.E S.hc (Proofs.Optimistic.confStore S rho u d) d
        (movingSlotConfirmationOutput S rho d u) ∧
      Block.Preceq (movingSlotConfirmationOutput S rho d u) (F (d + 2))
  /-- Confirmation outputs are above the endpoint entered by their slot. -/
  confAbove : ∀ d : Slot, s0 ≤ d → d + 1 < s → ∀ u ∈ rho.honest,
    Block.Preceq (F (d + 1)) (movingSlotConfirmationOutput S rho d u)
  /-- The named moving history at every passed proposal cursor. -/
  historyAt : ∀ d : Slot, s0 ≤ d → d ≤ s →
    ∃ EndAt : Nat → Block V,
      MovingFrontierChainStateN S rho t1 M0 (strictEventIndex rho t1)
          (strictEventIndex rho (Protocol.proposal_time S.E d)) EndAt ∧
        EndAt (strictEventIndex rho (Protocol.proposal_time S.E d)) = F d

/-- The schedule and horizon data one step of the fold consumes: the window
data of the slot being left, its action timing, and the window data of the slot
being entered. -/
def MovingSlotStepSupply
    (S : Setup V) (rho : Run V) (t1 : Time) (M0 : Height) (c : Slot) : Prop :=
  MovingSlotWindowData S rho t1 M0 c ∧ MovingSlotActionTiming S rho t1 c ∧
    MovingSlotWindowData S rho t1 M0 (c + 1)


-- pins the fold cannot supply for the slot it is about to enter.
private theorem movingSlotEntryStateN_prevLe
    {S : Setup V} {rho : Run V} {t1 : Time} {M0 : Height}
    {s : Slot} {Prev End : Block V}
    (h : MovingSlotEntryStateN S rho t1 M0 s Prev End) :
    Block.Preceq Prev End := by
  obtain ⟨EndAt, hhistory, hprev, hEnd⟩ := h.prevEndpoint
  rw [← hprev, ← hEnd]
  have hmono : ∀ {j k : Nat},
      strictEventIndex rho t1 ≤ j → j ≤ k →
      k ≤ inclusiveEventIndex rho (Protocol.proposal_time S.E s) →
      Block.Preceq (EndAt j) (EndAt k) := by
    intro j k hj hjk hk
    induction hjk with
    | refl => exact Block.preceq_self _
    | @step k hjk ih =>
        exact Block.preceq_trans (ih (Nat.le_trans (Nat.le_succ k) hk))
          (hhistory.endpointMono k (hj.trans hjk) (Nat.lt_of_succ_le hk))
  exact hmono (strictEventIndex_mono rho h.startTime)
    (strictEventIndex_le_inclusiveEventIndex rho _) (Nat.le_refl _)

/-- **One step of the named fold**, over the slot the step is about to enter.

`MovingSlotFoldAtN` records the adoption facts of every slot the fold has
PASSED. Both branches of the step need the same facts one slot further on, at
`c + 2`, and the fold does not have them: the honest branch needs the
proposal's parent to sit at or above the window endpoint, the slot-`(c + 2)`
vote cone above that proposal, and the proposal-walk transfer; the Byzantine
branch needs the slot-`(c + 2)` vote cone above the window endpoint itself.
Those are the adoption step at an arbitrary honest-proposer slot, taken here as
pins (PRE-BUILDING) and closed by a one-line consumer when their producer
lands. -/
theorem MovingSlotFoldAtN.step_of_slotCone
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {t1 : Time} {M0 : Height} {s0 c : Slot} {F : Slot → Block V}
    {End : Block V}
    (hfold : MovingSlotFoldAtN S rho t1 M0 s0 (c + 1) F End)
    (hsupply : MovingSlotStepSupply S rho t1 M0 c)
    {v : V} (hv : v ∈ rho.honest)
    (_of_honestSlotAdoption : ∀ Next : Block V,
      MovingSlotFrontierAt S rho c End Next →
      S.E.proposer (c + 1 + 1) ∈ rho.honest →
      ∀ P : NamedBlock V, proposedBlockAt S rho (c + 1 + 1) = some P →
        Block.Preceq Next (proposedParent S rho (c + 1 + 1)) ∧
        NamedHonestVotesCone S rho (c + 1 + 1)
            (fun X => Block.Preceq P.erase X) ∧
        (∀ w ∈ rho.honest, ∃ tree₀ : Finset (Block V),
          Proofs.Optimistic.NamedVoteStoreExtends S rho w (c + 1 + 1) tree₀
            (proposedParent S rho (c + 1 + 1)) P) ∧
        (∀ w ∈ rho.honest, ∀ D : Block V,
          GenuineConfirmationWith
            (NamedProfile.gradeContract
              (confirmationInputRead S rho w (c + 1)).cache)
            S.E S.hc (Proofs.Optimistic.confStore S rho w (c + 1)) (c + 1) D →
            Block.compatible D P.erase = true))
    (_of_byzantineSlotCone : ∀ Next : Block V,
      MovingSlotFrontierAt S rho c End Next →
      S.E.proposer (c + 1 + 1) ∉ rho.honest →
      NamedHonestVotesCone S rho (c + 1 + 1)
        (fun X => Block.Preceq Next X)) :
    ∃ (F' : Slot → Block V) (End' : Block V),
      MovingSlotFoldAtN S rho t1 M0 s0 (c + 1 + 1) F' End' ∧
        ∀ d : Slot, d ≤ c + 1 → F' d = F d := by
  classical
  obtain ⟨hdata, htiming, hdata'⟩ := hsupply
  obtain ⟨r, hround, ht1, hpostAction, hcut⟩ := hdata.round
  obtain ⟨Next, hfrontier, hfacts⟩ :=
    hfold.entry.windowFacts S adm hcom hfb hdata.pos hround ht1 hpostAction
      hcut hdata.postVote hdata.postProp hdata.slotHor htiming
  refine ⟨fun d => if d ≤ c + 1 then F d else Next, ?_⟩
  have hlow : ∀ d : Slot, d ≤ c + 1 →
      (if d ≤ c + 1 then F d else Next) = F d := fun _ hd => if_pos hd
  have hhigh :
      (if c + 1 + 1 ≤ c + 1 then F (c + 1 + 1) else Next) = Next :=
    if_neg (nat_not_succ_succ_le c)
  have hendNext : Block.Preceq End Next := hfrontier.oldPreceq
  have hprevNext : Block.Preceq (F (c + 1)) Next :=
    Block.preceq_trans (movingSlotEntryStateN_prevLe hfold.entry) hendNext
  have hmono : ∀ d e : Slot, s0 ≤ d → d ≤ e → e ≤ c + 1 + 1 →
      Block.Preceq (if d ≤ c + 1 then F d else Next)
        (if e ≤ c + 1 then F e else Next) := by
    intro d e hd hde he
    by_cases hec : e ≤ c + 1
    · rw [hlow d (hde.trans hec), hlow e hec]
      exact hfold.mono d e hd hde hec
    · rw [if_neg hec]
      by_cases hdle : d ≤ c + 1
      · rw [hlow d hdle]
        exact Block.preceq_trans
          (hfold.mono d (c + 1) hd hdle (Nat.le_refl _)) hprevNext
      · rw [if_neg hdle]
        exact Block.preceq_self Next
  have habsorbed : ∀ d : Slot, s0 ≤ d → d < c + 1 + 1 →
      S.E.proposer d ∈ rho.honest →
      ∃ P : NamedBlock V, proposedBlockAt S rho d = some P ∧
        Block.Preceq P.erase
          (if d + 1 ≤ c + 1 then F (d + 1) else Next) := by
    intro d hd hdlt hdprop
    rcases Nat.lt_or_ge d (c + 1) with hlt | hge
    · rw [hlow (d + 1) (Nat.succ_le_of_lt hlt)]
      exact hfold.absorbed d hd hlt hdprop
    · have hdeq : d = c + 1 := Nat.le_antisymm (nat_le_of_lt_succ' hdlt) hge
      subst hdeq
      obtain ⟨P, hP, hEnd⟩ := hfold.endpointProposal hdprop
      rw [hhigh]
      exact ⟨P, hP, hEnd ▸ hendNext⟩
  have hconfAbsorbed : ∀ d : Slot, s0 ≤ d → d + 1 < c + 1 + 1 →
      ∀ u ∈ rho.honest,
        GenuineConfirmationWith
            (NamedProfile.gradeContract (confirmationInputRead S rho u d).cache)
            S.E S.hc (Proofs.Optimistic.confStore S rho u d) d
            (movingSlotConfirmationOutput S rho d u) ∧
          Block.Preceq (movingSlotConfirmationOutput S rho d u)
            (if d + 2 ≤ c + 1 then F (d + 2) else Next) := by
    intro d hd hdlt u hu
    rcases Nat.lt_or_ge (d + 1) (c + 1) with hlt | hge
    · rw [hlow (d + 2) (Nat.succ_le_of_lt hlt)]
      exact hfold.confAbsorbed d hd hlt u hu
    · have hdeq : d = c := nat_eq_of_succ_le_succ_of_lt_succ hge hdlt
      subst hdeq
      have hout := hfold.entry.confOutcome_atPrev_named S adm hcom hfb
        hdata.pos hround ht1 hpostAction hcut hdata.postVote hdata.slotHor hu
      refine ⟨hout.1, ?_⟩
      rw [if_neg (nat_not_add_two_le_succ d)]
      exact hfrontier.genuinePreceq u hu _ hout.1
  have hconfAbove : ∀ d : Slot, s0 ≤ d → d + 1 < c + 1 + 1 →
      ∀ u ∈ rho.honest,
        Block.Preceq (if d + 1 ≤ c + 1 then F (d + 1) else Next)
          (movingSlotConfirmationOutput S rho d u) := by
    intro d hd hdlt u hu
    rcases Nat.lt_or_ge (d + 1) (c + 1) with hlt | hge
    · rw [hlow (d + 1) (le_of_lt hlt)]
      exact hfold.confAbove d hd hlt u hu
    · have hdeq : d = c := nat_eq_of_succ_le_succ_of_lt_succ hge hdlt
      subst hdeq
      rw [hlow (d + 1) (Nat.le_refl _)]
      exact (hfold.entry.confOutcome_atPrev_named S adm hcom hfb
        hdata.pos hround ht1 hpostAction hcut hdata.postVote hdata.slotHor
        hu).2
  have hcone := hfold.entry.windowVotesCone S adm hcom hfb hdata.pos hround
    ht1 hpostAction hcut hdata.postVote hdata.postProp hdata.slotHor
    hfrontier
  have hwindowCone : ∀ d : Slot, s0 ≤ d → d < c + 1 + 1 →
      NamedHonestVotesCone S rho d
        (fun X => Block.Preceq
          (if d + 1 ≤ c + 1 then F (d + 1) else Next) X) := by
    intro d hd hdlt
    rcases Nat.lt_or_ge d (c + 1) with hlt | hge
    · rw [hlow (d + 1) (Nat.succ_le_of_lt hlt)]
      exact hfold.windowCone d hd hlt
    · have hdeq : d = c + 1 := Nat.le_antisymm (nat_le_of_lt_succ' hdlt) hge
      subst hdeq
      rw [if_neg (nat_not_succ_succ_le c)]
      exact hcone
  have hhistoryAt : ∀ E' : Block V,
      MovingSlotEntryStateN S rho t1 M0 (c + 1 + 1) Next E' →
      ∀ d : Slot, s0 ≤ d → d ≤ c + 1 + 1 →
        ∃ EndAt : Nat → Block V,
          MovingFrontierChainStateN S rho t1 M0 (strictEventIndex rho t1)
              (strictEventIndex rho (Protocol.proposal_time S.E d)) EndAt ∧
            EndAt (strictEventIndex rho (Protocol.proposal_time S.E d)) =
              (if d ≤ c + 1 then F d else Next) := by
    intro E' hentry' d hd hdle
    rcases Nat.lt_or_ge d (c + 1 + 1) with hlt | hge
    · obtain ⟨EndAt, hstate, hval⟩ :=
        hfold.historyAt d hd (nat_le_of_lt_succ' hlt)
      refine ⟨EndAt, hstate, ?_⟩
      rw [hlow d (nat_le_of_lt_succ' hlt)]
      exact hval
    · have hdeq : d = c + 1 + 1 := Nat.le_antisymm hdle hge
      subst hdeq
      obtain ⟨EndAt, hhistory, hprev, _hEnd⟩ := hentry'.prevEndpoint
      refine ⟨EndAt, hhistory.prefix
        (strictEventIndex_mono rho hentry'.startTime)
        (strictEventIndex_le_inclusiveEventIndex rho _), ?_⟩
      rw [hhigh]
      exact hprev
  obtain ⟨EndAt0, hhistory0, _hprev0, hEnd0⟩ := hfold.entry.prevEndpoint
  have hrunEnd : ∃ E : NamedBlock V, E.erase = End ∧ RunBlock S rho E := by
    rw [← hEnd0]
    exact hhistory0.endpointRun _ hhistory0.start_le (Nat.le_refl _)
  have hrunNext : ∃ E : NamedBlock V, E.erase = Next ∧ RunBlock S rho E :=
    hfrontier.runBlock S adm hrunEnd
  by_cases hprop : S.E.proposer (c + 1 + 1) ∈ rho.honest
  · obtain ⟨P, hP⟩ := proposedBlockAt_isSome S rho (c + 1 + 1)
    obtain ⟨hparent, hnextCone, hheadEq, hnextConf⟩ :=
      _of_honestSlotAdoption Next hfrontier hprop P hP
    have hentry' := hfold.entry.step_honestProposer_named S adm
      (Nat.succ_pos c) hrunNext
      hfacts hprop
      (by exact ((Protocol.proposal_time_succ_lt_confirmation_time S.E
        (c + 1)).le).trans hdata'.slotHor)
      (by
        exact le_trans (support_cutoff_le_confirmation_time S.E (c + 1))
          hdata'.slotHor)
      hparent hv hP hcone hnextCone hheadEq hnextConf
    refine ⟨P.erase, ?_, hlow⟩
    exact
      { base := hfold.base.trans (Nat.le_succ _)
        entry := by rw [hhigh]; exact hentry'
        endpointProposal := fun _ => ⟨P, hP, rfl⟩
        mono := hmono
        parent := by
          intro d hd hdle hdprop
          rcases Nat.lt_or_ge d (c + 1 + 1) with hlt | hge
          · rw [hlow d (nat_le_of_lt_succ' hlt)]
            exact hfold.parent d hd (nat_le_of_lt_succ' hlt) hdprop
          · have hdeq : d = c + 1 + 1 := Nat.le_antisymm hdle hge
            subst hdeq
            rw [hhigh]
            exact hparent
        absorbed := habsorbed
        confAbsorbed := hconfAbsorbed
        confAbove := hconfAbove
        windowCone := hwindowCone
        historyAt := hhistoryAt _ hentry' }
  · have hentry' := hfold.entry.step_byzantineProposer_named S adm
      (Nat.succ_pos c) hrunNext hfacts hprop hv
      ((support_cutoff_le_confirmation_time S.E (c + 1)).trans hdata'.slotHor)
      hcone (_of_byzantineSlotCone Next hfrontier hprop)
      (by
        obtain ⟨r', hround', ht1', hpostAction', hcut'⟩ := hdata'.round
        exact (hfold.entry.nextPreEntry_byzantine S adm hcom hfb hdata.pos
          hround ht1 hpostAction hcut hdata.postVote hdata.postProp
          hdata.slotHor hfrontier hfacts hprop hv
          ((support_cutoff_le_confirmation_time S.E (c + 1)).trans
            hdata'.slotHor)).confCompatible_byzantine S adm hcom hfb
          (Nat.succ_pos c) hround' ht1' hpostAction' hcut' hdata'.postVote
          hdata'.slotHor)
    refine ⟨Next, ?_, hlow⟩
    exact
      { base := hfold.base.trans (Nat.le_succ _)
        entry := by rw [hhigh]; exact hentry'
        endpointProposal := fun hp => absurd hp hprop
        mono := hmono
        parent := by
          intro d hd hdle hdprop
          rcases Nat.lt_or_ge d (c + 1 + 1) with hlt | hge
          · rw [hlow d (nat_le_of_lt_succ' hlt)]
            exact hfold.parent d hd (nat_le_of_lt_succ' hlt) hdprop
          · have hdeq : d = c + 1 + 1 := Nat.le_antisymm hdle hge
            subst hdeq
            exact absurd hdprop hprop
        absorbed := habsorbed
        confAbsorbed := hconfAbsorbed
        confAbove := hconfAbove
        windowCone := hwindowCone
        historyAt := hhistoryAt _ hentry' }



/-
/-- **One step of the fold.**

The window facts of slot `c + 1` choose the window endpoint; the next
proposer's honesty chooses the branch. The family is extended by that window
endpoint, which is the next slot's pre-proposal endpoint in both branches. -/
theorem MovingSlotFoldAt.step
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hfb: BelowOneThird S rho.honest)
    {t1: Time} {M0: Height} {s0 c: Slot} {F: Slot → Block V}
    {End: Block V}
    (hfold: MovingSlotFoldAt S rho t1 M0 s0 (c + 1) F End)
    (hsupply: MovingSlotStepSupply S rho t1 M0 c)
    {v: V} (hv: v ∈ rho.honest):
    ∃ (F': Slot → Block V) (End': Block V),
      MovingSlotFoldAt S rho t1 M0 s0 (c + 1 + 1) F' End' ∧
        ∀ d: Slot, d ≤ c + 1 → F' d = F d:= by
  classical
  obtain ⟨hdata, htiming, hdata'⟩:= hsupply
  obtain ⟨r, hround, ht1, hpostAction, hcut⟩:= hdata.round
  obtain ⟨Next, hfrontier, hfacts⟩:=
    hfold.entry.windowFacts S adm hcom hfb hdata.pos hround ht1 hpostAction
      hcut hdata.postVote hdata.postProp hdata.slotHor htiming
  refine ⟨fun d => if d ≤ c + 1 then F d else Next, ?_⟩
  have hlow: ∀ d: Slot, d ≤ c + 1 →
      (if d ≤ c + 1 then F d else Next) = F d:= fun _ hd => if_pos hd
  have hhigh: (if c + 1 + 1 ≤ c + 1 then F (c + 1 + 1) else Next) = Next:=
    if_neg (nat_not_succ_succ_le c)
  have hendNext: Block.Preceq End Next:= hfrontier.oldPreceq
  have hprevNext: Block.Preceq (F (c + 1)) Next:=
    Block.preceq_trans hfold.entry.toPre.prevLe hendNext
  have hmono: ∀ d e: Slot, s0 ≤ d → d ≤ e → e ≤ c + 1 + 1 →
      Block.Preceq (if d ≤ c + 1 then F d else Next)
        (if e ≤ c + 1 then F e else Next):= by
    intro d e hd hde he
    by_cases hec: e ≤ c + 1
    · rw [hlow d (hde.trans hec), hlow e hec]
      exact hfold.mono d e hd hde hec
    · rw [if_neg hec]
      by_cases hdle: d ≤ c + 1
      · rw [hlow d hdle]
        exact Block.preceq_trans (hfold.mono d (c + 1) hd hdle (Nat.le_refl _))
          hprevNext
      · rw [if_neg hdle]
        exact Block.preceq_self Next
  have habsorbed: ∀ d: Slot, s0 ≤ d → d < c + 1 + 1 →
      S.E.proposer d ∈ rho.honest →
      Block.Preceq (proposedBlock S rho d)
        (if d + 1 ≤ c + 1 then F (d + 1) else Next):= by
    intro d hd hdlt hdprop
    rcases Nat.lt_or_ge d (c + 1) with hlt | hge
    · rw [hlow (d + 1) (Nat.succ_le_of_lt hlt)]
      exact hfold.absorbed d hd hlt hdprop
    · have hdeq: d = c + 1:= Nat.le_antisymm (nat_le_of_lt_succ' hdlt) hge
      subst hdeq
      rw [hhigh]
      rw [hfold.endpointProposal hdprop] at hendNext
      exact hendNext
  have hconfAbsorbed: ∀ d: Slot, s0 ≤ d → d + 1 < c + 1 + 1 →
      ∀ u ∈ rho.honest,
        GenuineConfirmation (contract:= Protocol.GradeContract.current) S.E S.hc (Proofs.Optimistic.confStore S rho u d) d
            (movingSlotConfirmationOutput S rho d u) ∧
          Block.Preceq (movingSlotConfirmationOutput S rho d u)
            (if d + 2 ≤ c + 1 then F (d + 2) else Next):= by
    intro d hd hdlt u hu
    rcases Nat.lt_or_ge (d + 1) (c + 1) with hlt | hge
    · rw [hlow (d + 2) (Nat.succ_le_of_lt hlt)]
      exact hfold.confAbsorbed d hd hlt u hu
    · have hdeq: d = c:= nat_eq_of_succ_le_succ_of_lt_succ hge hdlt
      subst hdeq
      have hout:= hfold.entry.toPre.confOutcome_atPrev S adm hcom hfb
        hdata.pos hround ht1 hpostAction hcut hdata.postVote hdata.slotHor
        hu
      refine ⟨hout.1, ?_⟩
      rw [if_neg (nat_not_add_two_le_succ d)]
      exact hfrontier.genuinePreceq u hu _ hout.1
  have hconfAbove: ∀ d: Slot, s0 ≤ d → d + 1 < c + 1 + 1 →
      ∀ u ∈ rho.honest,
        Block.Preceq (if d + 1 ≤ c + 1 then F (d + 1) else Next)
          (movingSlotConfirmationOutput S rho d u):= by
    intro d hd hdlt u hu
    rcases Nat.lt_or_ge (d + 1) (c + 1) with hlt | hge
    · rw [hlow (d + 1) (le_of_lt hlt)]
      exact hfold.confAbove d hd hlt u hu
    · have hdeq: d = c:= nat_eq_of_succ_le_succ_of_lt_succ hge hdlt
      subst hdeq
      rw [hlow (d + 1) (Nat.le_refl _)]
      exact (hfold.entry.toPre.confOutcome_atPrev S adm hcom hfb
        hdata.pos hround ht1 hpostAction hcut hdata.postVote hdata.slotHor
        hu).2
  have hcone:= hfold.entry.windowVotesCone S adm hcom hfb hdata.pos hround
    ht1 hpostAction hcut hdata.postVote hdata.postProp hdata.slotHor
    hfrontier
  have hwindowCone: ∀ d: Slot, s0 ≤ d → d < c + 1 + 1 →
      Proofs.Optimistic.HonestVotesCone S rho d
        (fun X => Block.Preceq (if d + 1 ≤ c + 1 then F (d + 1) else Next) X):= by
    intro d hd hdlt
    rcases Nat.lt_or_ge d (c + 1) with hlt | hge
    · rw [hlow (d + 1) (Nat.succ_le_of_lt hlt)]
      exact hfold.windowCone d hd hlt
    · have hdeq: d = c + 1:= Nat.le_antisymm (nat_le_of_lt_succ' hdlt) hge
      subst hdeq
      rw [if_neg (nat_not_succ_succ_le c)]
      exact hcone
  have hhistoryAt: ∀ E': Block V,
      MovingSlotEntryState S rho t1 M0 (c + 1 + 1) Next E' →
      ∀ d: Slot, s0 ≤ d → d ≤ c + 1 + 1 →
        ∃ EndAt: Nat → Block V,
          MovingFrontierChainState S rho t1 M0 (strictEventIndex rho t1)
              (strictEventIndex rho (Protocol.proposal_time S.E d)) EndAt ∧
            EndAt (strictEventIndex rho (Protocol.proposal_time S.E d)) =
              (if d ≤ c + 1 then F d else Next):= by
    intro E' hentry' d hd hdle
    rcases Nat.lt_or_ge d (c + 1 + 1) with hlt | hge
    · obtain ⟨EndAt, hstate, hval⟩:=
        hfold.historyAt d hd (nat_le_of_lt_succ' hlt)
      refine ⟨EndAt, hstate, ?_⟩
      rw [hlow d (nat_le_of_lt_succ' hlt)]
      exact hval
    · have hdeq: d = c + 1 + 1:= Nat.le_antisymm hdle hge
      subst hdeq
      obtain ⟨EndAt, hhistory, hprev, _hEnd⟩:= hentry'.prevEndpoint
      refine ⟨EndAt, hhistory.prefix
        (strictEventIndex_mono rho hentry'.startTime)
        (strictEventIndex_le_inclusiveEventIndex rho _), ?_⟩
      rw [hhigh]
      exact hprev
  by_cases hprop: S.E.proposer (c + 1 + 1) ∈ rho.honest
  · have hparent:= hfold.entry.honestParent S adm hcom hfb hdata hdata'
      hfrontier hfacts hprop hv
    have hentry':= hfold.entry.stepHonest S adm hcom hfb hdata hdata'
      hfrontier hfacts hprop hparent hv
    refine ⟨proposedBlock S rho (c + 1 + 1), ?_, hlow⟩
    exact
      { base:= hfold.base.trans (Nat.le_succ _)
        entry:= by rw [hhigh]; exact hentry'
        endpointProposal:= fun _ => rfl
        mono:= hmono
        parent:= by
          intro d hd hdle hdprop
          rcases Nat.lt_or_ge d (c + 1 + 1) with hlt | hge
          · rw [hlow d (nat_le_of_lt_succ' hlt)]
            exact hfold.parent d hd (nat_le_of_lt_succ' hlt) hdprop
          · have hdeq: d = c + 1 + 1:= Nat.le_antisymm hdle hge
            subst hdeq
            rw [hhigh]
            exact hparent
        absorbed:= habsorbed
        confAbsorbed:= hconfAbsorbed
        confAbove:= hconfAbove
        windowCone:= hwindowCone
        historyAt:= hhistoryAt _ hentry' }
  · have hentry':= hfold.entry.stepByzantine S adm hcom hfb hdata hdata'
      hfrontier hfacts hprop hv
    refine ⟨Next, ?_, hlow⟩
    exact
      { base:= hfold.base.trans (Nat.le_succ _)
        entry:= by rw [hhigh]; exact hentry'
        endpointProposal:= fun hp => absurd hp hprop
        mono:= hmono
        parent:= by
          intro d hd hdle hdprop
          rcases Nat.lt_or_ge d (c + 1 + 1) with hlt | hge
          · rw [hlow d (nat_le_of_lt_succ' hlt)]
            exact hfold.parent d hd (nat_le_of_lt_succ' hlt) hdprop
          · have hdeq: d = c + 1 + 1:= Nat.le_antisymm hdle hge
            subst hdeq
            exact absurd hdprop hprop
        absorbed:= habsorbed
        confAbsorbed:= hconfAbsorbed
        confAbove:= hconfAbove
        windowCone:= hwindowCone
        historyAt:= hhistoryAt _ hentry' }
-/




/-
/-- **The fold, iterated.**

`n` slots of supply carry the fold `n` slots forward. The family and the three
facts extend with it; nothing about the slots already passed changes. -/
theorem MovingSlotFoldAt.iterate
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hfb: BelowOneThird S rho.honest)
    {t1: Time} {M0: Height} {s0: Slot}
    {v: V} (hv: v ∈ rho.honest):
    ∀ (n: Nat) (c: Slot) (F: Slot → Block V) (End: Block V),
      MovingSlotFoldAt S rho t1 M0 s0 (c + 1) F End →
      (∀ j: Slot, c ≤ j → j < c + n → MovingSlotStepSupply S rho t1 M0 j) →
      ∃ (F': Slot → Block V) (End': Block V),
        MovingSlotFoldAt S rho t1 M0 s0 (c + 1 + n) F' End':= by
  intro n
  induction n with
  | zero => intro c F End hfold _; exact ⟨F, End, hfold⟩
  | succ n ih =>
    intro c F End hfold hsupply
    obtain ⟨F1, End1, hfold1, -⟩:=
      hfold.step S adm hcom hfb
        (hsupply c (Nat.le_refl c) (Nat.lt_add_of_pos_right (Nat.succ_pos n)))
        hv
    obtain ⟨F', End', hfold'⟩:= ih (c + 1) F1 End1 hfold1 (by
      intro j hj hjlt
      exact hsupply j ((Nat.le_succ c).trans hj) (nat_lt_shift hjlt))
    exact ⟨F', End', by
      have hshift: c + 1 + 1 + n = c + 1 + (n + 1):= nat_shift_succ c n
      rw [hshift] at hfold'
      exact hfold'⟩
-/






-- form of the two adoption pins `MovingSlotFoldAtN.step_of_slotCone` already




/-- **The adoption data one fold step consumes about the slot it enters**, at
the prior endpoint the step is leaving.

The endpoint is a PARAMETER, not quantified (the corresponding branch). Quantifying it
looked harmless because `MovingSlotFrontierAt.selected` determines the NEW
endpoint, but that is determinacy given the same OLD endpoint; a frontier
record over a different old endpoint is a different premise, and no producer
covers it. The iteration therefore indexes this by the fold state it has
reached, in `iterate_of_supply`, where the endpoint is known.

The honest branch is the general-slot adoption step at the slot being entered:
the proposal builds at or above the window endpoint, every honest slot-`(c + 2)`
vote is above that proposal, and the proposal walk transfers. The Byzantine
branch is the same vote cone above the window endpoint itself.

Both branches also carry the slot-`(c + 1)` CONFIRMATION COMPATIBILITY: every
honest genuine confirmation of the slot the step is leaving is compatible with
the endpoint it is entering. That one is a next-slot fact, not a window fact —
the window facts of `MovingSlotWindowData` speak about slot `s - 1 = c` — so it
cannot come from `hfacts.confirmed`; the corresponding branch found it by compiling the step
. Its producer is the N twin of `MovingSlotPreEntry.confCompatible_honest`
and `.confCompatible_byzantine` (`MovingChainNextEntryRun.lean:474`, `:436`),
and the honest cone is the general-slot adoption step (the corresponding branch, records
w4-gs.md). Nothing here proves either. -/
def MovingSlotAdoptionSupplyAt
    (S : Setup V) (rho : Run V) (c : Slot) (End : Block V) : Prop :=
  (∀ Next : Block V,
      MovingSlotFrontierAt S rho c End Next →
      S.E.proposer (c + 1 + 1) ∈ rho.honest →
      ∀ P : NamedBlock V, proposedBlockAt S rho (c + 1 + 1) = some P →
        Block.Preceq Next (proposedParent S rho (c + 1 + 1)) ∧
        NamedHonestVotesCone S rho (c + 1 + 1)
            (fun X => Block.Preceq P.erase X) ∧
        (∀ w ∈ rho.honest, ∃ tree₀ : Finset (Block V),
          Proofs.Optimistic.NamedVoteStoreExtends S rho w (c + 1 + 1) tree₀
            (proposedParent S rho (c + 1 + 1)) P) ∧
        (∀ w ∈ rho.honest, ∀ D : Block V,
          GenuineConfirmationWith
            (NamedProfile.gradeContract
              (confirmationInputRead S rho w (c + 1)).cache)
            S.E S.hc (Proofs.Optimistic.confStore S rho w (c + 1)) (c + 1) D →
            Block.compatible D P.erase = true))


/-- Two frontier witnesses over the same old endpoint are equal: the record's
`selected` field fixes the new endpoint by `Block.deepest?` on the candidate
set (the corresponding branch's observation). -/
private theorem w4b_frontier_unique
    {S : Setup V} {rho : Run V} {s : Slot} {End A B : Block V}
    (hA : MovingSlotFrontierAt S rho s End A)
    (hB : MovingSlotFrontierAt S rho s End B) : A = B :=
  Option.some.inj (hA.selected.symm.trans hB.selected)

/-- **One step of the named fold**, over the slot-indexed adoption supply.
The missing `MovingSlotFoldAtN.step` of the parked iteration, in the only form
the fold can have until the general-slot adoption step lands. -/
theorem MovingSlotFoldAtN.step_of_supply
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {t1 : Time} {M0 : Height} {s0 c : Slot} {F : Slot → Block V}
    {End : Block V}
    (hfold : MovingSlotFoldAtN S rho t1 M0 s0 (c + 1) F End)
    (hsupply : MovingSlotStepSupply S rho t1 M0 c)
    {v : V} (hv : v ∈ rho.honest)
    (hadopt : MovingSlotAdoptionSupplyAt S rho c End) :
    ∃ (F' : Slot → Block V) (End' : Block V),
      MovingSlotFoldAtN S rho t1 M0 s0 (c + 1 + 1) F' End' ∧
        ∀ d : Slot, d ≤ c + 1 → F' d = F d := by
  obtain ⟨hdata, htiming, hdata'⟩ := hsupply
  obtain ⟨r, hround, ht1, hpostAction, hcut⟩ := hdata.round
  obtain ⟨r', hround', ht1', hpostAction', hcut'⟩ := hdata'.round
  obtain ⟨Next, hfrontier, hfacts⟩ :=
    hfold.entry.windowFacts S adm hcom hfb hdata.pos hround ht1 hpostAction
      hcut hdata.postVote hdata.postProp hdata.slotHor htiming
  refine MovingSlotFoldAtN.step_of_slotCone S adm hcom hfb hfold
    ⟨hdata, htiming, hdata'⟩ hv hadopt ?_
  intro N' hfrontier' hbyz
  have hNN : N' = Next := w4b_frontier_unique hfrontier' hfrontier
  subst hNN
  have hhorSC : Protocol.support_cutoff S.E (c + 1) ≤ rho.horizon :=
    (support_cutoff_le_confirmation_time S.E (c + 1)).trans hdata'.slotHor
  have hpre := MovingSlotEntryStateN.nextPreEntry_byzantine S adm hcom hfb
    hfold.entry hdata.pos hround ht1 hpostAction hcut hdata.postVote
    hdata.postProp hdata.slotHor hfrontier' hfacts hbyz hv hhorSC
  exact hpre.votesCone_prev S adm hcom hfb (Nat.succ_pos c) hround' ht1'
    hpostAction' hcut' hdata'.postVote hdata'.slotHor

/-- **The named fold, iterated.**

`n` slots of schedule supply and of adoption supply carry the named fold `n`
slots forward. This is the parked `MovingSlotFoldAtN.iterate` body verbatim,
with the adoption supply threaded beside the schedule supply; the induction
itself is unchanged. -/
theorem MovingSlotFoldAtN.iterate_of_supply
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {t1 : Time} {M0 : Height} {s0 : Slot}
    {v : V} (hv : v ∈ rho.honest) :
    ∀ (n : Nat) (c : Slot) (F : Slot → Block V) (End : Block V),
      MovingSlotFoldAtN S rho t1 M0 s0 (c + 1) F End →
      (∀ j : Slot, c ≤ j → j < c + n →
        MovingSlotStepSupply S rho t1 M0 j) →
      (∀ (j : Slot) (F' : Slot → Block V) (End' : Block V),
        c ≤ j → j < c + n →
        MovingSlotFoldAtN S rho t1 M0 s0 (j + 1) F' End' →
        MovingSlotAdoptionSupplyAt S rho j End') →
      ∃ (F' : Slot → Block V) (End' : Block V),
        MovingSlotFoldAtN S rho t1 M0 s0 (c + 1 + n) F' End' := by
  intro n
  induction n with
  | zero => intro c F End hfold _ _; exact ⟨F, End, hfold⟩
  | succ n ih =>
    intro c F End hfold hsupply hadopt
    obtain ⟨F1, End1, hfold1, -⟩ :=
      hfold.step_of_supply S adm hcom hfb
        (hsupply c (Nat.le_refl c) (Nat.lt_add_of_pos_right (Nat.succ_pos n)))
        hv
        (hadopt c F End (Nat.le_refl c)
          (Nat.lt_add_of_pos_right (Nat.succ_pos n)) hfold)
    obtain ⟨F', End', hfold'⟩ := ih (c + 1) F1 End1 hfold1
      (by
        intro j hj hjlt
        exact hsupply j ((Nat.le_succ c).trans hj) (nat_lt_shift hjlt))
      (by
        intro j F' End' hj hjlt hfold'
        exact hadopt j F' End' ((Nat.le_succ c).trans hj)
          (nat_lt_shift hjlt) hfold')
    exact ⟨F', End', by
      have hshift : c + 1 + 1 + n = c + 1 + (n + 1) := nat_shift_succ c n
      rw [hshift] at hfold'
      exact hfold'⟩

#print axioms MovingSlotFoldAtN.step_of_slotCone
#print axioms MovingSlotFoldAtN.step_of_supply
#print axioms MovingSlotFoldAtN.iterate_of_supply

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
