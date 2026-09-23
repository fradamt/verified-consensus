module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Objects.W4GeneralSlotAdoption
public import DecoupledConsensusProofs.Protocol.Schedule.W4ConfCompatibleHonest

@[expose] public section

/-!
# The named slot fold, iterated pin-free (W4 branches b)

`MovingChainIterateRun` carries the fold over an adoption PIN: its
`MovingSlotFoldAtN.step_of_supply` and `.iterate_of_supply` take
`MovingSlotAdoptionSupplyAt` as a hypothesis, indexed by the fold state whose
endpoint it speaks about. This leaf discharges that hypothesis and lands the
unparked `MovingSlotFoldAtN.iterate` (design note) with no adoption input.

The discharge is a join of two available producers over one shared frontier:

* the corresponding branch's `movingSlotAdoptionSupplyAt_of_generalSlot`
  (`W4GeneralSlotAdoptionRun`) closes the parent, the slot vote cone and the
  proposal walk, and leaves the slot's confirmation compatibility open;
* this result's `MovingSlotPreEntryN.confCompatible_honest_closed`
  (`W4ConfCompatibleHonestRun`) closes that last conjunct, but reads a
  PRE-entry at the slot being ENTERED. h2's consumer does not hold one; the
  fold step builds it. So the join happens here, where both the entry state and
  the frontier are in hand.

The leaf sits above both because the moving-chain tree cannot import a W4 leaf:
`W4GeneralSlotAdoptionRun` already imports `MovingChainIterateRun`, so the
discharge in place would be an import cycle. Adding it here is additive
(R119a): nothing under the moving-chain tree changes.

The ceiling-side schedule data is genuinely extra input. `MovingSlotWindowData`
(`t1`-indexed, what the fold step already consumes) and `MovingSlotWindowDataC`
(endpoint-indexed, what the general-slot family consumes) are NOT
interderivable: the plain record carries `t1 ≤ S.a r` and the C record carries
instead the honest SG-ancestor clause at that round. Both are therefore taken.
-/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Internal.NamedRecoveryRead
open Internal.PhaseGrades
open Protocol
open Proofs.HealingLemmas
open Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}

/-- **The ceiling-side schedule data one fold step consumes**, at the endpoint
the step is leaving: the C window record of the slot being left, its action
ceiling, and the ordinary `t1`-indexed window record of the slot being entered,
all over the same `Prev`. This is exactly the triple
`movingSlotAdoptionSupplyAt_of_generalSlot` and
`movingSlotAdoptionParent_of_ordinary` read. -/
def MovingSlotCeilingSupplyAt (S : Setup V) (rho : Run V) (t1 : Time)
    (M0 : Height) (c : Slot) (Prev : Block V) : Prop :=
  MovingSlotWindowDataC S rho M0 c Prev ∧
    MovingSlotActionCeiling S rho c Prev ∧
    MovingSlotWindowData S rho t1 M0 (c + 1)

/-- Two frontier witnesses over the same old endpoint are equal (the `selected`
field fixes the new endpoint by `Block.deepest?`). A private twin of
`MovingChainIterateRun`'s `w4b_frontier_unique`, which is module-private. -/
private theorem w4b_frontier_unique'
    {S : Setup V} {rho : Run V} {s : Slot} {End A B : Block V}
    (hA : MovingSlotFrontierAt S rho s End A)
    (hB : MovingSlotFrontierAt S rho s End B) : A = B :=
  Option.some.inj (hA.selected.symm.trans hB.selected)


/-- **The adoption supply of one fold step, discharged.**

Given the fold state at `c + 1` and the schedule data of the step, all four
conjuncts of `MovingSlotAdoptionSupplyAt` hold at the state's own endpoint.

The proof fixes the frontier once: the entry state's `windowFacts` produces a
frontier witness, the supply's quantified `Next` is identified with it by
`w4b_frontier_unique'`, and every downstream producer is then read at that one
witness. The parent conjunct (the corresponding branch's `movingSlotAdoptionParent_of_ceiling`)
is taken first because `nextPreEntry_honest` consumes it, and the pre-entry it
builds is what carries the confirmation-compatibility conjunct. -/
theorem movingSlotAdoptionSupplyAt_of_foldStep
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {t1 : Time} {M0 : Height} {s0 c : Slot} {F : Slot → Block V}
    {End : Block V}
    (hfold : MovingSlotFoldAtN S rho t1 M0 s0 (c + 1) F End)
    (hsupply : MovingSlotStepSupply S rho t1 M0 c)
    (hceil : MovingSlotCeilingSupplyAt S rho t1 M0 c (F (c + 1)))
    {v : V} (hv : v ∈ rho.honest)
    (hdeadline : S.hc.opening_slot
      (fgSafetyProgressDeadline S rho rGST gap delayExtra + 2) ≤ c + 1 + 1)
    (hvoteHor : Protocol.vote_time S.E (c + 1 + 1) ≤ rho.horizon) :
    MovingSlotAdoptionSupplyAt S rho c End := by
  obtain ⟨hdata, htiming, hdataStep⟩ := hsupply
  obtain ⟨hdataC, htimingC, hdataEntered⟩ := hceil
  obtain ⟨r, hround, ht1, hpostAction, hcut⟩ := hdata.round
  obtain ⟨Next0, hfrontier0, hfacts0⟩ :=
    hfold.entry.windowFacts S adm hcom hfb hdata.pos hround ht1 hpostAction
      hcut hdata.postVote hdata.postProp hdata.slotHor htiming
  have hfactsAll : ∀ Next : Block V,
      MovingSlotFrontierAt S rho c End Next →
      NamedMovingSlotWindowFacts S rho (c + 1) End Next := by
    intro Next hf
    rw [w4b_frontier_unique' hf hfrontier0]
    exact hfacts0
  refine movingSlotAdoptionSupplyAt_of_generalSlot S adm hcom hfb hrec hdelay
    hpost hfold.entry hdataC hdataEntered hfactsAll hv hdeadline hvoteHor ?_
  intro Next hfrontier hprop P hP
  have hparent : Block.Preceq Next (proposedParent S rho (c + 1 + 1)) :=
    movingSlotAdoptionParent_of_ordinary S adm hcom hfb hfold.entry hdataC
      htimingC hdataEntered hv Next hfrontier hprop P hP
  obtain ⟨P', hP', hpre⟩ :=
    MovingSlotEntryStateN.nextPreEntry_honest S adm hcom hfb hfold.entry
      hdata hdataEntered hfrontier (hfactsAll Next hfrontier) hprop hparent hv
  have hPP : P' = P := Option.some.inj (hP'.symm.trans hP)
  subst hPP
  obtain ⟨r', hround', ht1', hpostAction', hcut'⟩ := hdataEntered.round
  have hheads : ∀ u ∈ rho.honest,
      voteDutyHead S rho u (c + 1 + 1) = P'.erase :=
    honestProposal_voterHeadAt_eq_after_SG_healing_named_slot
      S adm hcom hfb hrec hdelay hpost hdeadline hvoteHor hprop hP'
  exact hpre.confCompatible_honest_closed S adm hcom hfb (Nat.succ_pos c)
    hround' ht1' hpostAction' hcut' hdataEntered.postVote hdataEntered.postProp
    hdataEntered.slotHor hheads hv


/-- **The named fold, iterated —  UNPARKED, pin-free.**

`n` slots of schedule supply carry the named fold `n` slots forward, with no
adoption input: each step's adoption supply is discharged by
`movingSlotAdoptionSupplyAt_of_foldStep` at the fold state the iteration has
reached.

The ceiling supply is indexed by the fold state, not quantified over endpoints:
`MovingSlotFrontierAt.selected` determines the NEW endpoint only given the same
OLD one, so a record over a different old endpoint is a different premise with
no producer (the corresponding branch). The deadline bound is taken once at `c` and
carried up the range; the vote horizon is per slot because it grows with the
slot. -/
theorem MovingSlotFoldAtN.iterate
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {t1 : Time} {M0 : Height} {s0 : Slot}
    {v : V} (hv : v ∈ rho.honest)
    (n : Nat) (c : Slot) (F : Slot → Block V) (End : Block V)
    (hfold : MovingSlotFoldAtN S rho t1 M0 s0 (c + 1) F End)
    (hsupply : ∀ j : Slot, c ≤ j → j < c + n →
      MovingSlotStepSupply S rho t1 M0 j)
    (hceil : ∀ (j : Slot) (F' : Slot → Block V) (End' : Block V),
      c ≤ j → j < c + n →
      MovingSlotFoldAtN S rho t1 M0 s0 (j + 1) F' End' →
      MovingSlotCeilingSupplyAt S rho t1 M0 j (F' (j + 1)))
    (hdeadline : S.hc.opening_slot
      (fgSafetyProgressDeadline S rho rGST gap delayExtra + 2) ≤ c + 1 + 1)
    (hvoteHor : ∀ j : Slot, c ≤ j → j < c + n →
      Protocol.vote_time S.E (j + 1 + 1) ≤ rho.horizon) :
    ∃ (F' : Slot → Block V) (End' : Block V),
      MovingSlotFoldAtN S rho t1 M0 s0 (c + 1 + n) F' End' := by
  refine MovingSlotFoldAtN.iterate_of_supply S adm hcom hfb hv n c F End hfold
    hsupply ?_
  intro j F' End' hj hjlt hfold'
  exact movingSlotAdoptionSupplyAt_of_foldStep S adm hcom hfb hrec hdelay hpost
    hfold' (hsupply j hj hjlt) (hceil j F' End' hj hjlt hfold') hv
    (le_trans hdeadline (Nat.succ_le_succ (Nat.succ_le_succ hj)))
    (hvoteHor j hj hjlt)

private theorem w4b_nat_shift_succ (c n : Nat) :
    c + 1 + 1 + n = c + 1 + (n + 1) := by
  omega

private theorem w4b_nat_lt_shift {j c n : Nat} (h : j < c + 1 + n) :
    j < c + (n + 1) := by
  omega

/-- **The named fold, iterated with its base family preserved.**
This is the additive companion of `MovingSlotFoldAtN.iterate`. Each
`step_of_supply` already returns equality of the new family with the previous
family below the step cursor; this induction retains that equality instead of
discarding it at the recursive call. -/
theorem MovingSlotFoldAtN.iterate_withBase
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {t1 : Time} {M0 : Height} {s0 : Slot}
    {v : V} (hv : v ∈ rho.honest) :
    ∀ (n : Nat) (c : Slot) (F : Slot → Block V) (End : Block V),
      MovingSlotFoldAtN S rho t1 M0 s0 (c + 1) F End →
      (∀ j : Slot, c ≤ j → j < c + n →
        MovingSlotStepSupply S rho t1 M0 j) →
      (∀ (j : Slot) (F' : Slot → Block V) (End' : Block V),
        c ≤ j → j < c + n →
        MovingSlotFoldAtN S rho t1 M0 s0 (j + 1) F' End' →
        MovingSlotCeilingSupplyAt S rho t1 M0 j (F' (j + 1))) →
      S.hc.opening_slot
        (fgSafetyProgressDeadline S rho rGST gap delayExtra + 2) ≤ c + 1 + 1 →
      (∀ j : Slot, c ≤ j → j < c + n →
        Protocol.vote_time S.E (j + 1 + 1) ≤ rho.horizon) →
      ∃ (F' : Slot → Block V) (End' : Block V),
        MovingSlotFoldAtN S rho t1 M0 s0 (c + 1 + n) F' End' ∧
          ∀ d : Slot, d ≤ c + 1 → F' d = F d := by
  intro n
  induction n with
  | zero =>
      intro c F End hfold _ _ _ _
      exact ⟨F, End, hfold, fun d _ => rfl⟩
  | succ n ih =>
      intro c F End hfold hsupply hceil hdeadline hvoteHor
      obtain ⟨F1, End1, hfold1, hbase1⟩ :=
        hfold.step_of_supply S adm hcom hfb
          (hsupply c (Nat.le_refl c)
            (Nat.lt_add_of_pos_right (Nat.succ_pos n)))
          hv
          (movingSlotAdoptionSupplyAt_of_foldStep S adm hcom hfb hrec hdelay
            hpost hfold
            (hsupply c (Nat.le_refl c)
              (Nat.lt_add_of_pos_right (Nat.succ_pos n)))
            (hceil c F End (Nat.le_refl c)
              (Nat.lt_add_of_pos_right (Nat.succ_pos n)) hfold)
            hv hdeadline
            (hvoteHor c (Nat.le_refl c)
              (Nat.lt_add_of_pos_right (Nat.succ_pos n))))
      obtain ⟨F', End', hfold', hbase'⟩ := ih (c + 1) F1 End1 hfold1
        (fun j hj hjlt =>
          hsupply j ((Nat.le_succ c).trans hj) (w4b_nat_lt_shift hjlt))
        (fun j F2 End2 hj hjlt hf =>
          hceil j F2 End2 ((Nat.le_succ c).trans hj)
            (w4b_nat_lt_shift hjlt) hf)
        (le_trans hdeadline
          (Nat.succ_le_succ (Nat.le_succ (c + 1))))
        (fun j hj hjlt =>
          hvoteHor j ((Nat.le_succ c).trans hj) (w4b_nat_lt_shift hjlt))
      refine ⟨F', End', ?_, ?_⟩
      · have hshift : c + 1 + 1 + n = c + 1 + (n + 1) :=
          w4b_nat_shift_succ c n
        rw [hshift] at hfold'
        exact hfold'
      · intro d hd
        exact (hbase' d (hd.trans (Nat.le_succ (c + 1)))).trans
          (hbase1 d hd)

#print axioms movingSlotAdoptionSupplyAt_of_foldStep
#print axioms MovingSlotFoldAtN.iterate_withBase

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
