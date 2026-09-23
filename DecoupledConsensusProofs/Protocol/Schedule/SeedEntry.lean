module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.SeedBaseCeiling
public import DecoupledConsensusProofs.Protocol.Schedule.MovingChainSupporter
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SeedActivity
public import DecoupledConsensusProofs.Protocol.Grades.SeedFlush
public import DecoupledConsensusProofs.Execution.RecoveryActionCarrierG0Compatibility

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# The entry block of the gate-off seed: the deepest honest action carrier

`SeedBoundaryAdoptionAt` asks for one run block above every honest round-`q`
action carrier and below every honest Goldfish head of the round's last vote
duty. The carrier BOUND set does not supply it: an honest fresh anchor may
conflict with another honest reader's genuine confirmation, and then the anchor
holder's own head conflicts with that confirmation.

The carriers themselves do. Every honest round-`q` fresh anchor — at any read
of the round, not only at the action read — is compatible with every honest
round-`q` action carrier, because the grade-1 anchor is a delivered grade-0
veto at the carrier's own action store and the SG vote is veto free. So at
each vote duty the reader's anchor is on the deepest carrier's chain, and the
two sides of that comparison close the head bound in different ways: below the
anchor the head is above the carrier outright, above the anchor the reader is
captured by the genuine confirmation the carrier sits under.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol
open Proofs.HealingLemmas
open Proofs.Optimistic
open GradeDeliveryRun

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## The deepest honest action carrier -/



/-! ## The action carrier as a run block with a viability witness -/




/-! ## Round-`q` fresh anchors against the round's action carriers -/



/-
/-- **The action-read form of the anchor veto.** A fresh anchor selected at an
honest action read of round `q` is compatible with every honest round-`q`
action carrier.

Either the anchor is below the reader's own selected FG root, and the reader's
carrier is above that root; or it is active at the reader, where it is stamped
before the veto freeze and holds the delivered grade 0, and the SG vote of a
store with a selected grade 2 is veto free. -/
theorem seedActionFreshAnchor_compatible_actionCarrier
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hfb: BelowOneThird S rho.honest)
    {q: Round}
    (hready: GradeRoundReady S rho q)
    (hg1: LiveG1SettledAt S rho q)
    (hselected: ∀ v ∈ rho.honest, ∃ Q: Block V,
      Protocol.grade2_block S.E S.hc
        (actionStoreAt S rho v q).toHealing q = some Q)
    {w: V} (hw: w ∈ rho.honest) {A: Block V}
    (hA: Protocol.fresh_anchor S.E S.hc
      (actionStoreAt S rho w q).toHealing q = some A)
    {v: V} (hv: v ∈ rho.honest):
    Block.compatible A (actionSGBlockAt S rho v q) = true:= by
  have hG1Action: Protocol.G1 S.E
      (actionStoreAt S rho w q).toHealing.gradeView S.hc q A = true:=
    (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hA)).2
  have hG1: Protocol.G1 S.E (gradeViewAt S rho w q) S.hc q A = true:= by
    rw [gradeViewAt, healStoreAt,
      ← Protocol.actionStoreAt_gradeView_eq_storeBeforeTime S rho w q]
    exact hG1Action
  rcases hg1 w hw A hG1 v hv with hroot | hactive
  · have hrootAction: Block.Preceq A
        (Protocol.get_fg_root
          (actionStoreAt S rho v q).toHealing.toFG):= by
      rw [actionStoreAt_fgRoot_eq_storeBeforeTime S rho v q]
      exact hroot
    simp only [Block.compatible, Bool.or_eq_true]
    exact Or.inl (Block.preceq_trans hrootAction
      (actionFGRoot_preceq_actionSGBlockAt S rho v q))
  · obtain ⟨Q, hQ⟩:= hselected v hv
    have hactiveAction: A ∈ Protocol.get_filtered_block_tree
        (actionStoreAt S rho v q).toHealing.toFG:= by
      rw [actionStoreAt_filteredTree S rho v q]
      exact hactive
    have hAread: Protocol.fresh_anchor S.E S.hc
        (healStoreAt S rho w q) q = some A:= by
      simpa only [Protocol.fresh_anchor, healStoreAt,
        actionStoreAt_filteredTree S rho w q,
        Protocol.actionStoreAt_gradeView_eq_storeBeforeTime S rho w q]
        using hA
    have hstamp:= anchorVisible_of_admissible S adm hfb hready
      w hw A hAread v hv hactive
    have hstampAction: stampedBefore
        (actionStoreAt S rho v q).toHealing.gradeView.timestamp_block
        (S.hc.Γ_1 S.E.Δ q) A = true:= by
      rw [Protocol.actionStoreAt_gradeView_eq_storeBeforeTime S rho v q]
      simpa only [gradeViewAt, healStoreAt] using hstamp
    have hdelivery:= honestGradeDelivery_of_admissible S adm hready
    have hG0: Protocol.G0 S.E
        (actionStoreAt S rho v q).toHealing.gradeView S.hc q A = true:= by
      rw [Protocol.actionStoreAt_gradeView_eq_storeBeforeTime S rho v q]
      exact G1_imp_G0_delivered S.E (hdelivery w hw v hv) hactive hG1
    simpa only [actionSGBlockAt] using
      recoveryActionCarrier_compatible_of_g0 S.E hQ hactiveAction hstampAction
        hG0
-/


/-
/-- **The anchor veto at any read of the round.** A fresh anchor of round `q`
selected at any honest read at or after the round's grade-zero cutoff is
compatible with every honest round-`q` action carrier.

The grade is frozen at that cutoff, so the anchor holds the same grade 1 at its
holder's own action read. There it is either below the holder's selected FG
root — and a gate-off root is compatible with every carrier — or active, and
then it is dominated by the holder's own action anchor, which the action-read
veto settles. -/
theorem seedRoundAnchor_compatible_actionCarrier
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hfb: BelowOneThird S rho.honest)
    {M: Height} {q: Round}
    (hready: GradeRoundReady S rho q)
    (hg1: LiveG1SettledAt S rho q)
    (hselected: ∀ v ∈ rho.honest, ∃ Q: Block V,
      Protocol.grade2_block S.E S.hc
        (actionStoreAt S rho v q).toHealing q = some Q)
    (hfrontier: ∀ u ∈ rho.honest,
      (rho.storeBeforeTime S u (S.a q)).h_max = M)
    (hgate: ∀ u ∈ rho.honest,
      (rho.storeBeforeTime S u (S.a q)).h_j + 2 ≤ M)
    {w: V} (hw: w ∈ rho.honest) {t: Time}
    (hcut: S.hc.Γ_0 S.E.Δ q ≤ t) {A: Block V}
    (hA: Protocol.fresh_anchor S.E S.hc
      (rho.storeBeforeTime S w t).toHealing q = some A)
    {v: V} (hv: v ∈ rho.honest):
    Block.compatible A (actionSGBlockAt S rho v q) = true:= by
  have hsb: SlashableBound S rho:=
    slashableBound_of_admissible_belowOneThird S adm hfb
  have hG1t: Protocol.G1 S.E
      (rho.storeBeforeTime S w t).toHealing.gradeView S.hc q A = true:=
    (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hA)).2
  have hG1: Protocol.G1 S.E (gradeViewAt S rho w q) S.hc q A = true:= by
    rw [gradeViewAt, healStoreAt]
    rcases le_total t (S.a q) with hle | hle
    · exact G1_persists_after_cutoff S adm hw hcut hle hG1t
    · exact G1_reflects_after_cutoff S adm hw
        (seedEntryGamma0_le_action S q) hle hG1t
  rcases hg1 w hw A hG1 w hw with hroot | hactive
  · refine lowerBlock_compatible_carrier_of_oneChain hroot ?_
    have h:= actionFGRoot_compatible_actionCarrier_of_gateOff S adm hsb
      hfrontier hgate hw hv
    rwa [actionStoreAt_fgRoot_eq_storeBeforeTime S rho w q] at h
  · have hactiveAction: A ∈ Protocol.get_filtered_block_tree
        (actionStoreAt S rho w q).toHealing.toFG:= by
      rw [actionStoreAt_filteredTree S rho w q]
      exact hactive
    have hG1Action: Protocol.G1 S.E
        (actionStoreAt S rho w q).toHealing.gradeView S.hc q A = true:= by
      rw [Protocol.actionStoreAt_gradeView_eq_storeBeforeTime S rho w q]
      simpa only [gradeViewAt, healStoreAt] using hG1
    obtain ⟨A', hA'⟩:= Option.isSome_iff_exists.mp
      (fresh_anchor_isSome_of_G1 S.E hactiveAction hG1Action)
    have hAA': Block.Preceq A A':= by
      refine deepest?_dominates hA'
        (Finset.mem_filter.mpr ⟨hactiveAction, hG1Action⟩) ?_
      exact G1_compatible S.E hG1Action
        (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hA')).2
    exact lowerBlock_compatible_carrier_of_oneChain hAA'
      (seedActionFreshAnchor_compatible_actionCarrier S adm hfb hready hg1
        hselected hw hA' hv)
-/

/-! ## The slots and anchors of one round -/

/-- The slots strictly after a round's opening and at or before its last slot
belong to that round. -/
theorem seedEntryRoundOf (S : Setup V) {q : Round} {d : Slot}
    (hlo : S.hc.opening_slot q + 1 ≤ d) (hhi : d ≤ seedRoundLastSlot S q) :
    S.hc.round_of d = q := by
  refine round_of_eq_of_opening_succ_le_of_lt_next_opening S.hc hlo ?_
  refine lt_of_le_of_lt hhi ?_
  unfold seedRoundLastSlot
  have hpos : 0 < S.hc.opening_slot (q + 1) := by
    unfold Protocol.HealConfig.opening_slot
    exact Nat.mul_pos (Nat.succ_pos q)
      (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
  exact Nat.sub_lt hpos Nat.zero_lt_one

/-- Every slot of round `q` is in round `q`. -/
theorem seedEntryRoundOf' (S : Setup V) {q : Round} {d : Slot}
    (hlo : S.hc.opening_slot q ≤ d) (hhi : d ≤ seedRoundLastSlot S q) :
    S.hc.round_of d = q := by
  rcases Nat.eq_or_lt_of_le hlo with heq | hlt
  · rw [← heq]
    simp only [Protocol.HealConfig.round_of, Protocol.HealConfig.opening_slot]
    exact Nat.mul_div_left q
      (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
  · exact seedEntryRoundOf S hlt hhi




/-! ## Cross-round: round-`q` grades against the round-`(q-1)` bounds -/






/-- **Open — the one open comparison of the gate-off seed base**, stated
at exactly the read where the proof needs it.

The obligation is only at a MIDDLE-CASE read: an honest vote duty of round `q`
that holds no fresh grade-1 anchor AND whose SG root is not the fork-choice
root, so the relative-majority walk moved without a grade. At every other read
the comparison is proved: with a fresh anchor the grade-0 veto settles it
(`seedRoundAnchor_compatible_actionCarrier`), and with a collapsed root the
gate-off root is below the carrier's own viability witness
(`seedRoundAnchor_compatible_of_rootAbovePreviousCarriers`).

Its content is one selector tier. Three of the four round-`q` SG tiers are
proved against the round-`(q-1)` bounds by
`seedActionCarrier_compatible_previousBound`: a selected grade 2 and a raw fresh
anchor are grade-1 blocks of round `q`, so their own provenance carrier and the
bound chain place them (`seedRoundG1_compatible_previousBound`), and a store
that fell back to its fork-choice root carries that root, which gate off puts
below every run block of the frontier band. What is left is the CLEAR-WALK
tier under a genuine confirmation of slot `opening q`: the walk climbs from the
round-`q` SG root, which is itself compatible with the previous bounds, towards
a confirmation that nothing bounds from above. Both sit under run blocks of the
band, and two band blocks may conflict, so ordering them is the round-`(q-1)`
boundary cone — the ceiling the base is constructing — hence a regress
(log.md 06:25, 06:33, 06:41).

**Selected failure candidate, and what the available arms do and do not exclude.**
Take the §6 split: Byzantine round-`(q-1)` SG votes delivered selectively, a
genuine confirmation of slot `opening (q-1)` tipped onto one branch, and an
honest round-`q` opening proposal confirmed on the other, so a round-`q`
clear-walk carrier conflicts with that round-`(q-1)` bound.

* If the split leaves NO grade above the fork, the scenario contradicts the
  other named residual rather than this one: with no grade-2 block at the
  honest round-`q` action stores, `SeedRoundGradedAt.selected` fails. It is
  excluded by hypothesis, not by a theorem.
* If a grade DOES survive above the fork, the grade windows exclude conflicting
  grade-1 blocks, so every honest fresh anchor is on one branch — but a duty
  read whose fork-choice root has passed that grade holds no fresh anchor, and
  its relative-majority walk can still leave the root onto the other branch on
  selectively delivered Byzantine votes, because `Protocol.supports` has no
  equivocation sweep beyond the per-store `sole_vote?` and no `Γ` cutoff at all.
  The available collapse and counting arms do NOT exclude that: the counting only
  says the walk cannot move when NO honest round-`(q-1)` carrier is above the
  root.

So this is a genuine protocol-level assumption, of the same kind as the
finality track's one-height premise, and not a bookkeeping gap. It is vacuous
at every duty where the round's selected grade-2 block is still active — the
duty-read analogue of `SelectedG2SettledAt` — which is the natural way to
discharge it. -/
def SeedClearCarrierCompatiblePreviousAt
    (S : Setup V) (rho : Run V) (q : Round) : Prop :=
  ∀ d : Slot, S.hc.opening_slot q ≤ d → d ≤ seedRoundLastSlot S q →
    ∀ w ∈ rho.honest,
      Protocol.fresh_anchor S.E S.hc
          (voteDutyStore S rho w d).toHealing q = none →
      voterAnchorAt S rho w d ≠
          Protocol.get_fg_root
            (voteDutyStore S rho w d).toHealing.toFG →
      ∀ v ∈ rho.honest,
        Block.compatible
          (voterAnchorAt S rho w d)
          (actionSGBlockAt S rho v q) = true


/-
/-- **Every honest round-`q` action carrier is on the chain of every
round-`(q-1)` carrier bound**, modulo the one open tier. Three of the four
selector tiers close outright; the fourth is the named residual. -/
theorem seedActionCarrier_compatible_previousBound
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hfb: BelowOneThird S rho.honest)
    {M: Height} {q: Round} (hq: 0 < q)
    (hreadyPrev: GradeRoundReady S rho (q - 1))
    (hsettledPrev: SelectedG2SettledAt S rho (q - 1))
    (hselectedPrev: ∀ v ∈ rho.honest, ∃ Q: Block V,
      Protocol.grade2_block S.E S.hc
        (actionStoreAt S rho v (q - 1)).toHealing (q - 1) = some Q)
    (hselected: ∀ v ∈ rho.honest, ∃ Q: Block V,
      Protocol.grade2_block S.E S.hc
        (actionStoreAt S rho v q).toHealing q = some Q)
    (hpostPrev: S.E.t_GST ≤ S.a (q - 1))
    (hprevHor: S.a (q - 1) + S.E.Δ ≤ rho.horizon)
    (hprevDelta: S.a (q - 1) + S.E.Δ ≤ S.a q)
    (hopenPost: S.E.t_GST ≤
      Protocol.proposal_time S.E (S.hc.opening_slot (q - 1)))
    (hopenHor: Protocol.confirmation_time S.E
      (S.hc.opening_slot (q - 1)) ≤ rho.horizon)
    (hfrontierPrev: ∀ u ∈ rho.honest,
      (rho.storeBeforeTime S u (S.a (q - 1))).h_max = M)
    (hgatePrev: ∀ u ∈ rho.honest,
      (rho.storeBeforeTime S u (S.a (q - 1))).h_j + 2 ≤ M)
    (hfrontier: ∀ u ∈ rho.honest,
      (rho.storeBeforeTime S u (S.a q)).h_max = M)
    (hgate: ∀ u ∈ rho.honest,
      (rho.storeBeforeTime S u (S.a q)).h_j + 2 ≤ M)
    (hclear: ∀ v ∈ rho.honest, ∀ T: Block V,
      Protocol.deepest_clear
          (some (Protocol.get_sg_root S.E S.hc
            (actionStoreAt S rho v q).toHealing q))
          (actionStoreAt S rho v q).toHealing.live_confirmed
          (fun X => Protocol.g0_clear S.E
            (actionStoreAt S rho v q).toHealing.gradeView S.hc q X) = some T →
        (∃ D: Block V, GenuineConfirmation (contract:= Protocol.GradeContract.current) S.E S.hc
          (Proofs.Optimistic.confStore S rho v (S.hc.opening_slot q))
          (S.hc.opening_slot q) D) →
        ∀ B ∈ seedCarrierBounds S rho (q - 1), Block.compatible B T = true)
    {v: V} (hv: v ∈ rho.honest)
    {B: Block V} (hB: B ∈ seedCarrierBounds S rho (q - 1)):
    Block.compatible B (actionSGBlockAt S rho v q) = true:= by
  have hsb: SlashableBound S rho:=
    slashableBound_of_admissible_belowOneThird S adm hfb
  obtain ⟨Q, hQ⟩:= hselected v hv
  rcases actionSGBlockAt_clear_or_selectedG2 S rho hQ with
    ⟨T, hwalk, hcarrier⟩ | hcarrier
  · rcases actionStoreAt_liveConfirmed_genuine_or_fgRoot S rho v q with
      ⟨D, hD, hDeq⟩ | ⟨R, hReq, hRlive⟩
    · rw [hcarrier]
      exact hclear v hv T hwalk ⟨D, hD⟩ B hB
    · -- the store fell back to its own fork-choice root
      have hclear: Block.Preceq (actionSGBlockAt S rho v q)
          (actionStoreAt S rho v q).live_confirmed:= by
        rw [hcarrier]
        exact Proofs.Engine.deepest_clear_preceq hwalk
      have hTroot: T = Protocol.get_fg_root
          (actionStoreAt S rho v q).toHealing.toFG:=
        clearCarrier_eq_actionFGRoot_of_rootSource S rho hcarrier
          (by rw [← hcarrier]; exact hclear) hReq hRlive
      obtain ⟨W, hWrun, hBW, hWthin⟩:=
        seedCarrierBounds_thinWitness S adm hfrontierPrev hB
      rw [hcarrier, hTroot, actionStoreAt_fgRoot_eq_storeBeforeTime S rho v q]
      exact Protocol.compatible_comm
        (Block.compatible_of_preceq_common
          (frontierRoot_preceq_of_gateOff S adm hsb hv hWrun hWthin
            (hfrontier v hv) (hgate v hv)) hBW)
  · -- the selected grade 2 is a round-`q` grade-1 block
    have hQG2: Protocol.G2 S.E
        (actionStoreAt S rho v q).toHealing.gradeView S.hc q Q = true:=
      (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hQ)).2
    have hQG1: Protocol.G1 S.E
        (rho.storeBeforeTime S v (S.a q)).toHealing.gradeView S.hc q Q =
          true:= by
      rw [← Protocol.actionStoreAt_gradeView_eq_storeBeforeTime S rho v q]
      exact G2_imp_G1 S.E _ S.hc q Q hQG2
    rw [hcarrier]
    exact Protocol.compatible_comm
      (seedRoundG1_compatible_previousBound S adm hfb hq hreadyPrev
        hsettledPrev hselectedPrev hpostPrev hprevHor hopenPost hopenHor
        hfrontierPrev hgatePrev hv hprevDelta hQG1 hB)
-/

/-! ## The reveal case: the SG root collapses to the fork-choice root -/



/-
/-- **The reveal case.** When a released certificate moves an honest reader's
fork-choice root at or above every honest round-`(q-1)` action carrier, that
reader's round-`q` SG root IS the fork-choice root: no child of the root
carries a majority of the previous round's SG votes, so the relative-majority
walk cannot leave it, and a fresh grade-1 anchor cannot sit above it either.

This is why a reveal is favourable rather than harmful. The collapsed anchor
is the gate-off root, which is below every run block of the frontier band. -/
theorem seedRoundAnchor_eq_fgRoot_of_rootAbovePreviousCarriers
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hfb: BelowOneThird S rho.honest)
    {q: Round} (hq: 0 < q)
    (hpost: S.E.t_GST ≤ S.a (q - 1))
    (hcut: S.hc.Γ_neg1 S.E.Δ q ≤ rho.horizon)
    {w: V} (hw: w ∈ rho.honest) {t: Time}
    (hread: S.hc.Γ_0 S.E.Δ q ≤ t)
    (habove: ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u (q - 1))
        (Protocol.get_fg_root
          (rho.storeBeforeTime S w t).toHealing.toFG)):
    Protocol.get_sg_root S.E S.hc (rho.storeBeforeTime S w t).toHealing q =
      Protocol.get_fg_root
        (rho.storeBeforeTime S w t).toHealing.toFG:= by
  have hqPred: q - 1 + 1 = q:= Nat.sub_add_cancel (Nat.succ_le_of_lt hq)
  have hdep: DepReachableStore S.E S.hc S.cfg (S.node w)
      (rho.storeBeforeTime S w t):= by
    simpa only [Run.storeBeforeTime] using
      (Proofs.Bridges.depReachable_stateBeforeTime S adm.toScheduleWellFormed
        adm.toDeliveryWellFormed t w)
  have hrootMem: Protocol.get_fg_root
      (rho.storeBeforeTime S w t).toHealing.toFG ∈
        (rho.storeBeforeTime S w t).T:=
    Proofs.Records.get_filtered_block_tree_subset _
      (fgRoot_mem_filtered_depReachable S.E S.hc S.cfg (S.node w) hdep)
  have hle:= readAnchor_preceq_step S adm hfb (r:= q - 1) (t:= t)
    hpost (by rw [hqPred]; exact hcut) (by rw [hqPred]; exact hread) hw
    hrootMem (Block.preceq_self _) habove
  rw [hqPred] at hle
  exact Block.preceq_antisymm hle
    (seedFgRoot_preceq_roundAnchor S (rho.storeBeforeTime S w t) q)
-/


/-
/-- The collapsed anchor is compatible with every block of the frontier band,
so it needs no veto argument at all. -/
theorem seedRoundAnchor_compatible_of_rootAbovePreviousCarriers
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hfb: BelowOneThird S rho.honest)
    {M: Height} {q: Round} (hq: 0 < q)
    (hpost: S.E.t_GST ≤ S.a (q - 1))
    (hcut: S.hc.Γ_neg1 S.E.Δ q ≤ rho.horizon)
    {w: V} (hw: w ∈ rho.honest) {t: Time}
    (hread: S.hc.Γ_0 S.E.Δ q ≤ t)
    (hfrontier: (rho.storeBeforeTime S w t).h_max = M)
    (hgate: (rho.storeBeforeTime S w t).h_j + 2 ≤ M)
    (habove: ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u (q - 1))
        (Protocol.get_fg_root
          (rho.storeBeforeTime S w t).toHealing.toFG))
    {C W: Block V} (hWrun: RunBlock S rho W) (hCW: Block.Preceq C W)
    (hWthin: M - 1 ≤ (derived_state S.E S.cfg W).h):
    Block.compatible
      (Protocol.get_sg_root S.E S.hc
        (rho.storeBeforeTime S w t).toHealing q) C = true:= by
  have hsb: SlashableBound S rho:=
    slashableBound_of_admissible_belowOneThird S adm hfb
  rw [seedRoundAnchor_eq_fgRoot_of_rootAbovePreviousCarriers S adm hfb hq
    hpost hcut hw hread habove]
  exact Block.compatible_of_preceq_common
    (frontierRoot_preceq_of_gateOff S adm hsb hw hWrun hWthin hfrontier hgate)
    hCW
-/


/-
/-- **The round's SG roots against the PREVIOUS round's carrier frontier.**
At every honest read of round `q` the SG root is at or below a block that
dominates every honest round-`(q-1)` action carrier, or it is the fork-choice
root itself.

The two arms are the two positions of the read's root against that frontier,
and they are comparable because both lie under the frontier's own viability
witness. Below it, the relative-majority walk cannot leave the frontier's
chain (`readAnchor_preceq_step`): every previous-round carrier that supports a
child of the root lies on that segment. Above it, the root has already passed
every previous-round carrier, so no child of the root carries a majority and
the walk collapses. -/
theorem seedRoundAnchor_preceq_previousFrontier_or_eq_fgRoot
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hfb: BelowOneThird S rho.honest)
    {M: Height} {q: Round} (hq: 0 < q)
    (hpost: S.E.t_GST ≤ S.a (q - 1))
    (hcut: S.hc.Γ_neg1 S.E.Δ q ≤ rho.horizon)
    {w: V} (hw: w ∈ rho.honest) {t: Time}
    (hread: S.hc.Γ_0 S.E.Δ q ≤ t)
    (hfrontier: (rho.storeBeforeTime S w t).h_max = M)
    (hgate: (rho.storeBeforeTime S w t).h_j + 2 ≤ M)
    {Cprev W: Block V}
    (hWrun: RunBlock S rho W) (hCW: Block.Preceq Cprev W)
    (hWthin: M - 1 ≤ (derived_state S.E S.cfg W).h)
    (hmem: Cprev ∈ (rho.storeBeforeTime S w t).T)
    (hupper: ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u (q - 1)) Cprev):
    Block.Preceq
        (Protocol.get_sg_root S.E S.hc
          (rho.storeBeforeTime S w t).toHealing q) Cprev ∨
      Protocol.get_sg_root S.E S.hc
          (rho.storeBeforeTime S w t).toHealing q =
        Protocol.get_fg_root
          (rho.storeBeforeTime S w t).toHealing.toFG:= by
  have hsb: SlashableBound S rho:=
    slashableBound_of_admissible_belowOneThird S adm hfb
  have hqPred: q - 1 + 1 = q:= Nat.sub_add_cancel (Nat.succ_le_of_lt hq)
  have hrootW: Block.Preceq
      (Protocol.get_fg_root (rho.storeBeforeTime S w t).toHealing.toFG)
      W:=
    frontierRoot_preceq_of_gateOff S adm hsb hw hWrun hWthin hfrontier hgate
  have hcompat: Block.compatible
      (Protocol.get_fg_root (rho.storeBeforeTime S w t).toHealing.toFG)
      Cprev = true:= Block.compatible_of_preceq_common hrootW hCW
  simp only [Block.compatible, Bool.or_eq_true] at hcompat
  rcases hcompat with hrootPrev | hprevRoot
  · -- the root is below the previous frontier: the walk stays on its chain
    left
    have hle:= readAnchor_preceq_step S adm hfb (r:= q - 1) (t:= t)
      hpost (by rw [hqPred]; exact hcut) (by rw [hqPred]; exact hread) hw
      hmem hrootPrev hupper
    rwa [hqPred] at hle
  · -- the root has passed the previous frontier: the walk collapses
    right
    refine seedRoundAnchor_eq_fgRoot_of_rootAbovePreviousCarriers S adm hfb hq
      hpost hcut hw hread ?_
    intro u hu
    exact Block.preceq_trans (hupper u hu) hprevRoot
-/

/-! ## The head floor from a frozen witness above the anchor -/


/-
/-- **The frozen head floor.** A frozen-processed block of the frontier band
above the duty's own SG root puts the duty's Goldfish head in the band, with no
candidate-path input and no fresh anchor.

Every step strictly below the band is eligible for free
(`goldfish_eligible_iff`'s height arm), and the child towards the witness is a
frozen candidate (`frozenCandidate_child_towards_witness` when the walk already
left the anchor, `ancestorCandidate_of_processedDescendant_and_hMax` when it did
not), so a head below the band contradicts
`eligible_child_false_at_ghost_result`. -/
theorem seedVoteDutyHead_thin_of_frozenWitness
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    {w: V} (hw: w ∈ rho.honest) {s: Slot} {Z: Block V}
    (hZfrozen: Z ∈ Protocol.voter_processed_block_tree S.E
      (voteDutyStore S rho w (s + 1)).toHealing.toFG.toSG.toGoldfishStore
      (voteDutyStore S rho w (s + 1)).toHealing.s)
    (hZheight: (voteDutyStore S rho w (s + 1)).h_max - 1 ≤
      ((voteDutyStore S rho w (s + 1)).σ Z).h)
    (hanchorZ: Block.Preceq
      (Proofs.Optimistic.healAnchor S.E S.hc
        (voteDutyStore S rho w (s + 1)).toHealing) Z):
    (voteDutyStore S rho w (s + 1)).h_max - 1 ≤
      (derived_state S.E S.cfg (voteDutyHead S rho w (s + 1))).h:= by
  let duty:= Proofs.Optimistic.voteDutyStore S rho w (s + 1)
  let tree:= Proofs.Optimistic.voter_candidate_tree S.E duty.toHealing
  let A:= Proofs.Optimistic.healAnchor S.E S.hc duty.toHealing
  let score:= Protocol.goldfish_score S.E duty.T
    (Protocol.voter_view S.E duty.toHealing.toFG.toSG.toGoldfishStore duty.s)
    (Protocol.voter_support_view S.E duty.toHealing.toFG.toSG.toGoldfishStore duty.s) (duty.s - 1)
  let eligible:= Protocol.goldfish_eligible S.E duty.σ duty.h_max duty.T
    duty.s (Protocol.voter_view S.E duty.toHealing.toFG.toSG.toGoldfishStore duty.s)
    (Protocol.voter_support_view S.E duty.toHealing.toFG.toSG.toGoldfishStore duty.s) (duty.s - 1)
  let H:= voteDutyHead S rho w (s + 1)
  have hHghost: H = Protocol.ghost A tree score eligible:= rfl
  have hfacts:= voteDuty_parentClosed_agrees_rootInjective S adm hw (s + 1)
  have hpc: ParentClosed duty:= hfacts.1
  have hagree: DerivedStateAgrees S.E S.cfg duty:= hfacts.2.1
  have htreeT: tree ⊆ duty.T:= by
    intro B hB
    have hprocessed:= Proofs.Records.get_filtered_block_tree_from_subset
      duty.toHealing.toFG
      (Protocol.voter_processed_block_tree S.E
        duty.toHealing.toFG.toSG.toGoldfishStore duty.toHealing.s) hB
    exact (Finset.mem_filter.mp hprocessed).1
  have hrootTree: RootInjectiveBelow tree:=
    Protocol.RootInjectiveBelow.mono hfacts.2.2 htreeT
  have hZT: Z ∈ duty.T:= by
    have hdata:= hZfrozen
    simp only [Protocol.voter_processed_block_tree, Finset.mem_filter] at hdata
    exact hdata.1
  by_contra hnot
  have hHT: H ∈ duty.T:= by
    rcases Proofs.Records.ghost_mem A tree score eligible with hHA | hHtree
    · have hAT: A ∈ duty.T:=
        NjGap.mem_T_of_preceq hpc Z hZT A hanchorZ
      rw [hHghost, hHA]
      exact hAT
    · exact htreeT (by simpa only [hHghost] using hHtree)
  have hHlow: (duty.σ H).h < duty.h_max - 1:= by
    have hderived: (derived_state S.E S.cfg H).h = (duty.σ H).h:=
      (congrArg (fun x => x.h) (hagree H hHT)).symm
    rw [← hderived]
    exact Nat.lt_of_not_ge hnot
  have hstep: ∀ W: Block V,
      W ∈ Protocol.voter_processed_block_tree S.E
        duty.toHealing.toFG.toSG.toGoldfishStore duty.toHealing.s →
      Block.Preceq H W → duty.h_max - 1 ≤ (duty.σ W).h →
      (∀ D: Block V, D.parent? = some H → Block.Preceq D W →
        D ∈ tree) → False:= by
    intro W hWfrozen hHW hWheight hchild
    have hHneW: H ≠ W:= by
      intro hEq
      subst W
      exact (Nat.not_lt_of_ge hWheight) hHlow
    obtain ⟨D, hDparent, hDW⟩:= Protocol.exists_child_towards W hHW hHneW
    have hDtree: D ∈ tree:= hchild D hDparent hDW
    have hDeligible: eligible D = true:= by
      rw [Proofs.Optimistic.goldfish_eligible_iff]
      rw [parent_eq_of_parent? hDparent]
      exact Or.inl hHlow
    have hDfalse: eligible D = false:= by
      have hparent:= hDparent
      rw [hHghost] at hparent
      exact eligible_child_false_at_ghost_result hrootTree hDtree hparent
    rw [hDfalse] at hDeligible
    contradiction
  rcases Proofs.Records.ghost_mem A tree score eligible with hHA | hHtree
  · -- the walk never left the anchor: the witness is above it
    have hHA': H = A:= by simpa only [hHghost] using hHA
    have hHZ: Block.Preceq H Z:= by rw [hHA']; exact hanchorZ
    refine hstep Z hZfrozen hHZ hZheight ?_
    intro D hDparent hDZ
    have hDT: D ∈ duty.T:=
      NjGap.mem_T_of_preceq hpc Z hZT D hDZ
    have hHD: Block.Preceq H D:= Protocol.preceq_of_parent? hDparent
    have hrootH: Block.Preceq
        (Protocol.get_fg_root duty.toHealing.toFG) H:= by
      rw [hHA']
      simpa only [A, Proofs.Optimistic.healAnchor_eq_get_sg_root] using
        seedFgRoot_preceq_roundAnchor S duty
          (S.hc.round_of duty.toHealing.s)
    have hrootD: Block.Preceq
        (Protocol.get_fg_root duty.toHealing.toFG) D:=
      Block.preceq_trans hrootH hHD
    have hFD: Block.Preceq duty.F D:= by
      refine Block.preceq_trans ?_ hrootD
      have hFJ: Block.Preceq duty.F duty.J:= by
        have hdep: DepReachableStore S.E S.hc S.cfg (S.node w)
            (rho.storeBeforeTime S w
              (Protocol.vote_time S.E (s + 1))):= by
          simpa only [Run.storeBeforeTime] using
            (Proofs.Bridges.depReachable_stateBeforeTime S adm.toScheduleWellFormed
              adm.toDeliveryWellFormed (Protocol.vote_time S.E (s + 1)) w)
        have h:= finalizedPrecedesJustifiedInvariant S.E S.hc S.cfg (S.node w)
          _ (Proofs.Bridges.reachableStore_of_depReachableStore S.E S.hc S.cfg
            (S.node w) hdep)
        simpa only [duty, voteDutyStore, voteStore, tickStore] using h
      exact Proofs.Records.preceq_get_fg_root_of_F
        (st:= duty.toHealing.toFG) hFJ
    have hDfull: D ∈ Protocol.get_filtered_block_tree
        duty.toHealing.toFG:= by
      simp only [Protocol.get_filtered_block_tree,
        Protocol.get_filtered_block_tree_from, Protocol.viable_tree,
        Protocol.finalized_descendants, Protocol.viable,
        Finset.mem_filter, decide_eq_true_eq]
      exact ⟨⟨⟨hDT, hFD⟩, Z, hZT, hDZ, hZheight⟩, hrootD⟩
    have hmax: duty.h_max ≤ (derived_state S.E S.cfg Z).h + 1:= by
      have hZle:= Nat.sub_le_iff_le_add.mp hZheight
      calc
        duty.h_max ≤ (duty.σ Z).h + 1:= hZle
        _ = (derived_state S.E S.cfg Z).h + 1:= by
            rw [congrArg (fun x => x.h) (hagree Z hZT)]
    exact ancestorCandidate_of_processedDescendant_and_hMax S adm hw
      (by simpa only [duty] using hZfrozen) hDZ
      (by simpa only [duty] using hDfull) (by simpa only [duty] using hmax)
  · -- the walk is inside the candidate tree: use its own viability witness
    have hHtree': H ∈ tree:= by simpa only [hHghost] using hHtree
    have hHdata:= hHtree'
    simp only [tree, duty, Proofs.Optimistic.voter_candidate_tree,
      Protocol.get_filtered_block_tree_from, Protocol.viable_tree,
      Protocol.finalized_descendants, Protocol.viable,
      Finset.mem_filter, decide_eq_true_eq] at hHdata
    obtain ⟨⟨⟨-, -⟩, W, hWprocessed, hHW, hWheight⟩, -⟩:= hHdata
    refine hstep W (by simpa only [duty] using hWprocessed) hHW
      (by simpa only [duty] using hWheight) ?_
    intro D hDparent hDW
    exact frozenCandidate_child_towards_witness S adm hw hHtree'
      (by simpa only [duty] using hWprocessed) hDparent hDW
      (by simpa only [duty] using hWheight)
-/



/-
/-- **The head floor in the reveal case.** When the duty's SG root is the
fork-choice root, the block that carries the local frontier one slot earlier is
a frozen witness above it, so the duty's head is in the band. No fresh anchor
and no candidate-path input are used. -/
theorem seedVoteDutyHead_thin_of_rootAnchor
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hfb: BelowOneThird S rho.honest)
    {M: Height} {w: V} (hw: w ∈ rho.honest) {s: Slot}
    (hpost: S.E.t_GST ≤ Protocol.support_cutoff S.E s)
    (hhor: Protocol.view_freeze S.E s ≤ rho.horizon)
    (hcutFrontier:
      (rho.storeBeforeTime S w (Protocol.support_cutoff S.E s)).h_max = M)
    (hfreezeFrontier:
      (rho.storeBeforeTime S w (Protocol.view_freeze S.E s)).h_max = M)
    (hfreezeGate:
      (rho.storeBeforeTime S w (Protocol.view_freeze S.E s)).h_j + 2 ≤ M)
    (hdutyFrontier: (voteDutyStore S rho w (s + 1)).h_max = M)
    (hdutyGate: (voteDutyStore S rho w (s + 1)).h_j + 2 ≤ M)
    (hanchorRoot: Proofs.Optimistic.healAnchor S.E S.hc
        (voteDutyStore S rho w (s + 1)).toHealing =
      Protocol.get_fg_root
        (voteDutyStore S rho w (s + 1)).toHealing.toFG):
    M - 1 ≤ (derived_state S.E S.cfg (voteDutyHead S rho w (s + 1))).h:= by
  have hsb: SlashableBound S rho:=
    slashableBound_of_admissible_belowOneThird S adm hfb
  set cut:= Protocol.support_cutoff S.E s with hcutDef
  -- the local frontier carrier one slot earlier
  have hdep: DepReachableStore S.E S.hc S.cfg (S.node w)
      (rho.storeBeforeTime S w cut):= by
    simpa only [Run.storeBeforeTime] using
      (Proofs.Bridges.depReachable_stateBeforeTime S adm.toScheduleWellFormed
        adm.toDeliveryWellFormed cut w)
  obtain ⟨Z, hZmem, hZlower⟩:=
    hMaxInTree_depReachable S.E S.hc S.cfg (S.node w) hdep
  have hagreeCut: DerivedStateAgrees S.E S.cfg
      (rho.storeBeforeTime S w cut):=
    derivedStateAgrees_depReachable S.E S.hc S.cfg (S.node w) _ hdep
  have hZrun: RunBlock S rho Z:= by
    obtain ⟨n, hn, -⟩:= Proofs.Bridges.stateBeforeTime_eq_stateBefore
      S adm.toScheduleWellFormed cut
    apply Proofs.Bridges.runBlock_of_stateBefore_mem S hw (i:= n)
    rw [← hn]
    exact hZmem
  have hZthin: M - 1 ≤ (derived_state S.E S.cfg Z).h:= by
    refine Nat.le_trans (Nat.sub_le M 1) ?_
    calc
      M = (rho.storeBeforeTime S w cut).h_max:= hcutFrontier.symm
      _ ≤ ((rho.storeBeforeTime S w cut).σ Z).h:= hZlower
      _ = (derived_state S.E S.cfg Z).h:=
        congrArg (fun x => x.h) (hagreeCut Z hZmem)
  -- one relay makes it visible and stamped before the freeze
  have hvisible:= thinBlock_visible_and_stamped_after_oneDelay
    S adm hsb hw hw (source:= cut) (cut:= Protocol.view_freeze S.E s)
    (read:= Protocol.vote_time S.E (s + 1)) hZmem hZrun hZthin hpost
    (seedSupportCutoff_add_delta S.E s)
    (le_of_lt (Protocol.view_freeze_lt_vote_time_succ S.E s)) hhor
    hfreezeFrontier hfreezeGate
  have hZduty: Z ∈ (voteDutyStore S rho w (s + 1)).T:= by
    simpa only [voteDutyStore, voteStore, tickStore] using hvisible.1
  have hZstamp: stampedBefore
      (voteDutyStore S rho w (s + 1)).timestamp_block
      (Protocol.view_freeze S.E s) Z = true:= by
    rcases hvisible.2 with hgen | hstamp
    · rw [hgen]
      have h:= Protocol.genesis_mem_and_stamp_storeBeforeTime
        S adm.toScheduleWellFormed w (Protocol.vote_time S.E (s + 1))
        (Protocol.view_freeze S.E s)
      simpa only [voteDutyStore, voteStore, tickStore] using h.2
    · simpa only [voteDutyStore, voteStore, tickStore] using hstamp
  have hZfrozen: Z ∈ Protocol.voter_processed_block_tree S.E
      (voteDutyStore S rho w (s + 1)).toHealing.toFG.toSG.toGoldfishStore
      (voteDutyStore S rho w (s + 1)).toHealing.s:= by
    simp only [Protocol.voter_processed_block_tree, Finset.mem_filter,
      Proofs.Optimistic.toHealing_slot, Proofs.Optimistic.voteDutyStore_slot]
    exact ⟨hZduty, Or.inl (by
      simpa only [Nat.add_sub_cancel] using hZstamp)⟩
  have hagreeDuty: DerivedStateAgrees S.E S.cfg
      (voteDutyStore S rho w (s + 1)):=
    (voteDuty_parentClosed_agrees_rootInjective S adm hw (s + 1)).2.1
  have hZheight: (voteDutyStore S rho w (s + 1)).h_max - 1 ≤
      ((voteDutyStore S rho w (s + 1)).σ Z).h:= by
    rw [hdutyFrontier, congrArg (fun x => x.h) (hagreeDuty Z hZduty)]
    exact hZthin
  have hanchorZ: Block.Preceq
      (Proofs.Optimistic.healAnchor S.E S.hc
        (voteDutyStore S rho w (s + 1)).toHealing) Z:= by
    rw [hanchorRoot]
    have h:= frontierRoot_preceq_of_gateOff S adm hsb hw hZrun hZthin
      (read:= Protocol.vote_time S.E (s + 1))
      (by simpa only [voteDutyStore, voteStore, tickStore] using hdutyFrontier)
      (by simpa only [voteDutyStore, voteStore, tickStore] using hdutyGate)
    simpa only [voteDutyStore, voteStore, tickStore] using h
  have hfloor:= seedVoteDutyHead_thin_of_frozenWitness S adm hw hZfrozen
    hZheight hanchorZ
  rwa [hdutyFrontier] at hfloor
-/

/-! ## The round's SG roots against the entry block -/



/-
/-- **The anchor record from the middle-case residual.** Three cases, and
only the third is open: a fresh anchor is settled by the grade-0 veto, a
collapsed SG root is the gate-off fork-choice root and lies below the carrier's
own viability witness, and the middle case is the named residual. -/
theorem seedRoundAnchorCompatible_of_clearResidual
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hfb: BelowOneThird S rho.honest)
    {M: Height} {q: Round}
    (hready: GradeRoundReady S rho q)
    (hg1: LiveG1SettledAt S rho q)
    (hselected: ∀ v ∈ rho.honest, ∃ Q: Block V,
      Protocol.grade2_block S.E S.hc
        (actionStoreAt S rho v q).toHealing q = some Q)
    (hfrontier: ∀ u ∈ rho.honest,
      (rho.storeBeforeTime S u (S.a q)).h_max = M)
    (hgate: ∀ u ∈ rho.honest,
      (rho.storeBeforeTime S u (S.a q)).h_j + 2 ≤ M)
    (hdutyFrontier: ∀ d: Slot, S.hc.opening_slot q ≤ d →
      d ≤ seedRoundLastSlot S q → ∀ w ∈ rho.honest,
        (voteDutyStore S rho w d).h_max = M)
    (hdutyGate: ∀ d: Slot, S.hc.opening_slot q ≤ d →
      d ≤ seedRoundLastSlot S q → ∀ w ∈ rho.honest,
        (voteDutyStore S rho w d).h_j + 2 ≤ M)
    (hclear: SeedClearCarrierCompatiblePreviousAt S rho q)
    {v: V} (hv: v ∈ rho.honest):
    SeedRoundAnchorCompatibleAt S rho q (actionSGBlockAt S rho v q):= by
  have hsb: SlashableBound S rho:=
    slashableBound_of_admissible_belowOneThird S adm hfb
  obtain ⟨W, hWrun, hCW, hWthin⟩:= seedActionCarrier_thinWitness S adm hv
    hfrontier (hselected v hv)
  intro d hdlo hdhi w hw
  by_cases hanchor: ∃ A: Block V, Protocol.fresh_anchor S.E S.hc
      (voteDutyStore S rho w d).toHealing q = some A
  · -- the grade-0 veto
    obtain ⟨A, hA⟩:= hanchor
    have hAread: Protocol.fresh_anchor S.E S.hc
        (rho.storeBeforeTime S w (Protocol.vote_time S.E d)).toHealing q =
          some A:= by
      simpa only [voteDutyStore, voteStore, tickStore] using hA
    rw [seedVoteDutyAnchor_eq_roundAnchor S rho w hdlo hdhi,
      show Protocol.get_sg_root S.E S.hc
        (rho.storeBeforeTime S w (Protocol.vote_time S.E d)).toHealing q = A by
          simp only [Protocol.get_sg_root, hAread]]
    exact seedRoundAnchor_compatible_actionCarrier S adm hfb hready hg1
      hselected hfrontier hgate hw
      (Γ_0_le_vote_time_of_round_eq S (seedEntryRoundOf' S hdlo hdhi))
      hAread hv
  · push Not at hanchor
    have hnone: Protocol.fresh_anchor S.E S.hc
        (voteDutyStore S rho w d).toHealing q = none:= by
      cases hopt: Protocol.fresh_anchor S.E S.hc
          (voteDutyStore S rho w d).toHealing q with
      | none => rfl
      | some A => exact absurd hopt (hanchor A)
    by_cases hroot: Proofs.Optimistic.healAnchor S.E S.hc
        (voteDutyStore S rho w d).toHealing =
      Protocol.get_fg_root (voteDutyStore S rho w d).toHealing.toFG
    · -- the collapsed root
      rw [hroot]
      have hrootW: Block.Preceq
          (Protocol.get_fg_root
            (voteDutyStore S rho w d).toHealing.toFG) W:= by
        have h:= frontierRoot_preceq_of_gateOff S adm hsb hw hWrun hWthin
          (read:= Protocol.vote_time S.E d)
          (by simpa only [voteDutyStore, voteStore, tickStore] using
            hdutyFrontier d hdlo hdhi w hw)
          (by simpa only [voteDutyStore, voteStore, tickStore] using
            hdutyGate d hdlo hdhi w hw)
        simpa only [voteDutyStore, voteStore, tickStore] using h
      exact Block.compatible_of_preceq_common hrootW hCW
    · -- the middle case: the named residual
      exact hclear d hdlo hdhi w hw hnone hroot v hv
-/


/-
/-- **The anchor record from fresh anchors and the veto.** With a fresh anchor
of round `q` at every honest read of the round, every honest SG root of the
round is on the chain of every honest round-`q` action carrier. -/
theorem seedRoundAnchorCompatible_of_freshAnchors
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hfb: BelowOneThird S rho.honest)
    {M: Height} {q: Round}
    (hready: GradeRoundReady S rho q)
    (hg1: LiveG1SettledAt S rho q)
    (hselected: ∀ v ∈ rho.honest, ∃ Q: Block V,
      Protocol.grade2_block S.E S.hc
        (actionStoreAt S rho v q).toHealing q = some Q)
    (hfrontier: ∀ u ∈ rho.honest,
      (rho.storeBeforeTime S u (S.a q)).h_max = M)
    (hgate: ∀ u ∈ rho.honest,
      (rho.storeBeforeTime S u (S.a q)).h_j + 2 ≤ M)
    (hanchors: ∀ d: Slot, S.hc.opening_slot q ≤ d →
      d ≤ seedRoundLastSlot S q → ∀ w ∈ rho.honest, ∃ A: Block V,
        Protocol.fresh_anchor S.E S.hc
          (voteDutyStore S rho w d).toHealing q = some A)
    {v: V} (hv: v ∈ rho.honest):
    SeedRoundAnchorCompatibleAt S rho q (actionSGBlockAt S rho v q):= by
  intro d hdlo hdhi w hw
  obtain ⟨A, hA⟩:= hanchors d hdlo hdhi w hw
  have hAread: Protocol.fresh_anchor S.E S.hc
      (rho.storeBeforeTime S w (Protocol.vote_time S.E d)).toHealing q =
        some A:= by
    simpa only [voteDutyStore, voteStore, tickStore] using hA
  rw [seedVoteDutyAnchor_eq_roundAnchor S rho w hdlo hdhi,
    show Protocol.get_sg_root S.E S.hc
      (rho.storeBeforeTime S w (Protocol.vote_time S.E d)).toHealing q = A by
        simp only [Protocol.get_sg_root, hAread]]
  exact seedRoundAnchor_compatible_actionCarrier S adm hfb hready hg1
    hselected hfrontier hgate hw
    (Γ_0_le_vote_time_of_round_eq S (seedEntryRoundOf' S hdlo hdhi))
    hAread hv
-/

/-! ## The head bound at the duties of the round -/



/-! ## The fold to the last slot of the round -/












/-! ## The head floor at every vote duty of the round -/








/-
/-- **The head floor at every vote duty of the round, unconditionally.** Both
arms of `seedRoundAnchor_preceq_previousFrontier_or_eq_fgRoot` carry a frozen
witness of the frontier band above the duty's own SG root: the previous
round's frontier witness, relayed one delay after that round's action read and
therefore stamped before the duty's freeze, or the reader's own local frontier
carrier from the previous slot's support cutoff. -/
theorem seedVoteDutyHead_thin_of_previousFrontier
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hfb: BelowOneThird S rho.honest)
    {M: Height} {q: Round} (hq: 0 < q)
    {w: V} (hw: w ∈ rho.honest) {d: Slot}
    (hdlo: S.hc.opening_slot q ≤ d) (hdhi: d ≤ seedRoundLastSlot S q)
    (hpost: S.E.t_GST ≤ S.a (q - 1))
    (hcut: S.hc.Γ_neg1 S.E.Δ q ≤ rho.horizon)
    (hprevHor: S.a (q - 1) + S.E.Δ ≤ rho.horizon)
    {Cprev W: Block V} {holder: V} (hholder: holder ∈ rho.honest)
    (hWmem: W ∈ (rho.storeBeforeTime S holder (S.a (q - 1))).T)
    (hWrun: RunBlock S rho W) (hCW: Block.Preceq Cprev W)
    (hWthin: M - 1 ≤ (derived_state S.E S.cfg W).h)
    (hupper: ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u (q - 1)) Cprev)
    (hcutFrontier: ∀ u ∈ rho.honest,
      (rho.storeBeforeTime S u (S.a (q - 1) + S.E.Δ)).h_max = M)
    (hcutGate: ∀ u ∈ rho.honest,
      (rho.storeBeforeTime S u (S.a (q - 1) + S.E.Δ)).h_j + 2 ≤ M)
    (hdutyFrontier: (voteDutyStore S rho w d).h_max = M)
    (hdutyGate: (voteDutyStore S rho w d).h_j + 2 ≤ M)
    (hsupportPost: S.E.t_GST ≤ Protocol.support_cutoff S.E (d - 1))
    (hfreezeHor: Protocol.view_freeze S.E (d - 1) ≤ rho.horizon)
    (hsupportFrontier:
      (rho.storeBeforeTime S w (Protocol.support_cutoff S.E (d - 1))).h_max = M)
    (hfreezeFrontier:
      (rho.storeBeforeTime S w (Protocol.view_freeze S.E (d - 1))).h_max = M)
    (hfreezeGate:
      (rho.storeBeforeTime S w
        (Protocol.view_freeze S.E (d - 1))).h_j + 2 ≤ M):
    M - 1 ≤ (derived_state S.E S.cfg (voteDutyHead S rho w d)).h:= by
  have hR: 2 ≤ S.hc.R:= S.hc.R_ge_two
  have hqPred: q - 1 + 1 = q:= Nat.sub_add_cancel (Nat.succ_le_of_lt hq)
  have hopenSucc: S.hc.opening_slot q =
      S.hc.opening_slot (q - 1) + S.hc.R:= by
    have h:= opening_slot_succ_eq S.hc (q - 1)
    rw [hqPred] at h
    exact h
  obtain ⟨hslot, hdpos⟩:= seedEntryFreezeSlot_nat
    (a:= S.hc.opening_slot (q - 1)) (b:= S.hc.R) (d:= d) hR
    (by rw [← hopenSucc]; exact hdlo)
  have hpredSucc: d - 1 + 1 = d:=
    Nat.sub_add_cancel (Nat.succ_le_iff.mpr hdpos)
  have hfreeze: S.a (q - 1) + S.E.Δ ≤
      Protocol.view_freeze S.E (d - 1):= by
    rw [seedEntryActionDelay_eq_viewFreeze S (q - 1)]
    exact seedEntryViewFreeze_mono S.E hslot
  have hdutyFrontier':
      (rho.storeBeforeTime S w (Protocol.vote_time S.E d)).h_max = M:= by
    simpa only [voteDutyStore, voteStore, tickStore] using hdutyFrontier
  have hdutyGate':
      (rho.storeBeforeTime S w (Protocol.vote_time S.E d)).h_j + 2 ≤ M:= by
    simpa only [voteDutyStore, voteStore, tickStore] using hdutyGate
  -- the previous frontier's witness is visible and frozen at this duty
  have hvoteHi: Protocol.view_freeze S.E (d - 1) ≤
      Protocol.vote_time S.E d:= by
    rw [← hpredSucc]
    exact le_of_lt (Protocol.view_freeze_lt_vote_time_succ S.E (d - 1))
  have hvisible:= thinBlock_visible_and_stamped_after_oneDelay
    S adm (slashableBound_of_admissible_belowOneThird S adm hfb) hholder hw
    (source:= S.a (q - 1)) (cut:= S.a (q - 1) + S.E.Δ)
    (read:= Protocol.vote_time S.E d) hWmem hWrun hWthin hpost rfl
    (hfreeze.trans hvoteHi) hprevHor (hcutFrontier w hw) (hcutGate w hw)
  have hWduty: W ∈ (voteDutyStore S rho w d).T:= by
    simpa only [voteDutyStore, voteStore, tickStore] using hvisible.1
  have hWstamp: stampedBefore
      (voteDutyStore S rho w d).timestamp_block
      (Protocol.view_freeze S.E (d - 1)) W = true:= by
    rcases hvisible.2 with hgen | hstamp
    · rw [hgen]
      have h:= Protocol.genesis_mem_and_stamp_storeBeforeTime
        S adm.toScheduleWellFormed w (Protocol.vote_time S.E d)
        (Protocol.view_freeze S.E (d - 1))
      simpa only [voteDutyStore, voteStore, tickStore] using h.2
    · refine seedStampedBefore_mono hfreeze ?_
      simpa only [voteDutyStore, voteStore, tickStore] using hstamp
  have hWfrozen: W ∈ Protocol.voter_processed_block_tree S.E
      (voteDutyStore S rho w d).toHealing.toFG.toSG.toGoldfishStore
      (voteDutyStore S rho w d).toHealing.s:= by
    simp only [Protocol.voter_processed_block_tree, Finset.mem_filter,
      Proofs.Optimistic.toHealing_slot, Proofs.Optimistic.voteDutyStore_slot]
    exact ⟨hWduty, Or.inl hWstamp⟩
  have hagreeDuty: DerivedStateAgrees S.E S.cfg (voteDutyStore S rho w d):= by
    have h:= (voteDuty_parentClosed_agrees_rootInjective S adm hw
      (d - 1 + 1)).2.1
    rwa [hpredSucc] at h
  have hWheight: (voteDutyStore S rho w d).h_max - 1 ≤
      ((voteDutyStore S rho w d).σ W).h:= by
    rw [hdutyFrontier, congrArg (fun x => x.h) (hagreeDuty W hWduty)]
    exact hWthin
  rcases seedRoundAnchor_preceq_previousFrontier_or_eq_fgRoot S adm hfb hq
      hpost hcut hw (t:= Protocol.vote_time S.E d)
      (Γ_0_le_vote_time_of_round_eq S (seedEntryRoundOf' S hdlo hdhi))
      hdutyFrontier' hdutyGate' hWrun hCW hWthin
      (by
        refine NjGap.mem_T_of_preceq ?_ W ?_ Cprev hCW
        · have h:= (voteDuty_parentClosed_agrees_rootInjective S adm hw
            (d - 1 + 1)).1
          rw [hpredSucc] at h
          simpa only [voteDutyStore, voteStore, tickStore] using h
        · simpa only [voteDutyStore, voteStore, tickStore] using hWduty)
      hupper with hprev | hroot
  · -- the SG root is under the previous frontier, whose witness is frozen here
    have hanchorW: Block.Preceq
        (Proofs.Optimistic.healAnchor S.E S.hc (voteDutyStore S rho w d).toHealing)
        W:= by
      rw [seedVoteDutyAnchor_eq_roundAnchor S rho w hdlo hdhi]
      exact Block.preceq_trans hprev hCW
    have hfloor:= seedVoteDutyHead_thin_of_frozenWitness S adm hw
      (s:= d - 1)
      (by rw [hpredSucc]; exact hWfrozen)
      (by rw [hpredSucc]; exact hWheight)
      (by rw [hpredSucc]; exact hanchorW)
    rw [hpredSucc, hdutyFrontier] at hfloor
    exact hfloor
  · -- the SG root collapsed to the fork-choice root
    have hanchorRoot: Proofs.Optimistic.healAnchor S.E S.hc
        (voteDutyStore S rho w d).toHealing =
      Protocol.get_fg_root
        (voteDutyStore S rho w d).toHealing.toFG:= by
      rw [seedVoteDutyAnchor_eq_roundAnchor S rho w hdlo hdhi]
      simpa only [voteDutyStore, voteStore, tickStore] using hroot
    have hfloor:= seedVoteDutyHead_thin_of_rootAnchor S adm hfb
      (M:= M) (w:= w) (s:= d - 1) hw hsupportPost hfreezeHor
      hsupportFrontier hfreezeFrontier hfreezeGate
      (by rw [hpredSucc]; exact hdutyFrontier)
      (by rw [hpredSucc]; exact hdutyGate)
      (by rw [hpredSucc]; exact hanchorRoot)
    rw [hpredSucc] at hfloor
    exact hfloor
-/


/-
/-- **The head floor at every vote duty of the round, unconditionally**, from
The previous round's carrier frontier. No tier, no fresh anchors: both arms of
`seedRoundAnchor_preceq_previousFrontier_or_eq_fgRoot` carry a frozen band
witness above the duty's own SG root. -/
theorem seedRoundHeadsThin_of_previousFrontier
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hfb: BelowOneThird S rho.honest)
    {M: Height} {q: Round} (hq: 0 < q)
    (hpostPrev: S.E.t_GST ≤ S.a (q - 1))
    (hcut: S.hc.Γ_neg1 S.E.Δ q ≤ rho.horizon)
    (hprevHor: S.a (q - 1) + S.E.Δ ≤ rho.horizon)
    (hlastConfHor: Protocol.confirmation_time S.E
      (seedRoundLastSlot S q - 1) ≤ rho.horizon)
    {Cprev W: Block V} {holder: V} (hholder: holder ∈ rho.honest)
    (hWmem: W ∈ (rho.storeBeforeTime S holder (S.a (q - 1))).T)
    (hWrun: RunBlock S rho W) (hCW: Block.Preceq Cprev W)
    (hWthin: M - 1 ≤ (derived_state S.E S.cfg W).h)
    (hupper: ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u (q - 1)) Cprev)
    (hcutFrontier: ∀ u ∈ rho.honest,
      (rho.storeBeforeTime S u (S.a (q - 1) + S.E.Δ)).h_max = M)
    (hcutGate: ∀ u ∈ rho.honest,
      (rho.storeBeforeTime S u (S.a (q - 1) + S.E.Δ)).h_j + 2 ≤ M)
    (hconeWindow: GateOffSeedConeWindowAt S rho M
      (S.hc.opening_slot q) (seedRoundLastSlot S q - 1))
    (hslotWindow: ∀ read: Time, S.a (q - 1) ≤ read →
      read ≤ Protocol.confirmation_time S.E (seedRoundLastSlot S q - 1) →
      ∀ w ∈ rho.honest,
        (rho.storeBeforeTime S w read).h_j + 2 ≤ M ∧
          (rho.storeBeforeTime S w read).h_max = M):
    ∀ d: Slot, S.hc.opening_slot q ≤ d → d ≤ seedRoundLastSlot S q →
      ∀ X: Block V, HonestHead S rho d X →
        M - 1 ≤ (derived_state S.E S.cfg X).h:= by
  have hlastPos: 0 < seedRoundLastSlot S q:= seedEntryLastPos S q
  have hlastPred: seedRoundLastSlot S q - 1 + 1 = seedRoundLastSlot S q:=
    Nat.sub_add_cancel (Nat.succ_le_iff.mpr hlastPos)
  have hopenSucc: S.hc.opening_slot q =
      S.hc.opening_slot (q - 1) + S.hc.R:= by
    have h:= opening_slot_succ_eq S.hc (q - 1)
    rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hq)] at h
    exact h
  intro d hdlo hdhi X hX
  obtain ⟨hslot, hdpos⟩:= seedEntryFreezeSlot_nat
    (a:= S.hc.opening_slot (q - 1)) (b:= S.hc.R) (d:= d) S.hc.R_ge_two
    (by rw [← hopenSucc]; exact hdlo)
  have hpredSucc: d - 1 + 1 = d:=
    Nat.sub_add_cancel (Nat.succ_le_iff.mpr hdpos)
  have hvoteHor: Protocol.vote_time S.E d ≤ rho.horizon:=
    (seedEntryVoteTime_le_lastConfirmation S hdhi).trans hlastConfHor
  obtain ⟨w, hw, hwCommittee, hXrun, hXemit⟩:= hX
  have hXeq: X = voteDutyHead S rho w d:= by
    have hYrun: RunBlock S rho (voteDutyHead S rho w d):= by
      simpa only [voteDutyHead] using voteDutyHead_runBlock S adm hw d
    have hYemit:= seedVoteDutyHead_emits S adm hw hdpos hwCommittee hvoteHor
    have hrootEq: X.root = (voteDutyHead S rho w d).root:=
      congrArg GoldfishVote.head
        (emits_gfVote_unique S adm.toScheduleWellFormed hXemit hYemit rfl)
    exact runBlock_eq_of_root_eq adm.toRootCollisionFree hXrun hYrun hrootEq
  have hcutLo: S.a (q - 1) ≤ Protocol.support_cutoff S.E (d - 1):= by
    rw [seedAction_eq_supportCutoff S (q - 1)]
    exact Proofs.Optimistic.support_cutoff_mono S.E hslot
  have hcutHi: Protocol.support_cutoff S.E (d - 1) ≤
      Protocol.confirmation_time S.E (seedRoundLastSlot S q - 1):= by
    refine le_trans ?_ (seedEntryConfirmation_mono S.E
      (Nat.sub_le_sub_right hdhi 1))
    unfold Protocol.support_cutoff Protocol.confirmation_time
    have key: ∀ a e: Int, 0 < e → a + 2 * e ≤ a + 6 * e:= by
      intro a e he; omega
    exact key (S.E.t (d - 1)) S.E.Δ S.E.Δ_pos
  have hfreezeLo: S.a (q - 1) ≤ Protocol.view_freeze S.E (d - 1):=
    hcutLo.trans (le_of_lt
      (Proofs.Optimistic.support_cutoff_lt_view_freeze S.E (d - 1)))
  have hfreezeHi: Protocol.view_freeze S.E (d - 1) ≤
      Protocol.confirmation_time S.E (seedRoundLastSlot S q - 1):=
    (seedViewFreeze_le_confirmation S.E (d - 1)).trans
      (seedEntryConfirmation_mono S.E (Nat.sub_le_sub_right hdhi 1))
  have hfloor:= seedVoteDutyHead_thin_of_previousFrontier S adm hfb hq hw
    hdlo hdhi hpostPrev hcut hprevHor hholder hWmem hWrun hCW hWthin hupper
    hcutFrontier hcutGate
    (hconeWindow.voteFrontier d hdlo (by rw [hlastPred]; exact hdhi) w hw)
    (hconeWindow.voteGateOff d hdlo (by rw [hlastPred]; exact hdhi) w hw)
    (hpostPrev.trans hcutLo) (hfreezeHi.trans hlastConfHor)
    (hslotWindow _ hcutLo hcutHi w hw).2
    (hslotWindow _ hfreezeLo hfreezeHi w hw).2
    (hslotWindow _ hfreezeLo hfreezeHi w hw).1
  rw [hXeq]
  exact hfloor
-/

/-! ## The previous round's frontier, with a located witness -/


/-! ## The entry record from the round's graded reads -/


/-- **The remaining protocol input of the gate-off seed base.** The round's
reads carry grades: a selected grade-2 candidate at every honest action read,
and a fresh grade-1 anchor at every honest read of the round.

 (statement change, ledger row). The selection is the PREPARED frame
candidate `Internal.PhaseGrades.nodeQ2` at `actionReadAt`, not the absolute
`Protocol.grade2_block` at the erased action store. The two are not
interchangeable in either direction: `nodeQ2_of_grade2_block` is an
absolute-to-relative bridge that does not exist, and `G2_of_nodeQ2` is false
(both recorded byte-exactly in `SeedActionQ2Run.lean`). Every consumer of this
record reaches the selector through `Internal.PhaseGrades.Q31_actionSGBlock_tiers`
and `actionSGBlockAt_clear_or_selectedG2`, which take `nodeQ2`, so the record
is stated where the consumers read it. -/
structure SeedRoundGradedAt (S : Setup V) (rho : Run V) (q : Round) : Prop where
  selectedPrev : ∀ v ∈ rho.honest, ∃ Q : Block V,
    Internal.PhaseGrades.nodeQ2 S (actionReadAt S rho v (q - 1)) (q - 1) = some Q
  selected : ∀ v ∈ rho.honest, ∃ Q : Block V,
    Internal.PhaseGrades.nodeQ2 S (actionReadAt S rho v q) q = some Q



/- /-- **The entry block of the round.** The deepest honest action carrier is a
run block with a viability witness, above every honest round-`q` action
carrier, and below every honest Goldfish head of the round's last vote duty. -/
/-- **The entry block of the round.** The deepest honest action carrier is a
run block with a viability witness, above every honest round-`q` action
carrier, and below every honest Goldfish head of the round's last vote duty. -/
theorem seedEntry_entry
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hfb: BelowOneThird S rho.honest)
    {M: Height} {q: Round} (hq: 0 < q)
    (hready: GradeRoundReady S rho q)
    (hsettled: SelectedG2SettledAt S rho q)
    (hg1: LiveG1SettledAt S rho q)
    (hgraded: SeedRoundGradedAt S rho q)
    (hclearResidual: SeedClearCarrierCompatiblePreviousAt S rho q)
    (hpostProposal: S.E.t_GST ≤
      Protocol.proposal_time S.E (S.hc.opening_slot q))
    (hpostOpeningVote: S.E.t_GST ≤
      Protocol.vote_time S.E (S.hc.opening_slot q))
    (hopeningHor: Protocol.confirmation_time S.E
      (S.hc.opening_slot q) ≤ rho.horizon)
    (hlastConfHor: Protocol.confirmation_time S.E
      (seedRoundLastSlot S q - 1) ≤ rho.horizon)
    (hfrontier: ∀ u ∈ rho.honest,
      (rho.storeBeforeTime S u (S.a q)).h_max = M)
    (hgate: ∀ u ∈ rho.honest,
      (rho.storeBeforeTime S u (S.a q)).h_j + 2 ≤ M)
    (hprevFrontier: ∀ u ∈ rho.honest,
      (rho.storeBeforeTime S u (S.a (q - 1))).h_max = M)
    (hcutFrontier: ∀ u ∈ rho.honest,
      (rho.storeBeforeTime S u (S.a (q - 1) + S.E.Δ)).h_max = M)
    (hcutGate: ∀ u ∈ rho.honest,
      (rho.storeBeforeTime S u (S.a (q - 1) + S.E.Δ)).h_j + 2 ≤ M)
    (hsupportFrontier: ∀ u ∈ rho.honest,
      (rho.storeBeforeTime S u
        (Protocol.support_cutoff S.E (S.hc.opening_slot q))).h_max = M)
    (hsupportGate: ∀ u ∈ rho.honest,
      (rho.storeBeforeTime S u
        (Protocol.support_cutoff S.E (S.hc.opening_slot q))).h_j + 2 ≤ M)
    (hpostPrev: S.E.t_GST ≤ S.a (q - 1))
    (hprevHor: S.a (q - 1) + S.E.Δ ≤ rho.horizon)
    (hconeWindow: GateOffSeedConeWindowAt S rho M
      (S.hc.opening_slot q) (seedRoundLastSlot S q - 1))
    (hheadThin: ∀ d: Slot, S.hc.opening_slot q ≤ d →
      d ≤ seedRoundLastSlot S q → ∀ X: Block V, HonestHead S rho d X →
        M - 1 ≤ (derived_state S.E S.cfg X).h):
    ∃ C: Block V, RunBlock S rho C ∧
      (∃ W: Block V, RunBlock S rho W ∧ Block.Preceq C W ∧
        M - 1 ≤ (derived_state S.E S.cfg W).h) ∧
      (∀ v ∈ rho.honest, Block.Preceq (actionSGBlockAt S rho v q) C) ∧
      (∀ X: Block V,
        HonestHead S rho (S.hc.opening_slot (q + 1) - 1) X →
          Block.Preceq C X):= by
  have hsb: SlashableBound S rho:=
    slashableBound_of_admissible_belowOneThird S adm hfb
  have hlastPos: 0 < seedRoundLastSlot S q:= seedEntryLastPos S q
  have hlastPred: seedRoundLastSlot S q - 1 + 1 = seedRoundLastSlot S q:=
    Nat.sub_add_cancel (Nat.succ_le_iff.mpr hlastPos)
  have hopenLast: S.hc.opening_slot q < seedRoundLastSlot S q:=
    openingSlot_lt_seedRoundLastSlot' S q
  have hopenSuccLast: S.hc.opening_slot q + 1 ≤ seedRoundLastSlot S q:=
    Nat.succ_le_of_lt hopenLast
  obtain ⟨v0, hv0, hdom⟩:= exists_seedDeepestActionCarrier S adm hcom hfb
    hready hsettled hpostProposal hopeningHor hgraded.selected hfrontier hgate
  obtain ⟨W, hWrun, hCW, hWthin⟩:= seedActionCarrier_thinWitness S adm hv0
    hfrontier (hgraded.selected v0 hv0)
  refine ⟨actionSGBlockAt S rho v0 q,
    seedActionCarrier_runBlock S adm hv0 (hgraded.selected v0 hv0),
    ⟨W, hWrun, hCW, hWthin⟩, hdom, ?_⟩
  intro X hX
  have hXlast: HonestHead S rho (seedRoundLastSlot S q) X:= hX
  have hXthin: M - 1 ≤ (derived_state S.E S.cfg X).h:=
    hheadThin (seedRoundLastSlot S q) (Nat.le_of_lt hopenLast) (le_refl _)
      X hXlast
  obtain ⟨Q0, hQ0⟩:= hgraded.selected v0 hv0
  rcases actionSGBlockAt_clear_or_selectedG2 S rho hQ0 with
    ⟨T, hwalk, hcarrier⟩ | hcarrier
  · have hclear: Block.Preceq (actionSGBlockAt S rho v0 q)
        (actionStoreAt S rho v0 q).live_confirmed:= by
      rw [hcarrier]
      exact Proofs.Engine.deepest_clear_preceq hwalk
    rcases actionStoreAt_liveConfirmed_genuine_or_fgRoot S rho v0 q with
      ⟨D, hD, hDeq⟩ | ⟨R, hReq, hRlive⟩
    · -- The carrier sits under a genuine opening confirmation.
      have hCD: Block.Preceq (actionSGBlockAt S rho v0 q) D:= by
        rw [hDeq]
        exact hclear
      have hanchorRec:=
        seedRoundAnchorCompatible_of_clearResidual S adm hfb hready hg1
          hgraded.selected hfrontier hgate
          (fun d hdlo hdhi u hu => hconeWindow.voteFrontier d hdlo
            (by rw [hlastPred]; exact hdhi) u hu)
          (fun d hdlo hdhi u hu => hconeWindow.voteGateOff d hdlo
            (by rw [hlastPred]; exact hdhi) u hu)
          hclearResidual hv0
      have hanchorSucc: ∀ w ∈ rho.honest, Block.compatible
          (Proofs.Optimistic.healAnchor S.E S.hc
            (voteDutyStore S rho w
              (S.hc.opening_slot q + 1)).toHealing)
            (actionSGBlockAt S rho v0 q) = true:=
        fun w hw => hanchorRec (S.hc.opening_slot q + 1) (Nat.le_succ _)
          hopenSuccLast w hw
      have hseed:= seedCarrierCone_openingSucc S adm hcom hfb hq
        hpostProposal hpostOpeningVote hopeningHor hsupportFrontier
        hsupportGate
        (fun w hw => hconeWindow.voteFrontier (S.hc.opening_slot q + 1)
          (Nat.le_succ _) (by rw [hlastPred]; exact hopenSuccLast) w hw)
        (fun w hw => hconeWindow.voteGateOff (S.hc.opening_slot q + 1)
          (Nat.le_succ _) (by rw [hlastPred]; exact hopenSuccLast) w hw)
        (hheadThin (S.hc.opening_slot q) (le_refl _) (Nat.le_of_lt hopenLast))
        hv0 hD hCD hanchorSucc
      have hcone:= seedCarrierCone_through S adm hcom hfb hpostOpeningVote
        hlastConfHor hconeWindow
        (fun d hdlo hdhi => hheadThin d ((Nat.le_succ _).trans hdlo) hdhi)
        hanchorRec hWrun hCW hWthin hseed (seedRoundLastSlot S q)
        hopenSuccLast (le_refl _)
      exact seedEntryCone_preceq_honestHead S adm hcone hXlast
    · -- The carrier is the store's own fork-choice root.
      have hTroot: T = Protocol.get_fg_root
          (actionStoreAt S rho v0 q).toHealing.toFG:=
        clearCarrier_eq_actionFGRoot_of_rootSource S rho hcarrier
          (by rw [← hcarrier]; exact hclear) hReq hRlive
      obtain ⟨-, -, -, hXrun, -⟩:= hXlast
      rw [hcarrier, hTroot, actionStoreAt_fgRoot_eq_storeBeforeTime S rho v0 q]
      exact frontierRoot_preceq_of_gateOff S adm hsb hv0 hXrun hXthin
        (hfrontier v0 hv0) (hgate v0 hv0)
  · -- The carrier is the store's selected grade-2 block.
    have hround: S.hc.round_of (seedRoundLastSlot S q) = q:=
      seedEntryRoundOf' S (Nat.le_of_lt hopenLast) (le_refl _)
    have hrelay: S.a (q - 1) + S.E.Δ ≤
        Protocol.vote_time S.E (seedRoundLastSlot S q):= by
      have hqPred: q - 1 + 1 = q:= Nat.sub_add_cancel (Nat.succ_le_of_lt hq)
      refine (action_add_delta_le_openingProposal_of_round_lt S
        (r:= q - 1) (q:= q) (by rw [← hqPred]; exact Nat.lt_succ_self _)).trans ?_
      refine (Protocol.proposal_time_mono S.E
        (Nat.le_of_lt hopenLast)).trans ?_
      exact le_of_lt (Protocol.proposal_time_lt_vote_time S.E _)
    have hvoteHor: Protocol.vote_time S.E (seedRoundLastSlot S q) ≤
        rho.horizon:=
      (seedEntryVoteTime_le_lastConfirmation S (le_refl _)).trans hlastConfHor
    rw [hcarrier]
    exact seedGradeBound_preceq_roundHead S adm hfb hq hready hsettled
      hpostPrev hprevHor hprevFrontier hcutFrontier hcutGate hfrontier hgate
      hlastPos hround hrelay hvoteHor
      (fun u hu => hconeWindow.voteFrontier (seedRoundLastSlot S q)
        (Nat.le_of_lt hopenLast) (by rw [hlastPred]) u hu)
      (fun u hu => hconeWindow.voteGateOff (seedRoundLastSlot S q)
        (Nat.le_of_lt hopenLast) (by rw [hlastPred]) u hu)
      hv0 hQ0 hXlast hXthin
-/



/-
/-- **The healing entry property from the round's graded reads.** The deepest
honest round-`q` action carrier is the entry block. Its three shapes close
differently: a selected grade 2 is below every honest head of the round by the
grade arm; a recorded fork-choice root is below every run block of the frontier
band; and a clear-walk carrier sits under a genuine opening confirmation, so
the capture at the opening successor and the round fold carry it to the last
vote duty. -/
theorem seedBoundaryAdoption_of_graded
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hfb: BelowOneThird S rho.honest)
    {M: Height} {base q: Round}
    (hpostBase: S.E.t_GST ≤ S.a base)
    (hbaseq: base + 3 ≤ q)
    (hhor: S.a (q + 2) ≤ rho.horizon)
    (hwindow: ∀ read: Time, S.a base ≤ read → read ≤ S.a (q + 2) →
      ∀ w ∈ rho.honest,
        (rho.storeBeforeTime S w read).h_j + 2 ≤ M ∧
          (rho.storeBeforeTime S w read).h_max = M)
    (hgraded: SeedRoundGradedAt S rho q)
    (hclearResidual: SeedClearCarrierCompatiblePreviousAt S rho q):
    SeedBoundaryAdoptionAt S rho M q:= by
  have hsb: SlashableBound S rho:=
    slashableBound_of_admissible_belowOneThird S adm hfb
  obtain ⟨hqpos, hbasePred, hqPred, hpredQ, hbaseQ, hqPredPos, hbasePred2,
    hpred2Succ, hpredPred, hpred2Q⟩:= seedEntryBase_nat hbaseq
  -- Time landmarks of the window.
  have hpostPrev: S.E.t_GST ≤ S.a (q - 1):=
    hpostBase.trans (Assembly.a_mono S hbasePred)
  have hpostAction: S.E.t_GST ≤ S.a q:=
    hpostBase.trans (Assembly.a_mono S hbaseQ)
  have hprevDelta: S.a (q - 1) + S.E.Δ ≤ S.a q:= by
    have hlt: S.a (q - 1) + S.E.Δ < S.a q:= by
      have h:= lt_of_le_of_lt (action_add_delta_le_next_Γ_neg1 S (q - 1))
        (next_Γ_neg1_lt_action S (q - 1))
      rwa [hqPred] at h
    exact le_of_lt hlt
  have hactionHor: S.a q ≤ rho.horizon:=
    (Assembly.a_mono S (Nat.le_add_right q 2)).trans hhor
  have hnextActionHor: S.a (q + 1) ≤ rho.horizon:=
    (Assembly.a_mono S (Nat.add_le_add_left (by decide: 1 ≤ 2) q)).trans hhor
  have hlastLeOpening: seedRoundLastSlot S q - 1 ≤
      S.hc.opening_slot (q + 1):= by
    unfold seedRoundLastSlot
    exact (Nat.sub_le _ 1).trans (Nat.sub_le _ 1)
  have hlastConfHor: Protocol.confirmation_time S.E
      (seedRoundLastSlot S q - 1) ≤ rho.horizon:= by
    refine (seedEntryConfirmation_mono S.E hlastLeOpening).trans ?_
    rw [← Protocol.a_eq_confirmation_time]
    exact hnextActionHor
  have hlastConfLeEnd: Protocol.confirmation_time S.E
      (seedRoundLastSlot S q - 1) ≤ S.a (q + 2):= by
    refine (seedEntryConfirmation_mono S.E hlastLeOpening).trans ?_
    rw [← Protocol.a_eq_confirmation_time]
    exact Assembly.a_mono S (Nat.add_le_add_left (by decide: 1 ≤ 2) q)
  -- Frontier and gate at the reads the round uses.
  have hprevFrontier: ∀ u ∈ rho.honest,
      (rho.storeBeforeTime S u (S.a (q - 1))).h_max = M:= fun u hu =>
    (hwindow (S.a (q - 1)) (Assembly.a_mono S hbasePred)
      ((Assembly.a_mono S hpredQ).trans
        (Assembly.a_mono S (Nat.le_add_right q 2))) u hu).2
  have hcutFrontier: ∀ u ∈ rho.honest,
      (rho.storeBeforeTime S u (S.a (q - 1) + S.E.Δ)).h_max = M:= fun u hu =>
    (hwindow (S.a (q - 1) + S.E.Δ)
      ((Assembly.a_mono S hbasePred).trans
        (le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)))
      (hprevDelta.trans (Assembly.a_mono S (Nat.le_add_right q 2))) u hu).2
  have hcutGate: ∀ u ∈ rho.honest,
      (rho.storeBeforeTime S u (S.a (q - 1) + S.E.Δ)).h_j + 2 ≤ M:= fun u hu =>
    (hwindow (S.a (q - 1) + S.E.Δ)
      ((Assembly.a_mono S hbasePred).trans
        (le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)))
      (hprevDelta.trans (Assembly.a_mono S (Nat.le_add_right q 2))) u hu).1
  have hfrontier: ∀ u ∈ rho.honest,
      (rho.storeBeforeTime S u (S.a q)).h_max = M:= fun u hu =>
    (hwindow (S.a q) (Assembly.a_mono S hbaseQ)
      (Assembly.a_mono S (Nat.le_add_right q 2)) u hu).2
  have hgate: ∀ u ∈ rho.honest,
      (rho.storeBeforeTime S u (S.a q)).h_j + 2 ≤ M:= fun u hu =>
    (hwindow (S.a q) (Assembly.a_mono S hbaseQ)
      (Assembly.a_mono S (Nat.le_add_right q 2)) u hu).1
  -- The round's regime predicates.
  have hready: GradeRoundReady S rho q:= by
    refine gradeRoundReady_of_action_horizon S ?_ (le_refl q) hactionHor
    have h:= gst_le_Γ_neg1_succ S (q - 1) hpostPrev
    rwa [hqPred] at h
  have hsettled: SelectedG2SettledAt S rho q:=
    selectedG2SettledAt_of_gateOff S adm hfb hqpos hpostPrev hprevFrontier
      hfrontier hgate hactionHor
  have hg1: LiveG1SettledAt S rho q:=
    liveG1SettledAt_of_gateOff S adm hfb hqpos hpostPrev hprevFrontier
      hfrontier hgate hactionHor
  have hpostProposal: S.E.t_GST ≤
      Protocol.proposal_time S.E (S.hc.opening_slot q):= by
    refine hpostPrev.trans ?_
    refine (le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans ?_
    exact action_add_delta_le_openingProposal_of_round_lt S
      (by rw [hqPred] at *; exact Nat.sub_lt hqpos Nat.zero_lt_one)
  have hpostOpeningVote: S.E.t_GST ≤
      Protocol.vote_time S.E (S.hc.opening_slot q):=
    hpostProposal.trans
      (le_of_lt (Protocol.proposal_time_lt_vote_time S.E _))
  have hopeningHor: Protocol.confirmation_time S.E
      (S.hc.opening_slot q) ≤ rho.horizon:= by
    rw [← Protocol.a_eq_confirmation_time]
    exact hactionHor
  -- The per-read gate-off window of the round.
  have hsupportLo: S.a base ≤
      Protocol.support_cutoff S.E (S.hc.opening_slot q):= by
    refine (Assembly.a_mono S hbasePred).trans ?_
    rw [← Protocol.Γ_2_eq_support_cutoff]
    refine le_trans ?_ (le_of_lt (Γ_1_lt_Γ_2 S.hc S.E.Δ_pos q))
    refine le_trans ?_ (le_of_lt (Γ_0_lt_Γ_1 S.hc S.E.Δ_pos q))
    refine le_trans ?_ (le_of_lt (Γ_neg1_lt_Γ_0 S.hc S.E.Δ_pos q))
    have h:= action_add_delta_le_next_Γ_neg1 S (q - 1)
    rw [hqPred] at h
    exact (le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans h
  have hsupportHi: Protocol.support_cutoff S.E (S.hc.opening_slot q) ≤
      S.a q:= by
    rw [← Protocol.Γ_2_eq_support_cutoff, Setup.a]
    exact Γ_2_le_a S.hc S.E.Δ_pos q
  have hwindowPrev: ∀ read: Time, S.a (q - 1) ≤ read →
      read ≤ Protocol.confirmation_time S.E
        (seedRoundLastSlot S (q - 1 + 1) - 1) →
      ∀ w ∈ rho.honest,
        (rho.storeBeforeTime S w read).h_j + 2 ≤ M ∧
          (rho.storeBeforeTime S w read).h_max = M:= by
    intro read hlo hhi w hw
    refine hwindow read ((Assembly.a_mono S hbasePred).trans hlo) ?_ w hw
    rw [hqPred] at hhi
    exact hhi.trans hlastConfLeEnd
  have hconeWindow: GateOffSeedConeWindowAt S rho M
      (S.hc.opening_slot q) (seedRoundLastSlot S q - 1):= by
    have hnext:= roundCeilingNextRegime_of_window S adm hfb (M:= M)
      (q:= q - 1) hpostPrev (by rw [hqPred]; exact hlastConfHor) hwindowPrev
    have h:= hnext.window
    rw [hqPred] at h
    exact h
  have hsupportFrontier: ∀ u ∈ rho.honest,
      (rho.storeBeforeTime S u
        (Protocol.support_cutoff S.E (S.hc.opening_slot q))).h_max = M:= by
    intro u hu
    exact (hwindow _ hsupportLo (hsupportHi.trans
      (Assembly.a_mono S (Nat.le_add_right q 2))) u hu).2
  have hsupportGate: ∀ u ∈ rho.honest,
      (rho.storeBeforeTime S u
        (Protocol.support_cutoff S.E
          (S.hc.opening_slot q))).h_j + 2 ≤ M:= by
    intro u hu
    exact (hwindow _ hsupportLo (hsupportHi.trans
      (Assembly.a_mono S (Nat.le_add_right q 2))) u hu).1
  have hslotWindow: ∀ read: Time, S.a (q - 1) ≤ read →
      read ≤ Protocol.confirmation_time S.E (seedRoundLastSlot S q - 1) →
      ∀ w ∈ rho.honest,
        (rho.storeBeforeTime S w read).h_j + 2 ≤ M ∧
          (rho.storeBeforeTime S w read).h_max = M:= by
    intro read hlo hhi w hw
    exact hwindow read ((Assembly.a_mono S hbasePred).trans hlo)
      (hhi.trans hlastConfLeEnd) w hw
  -- the previous round's regime, for its carrier frontier
  have hpostPrev2: S.E.t_GST ≤ S.a (q - 2):=
    hpostBase.trans (Assembly.a_mono S hbasePred2)
  have hprevActionHor: S.a (q - 1) ≤ rho.horizon:=
    (Assembly.a_mono S (hpredQ.trans (Nat.le_add_right q 2))).trans hhor
  have hprev2Frontier: ∀ u ∈ rho.honest,
      (rho.storeBeforeTime S u (S.a (q - 2))).h_max = M:= fun u hu =>
    (hwindow (S.a (q - 2)) (Assembly.a_mono S hbasePred2)
      ((Assembly.a_mono S hpred2Q).trans
        (Assembly.a_mono S (Nat.le_add_right q 2))) u hu).2
  have hprevGate: ∀ u ∈ rho.honest,
      (rho.storeBeforeTime S u (S.a (q - 1))).h_j + 2 ≤ M:= fun u hu =>
    (hwindow (S.a (q - 1)) (Assembly.a_mono S hbasePred)
      ((Assembly.a_mono S hpredQ).trans
        (Assembly.a_mono S (Nat.le_add_right q 2))) u hu).1
  have hreadyPrev: GradeRoundReady S rho (q - 1):= by
    refine gradeRoundReady_of_action_horizon S ?_ (le_refl (q - 1))
      hprevActionHor
    have h:= gst_le_Γ_neg1_succ S (q - 2) hpostPrev2
    rwa [hpred2Succ] at h
  have hsettledPrev: SelectedG2SettledAt S rho (q - 1):= by
    refine selectedG2SettledAt_of_gateOff S adm hfb hqPredPos ?_ ?_
      hprevFrontier hprevGate hprevActionHor
    · rw [hpredPred]; exact hpostPrev2
    · rw [hpredPred]; exact hprev2Frontier
  have hprevProposal: S.E.t_GST ≤
      Protocol.proposal_time S.E (S.hc.opening_slot (q - 1)):= by
    refine hpostPrev2.trans ?_
    refine (le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans ?_
    refine action_add_delta_le_openingProposal_of_round_lt S ?_
    rw [← hpred2Succ]
    exact Nat.lt_succ_self _
  have hprevOpeningHor: Protocol.confirmation_time S.E
      (S.hc.opening_slot (q - 1)) ≤ rho.horizon:= by
    rw [← Protocol.a_eq_confirmation_time]
    exact hprevActionHor
  obtain ⟨Cprev, W, holder, hholder, hWmem, hWrun, hCW, hWthin, hupper⟩:=
    exists_seedPreviousFrontier S adm hcom hfb hreadyPrev hsettledPrev
      hprevProposal hprevOpeningHor hgraded.selectedPrev hprevFrontier
      hprevGate
  have hheadThin: ∀ d: Slot, S.hc.opening_slot q ≤ d →
      d ≤ seedRoundLastSlot S q → ∀ X: Block V, HonestHead S rho d X →
        M - 1 ≤ (derived_state S.E S.cfg X).h:=
    seedRoundHeadsThin_of_previousFrontier S adm hfb hqpos hpostPrev
      (by
        refine le_trans ?_ hactionHor
        have h:= le_of_lt (next_Γ_neg1_lt_action S (q - 1))
        rw [hqPred] at h
        exact h)
      (hprevDelta.trans hactionHor) hlastConfHor hholder hWmem hWrun hCW
      hWthin hupper hcutFrontier hcutGate hconeWindow hslotWindow
  exact ⟨hheadThin (seedRoundLastSlot S q)
      (Nat.le_of_lt (openingSlot_lt_seedRoundLastSlot' S q)) (le_refl _),
    seedEntry_entry S adm hcom hfb hqpos hready hsettled hg1 hgraded
      hclearResidual
      hpostProposal hpostOpeningVote hopeningHor hlastConfHor
      hfrontier hgate hprevFrontier hcutFrontier hcutGate hsupportFrontier
      hsupportGate hpostPrev (hprevDelta.trans hactionHor) hconeWindow
      hheadThin⟩
-/

/-! ## The seed entry with the graded residual -/



/-
/-- **The first ceiling or the fixed root.** This is the complete gate-off
seed base against the height-progress hypotheses: the only protocol input left
is that the round's reads carry grades. -/
theorem seedFixedRoot_or_firstRoundCeiling_of_graded
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hfb: BelowOneThird S rho.honest)
    {M: Height} {base q endpoint: Round}
    (hM: honestHMaxAt S rho (S.a base) = M)
    (hpost: S.E.t_GST ≤ S.a base)
    (h2: 2 ≤ M)
    (hcap: honestHMaxAt S rho (S.a endpoint) ≤ M)
    (hhor: S.a endpoint ≤ rho.horizon)
    (hqlo: base + 4 ≤ q)
    (hqhi: q + 2 ≤ endpoint)
    (hgraded: SeedRoundGradedAt S rho q)
    (hclearResidual: SeedClearCarrierCompatiblePreviousAt S rho q):
    (∃ u ∈ rho.honest, ∃ read: Time, S.E.t_GST ≤ read ∧
      read ≤ S.a endpoint ∧
      FixedHeightJustificationRootAtRead S rho M u read) ∨
    ∃ B: Block V, RoundCeilingAt S rho M (q + 1) B:= by
  obtain ⟨hbaseTwo, hbaseOne⟩:= seedEntrySeed_nat hqlo
  rcases seedFixedRoot_or_gateOffWindow S adm hfb hM hpost h2 hcap hhor with
    hfix | hgate
  · exact Or.inl hfix
  · refine Or.inr ?_
    have hhorQ: S.a (q + 2) ≤ rho.horizon:=
      (Assembly.a_mono S hqhi).trans hhor
    have hpostBase: S.E.t_GST ≤ S.a (base + 1):=
      hpost.trans (Assembly.a_mono S (Nat.le_succ base))
    have hwindow: ∀ read: Time, S.a (base + 1) ≤ read →
        read ≤ S.a (q + 2) → ∀ w ∈ rho.honest,
          (rho.storeBeforeTime S w read).h_j + 2 ≤ M ∧
            (rho.storeBeforeTime S w read).h_max = M:= by
      intro read hlo hhi w hw
      exact hgate read hlo (hhi.trans (Assembly.a_mono S hqhi)) w hw
    have hadoption:= seedBoundaryAdoption_of_graded S adm hcom hfb
      hpostBase hbaseTwo hhorQ hwindow hgraded hclearResidual
    exact exists_roundCeiling_of_window_of_adoption S adm hcom hfb
      hpostBase hbaseOne hhorQ hwindow hadoption
-/

end HealingSurface
end Proofs
end DecoupledConsensusModel

namespace DecoupledConsensusModel.Proofs.HealingSurface
#print axioms seedEntryRoundOf
#print axioms seedEntryRoundOf'
end DecoupledConsensusModel.Proofs.HealingSurface

end
