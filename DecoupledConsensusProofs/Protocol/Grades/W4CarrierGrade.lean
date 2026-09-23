module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.W4FKGrade
public import DecoupledConsensusProofs.Protocol.Grades.GradeFormsBridge
public import DecoupledConsensusProofs.Protocol.Grades.HonestProposalRawLifecycleNamed
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.W4NonLost
public import DecoupledConsensusProofs.Execution.MovingChainRoundFloorFields
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.W4HeightSourceHistory

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# The grade at the carrier's floor, with the floor CHOSEN

, the corresponding branch. The kernel's last conceptual item: the round-`r` grade of a
floor that is the round-`(r-1)` OPENING PROPOSAL, rather than an arbitrary
floor. Choosing the floor is what makes the grade provable: the previous
round's opening proposal is both the height history's natural reference and a
block already delivered before the round-`r` G2-domain read, because
`S.a (r-1) + Δ ≤ Γ[-1] r`.

The producer uses four theorems for the corresponding branch.
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
open Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}




/-- **The same grade over the carrier band**, which is the cheaper route.

the corresponding branch's `movingChainFloor_coneWitnessAtDomainRead_of_carrierBand`
gives the domain-read cone witness from one numeric band, in place of the
canonical height history and the domain-read body membership (H4, H5): the
round-`r` opening proposal does not exist at the G2-domain read
(`domain … r.g2 = proposal_time (opening_slot r) - Δ`), so the frontier there
is the round-`(r-1)` height, and the band is the carrier's.

The band does NOT eliminate H4 and H5; it relocates them. Discharging it by
the shared frontier cap (`…_of_heightGates` below) needs the height gates and
the body membership again, now at the round-`(r-1)` OPENING PROPOSAL, where
the lifecycle already supplies them. Choosing the floor is what makes the
grade provable. -/
theorem namedGradeFormsAt_prevOpeningProposal_of_carrierBand
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hmajority : HonestWeightMajority S rho.honest)
    {q0 r : Round} (hr : 0 < r) {Pprev : NamedBlock V} {End : Block V}
    (hcover : ActionCarriersCover S rho (r - 1) Pprev.erase)
    (hdomainRoots : ∀ w ∈ rho.honest,
      Block.Preceq
        (Protocol.get_fg_root
          (rho.storeBeforeTime S w
            (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2)).core.toHealing.toFG)
        Pprev.erase)
    (hcarrier : MovingChainAtCarrierFor S rho q0 r Pprev.erase End)
    (hnotLost : ¬ LostRoundAt S rho r)
    (hband : ∀ w ∈ rho.honest,
      (rho.storeBeforeTime S w
          (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2)).core.h_max - 1 ≤
        ((rho.storeBeforeTime S w
            (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2)).core.σ
          (actionSGBlockAt S rho w (r - 1))).h)
    (hactionRoots : ∀ v ∈ rho.honest,
      Block.Preceq
        (Protocol.get_fg_root
          (rho.storeBeforeTime S v (S.a r)).core.toHealing.toFG)
        Pprev.erase)
    (hwitness : ∀ v ∈ rho.honest,
      CanonicalConeWitness (rho.storeBeforeTime S v (S.a r)).core Pprev.erase)
    (hpost : S.E.t_GST ≤ S.a (r - 1))
    (hcut : S.hc.Γ_neg1 S.E.Δ r ≤ rho.horizon) :
    NamedGradeFormsAt S rho r Pprev.erase := by
  have hr1 : r - 1 + 1 = r := Nat.succ_pred_eq_of_pos hr
  have hconeDomain := movingChainFloor_coneWitnessAtDomainRead_of_carrierBand
    S adm hr hcarrier hnotLost hband
  have hactiveDomain := gradeFloor_active_at_read S adm hdomainRoots hconeDomain
  have hactive := gradeFloor_active_at_read S adm hactionRoots hwitness
  have hbridge := namedGradeFormsAt_succ_of_actionCarriersCover_and_next_active
    S adm hmajority (r := r - 1) (P := Pprev.erase) hcover hpost
    (by rw [hr1]; exact hcut) (by rw [hr1]; exact hactive)
    (by rw [hr1]; exact hactiveDomain)
  rwa [hr1] at hbridge

#print axioms namedGradeFormsAt_prevOpeningProposal_of_carrierBand

/-! ### Two private helpers of `W4NonLostRun`, reproduced (they cannot be
imported); renamed with a `w4u` prefix so the originals stay unambiguous. -/

private theorem w4uOpeningSlotAddTwoLe
    (S : Setup V) {m r : Round} (h : m < r) :
    S.hc.opening_slot m + 2 ≤ S.hc.opening_slot r := by
  have hR : 2 ≤ S.hc.R := S.hc.R_ge_two
  have hstep : (m + 1) * S.hc.R ≤ r * S.hc.R := Nat.mul_le_mul_right _ h
  simp only [Protocol.HealConfig.opening_slot]
  calc
    m * S.hc.R + 2 ≤ m * S.hc.R + S.hc.R := Nat.add_le_add_left hR _
    _ = (m + 1) * S.hc.R := by ring
    _ ≤ r * S.hc.R := hstep

/-- Verbatim copy of the private helper `runBlock_of_mem_storeBeforeTime`
(`FGSafetyRootNamedRun.lean:21`); the original is `private`. -/
private theorem w4RunBlockOfMemStoreBeforeTime
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {w : V} (hw : w ∈ rho.honest) {t : Time} {D : NamedBlock V}
    (hD : D ∈ (rho.storeBeforeTime S w t).bodies) : RunBlock S rho D := by
  obtain ⟨n, hn, -⟩ :=
    Proofs.Bridges.stateBeforeTime_eq_stateBefore S adm.toNamedScheduleWellFormed t
  have hD' : D ∈ (rho.stateBefore S n w).st.bodies := by
    simpa only [Run.storeBeforeTime, hn] using hD
  exact Proofs.Bridges.runBlock_of_stateBefore_mem S hw hD'

/-- Verbatim copy of the private helper
`NamedHeightRegimeRun.fgRoot_compatible_after_source_run`
(`FGSafetyRootNamedRun.lean:47`); the original is `private`. -/
private theorem w4uFgRootCompatibleAfterSourceRun
    {S : Setup V} {rho : Run V} {r0 : Round} {blocked : Height}
    {first i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg T Tprev : NamedBlock V} {c0 : Round}
    (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    (h : NamedHeightRegimeRun S rho r0 blocked first i a ta
      Cfg T Tprev c0)
    {read : Time} (hread : S.a a.round ≤ read)
    (hreadHor : read ≤ rho.horizon) {w : V} (hw : w ∈ rho.honest) :
    Block.compatible
      (Protocol.get_fg_root
        (rho.storeBeforeTime S w read).toHealing.toFG) T.erase = true := by
  apply h.seed.fgRoot_compatible_of_recentWitnessHistory_of_frame_run
    adm hcom hbelow h.crossing h.frame h.c0le h.ready h.postPrev
      h.g1 h.pred h.minimal hread
  · intro r hr ht v hv W hW
    exact ((h.laterHistory_main adm hcom hbelow hr).2
      (ht.le.trans hreadHor)).2 v hv W hW
  · exact hw

/-! ## H2, the domain-read root bound

The read-parametric twin of `w4FgRoot_preceq_openingProposal_after_SG_healing`
(`W4NonLostRun.lean:107`), copied and generalized from the action read
`S.a (p + 1)` to any read between the two action instants, because the
G2-domain read of round `p + 1` lies there. The body uses the read only
through the deadline bound, the horizon bound, and the one round-inversion
step, so all three are supplied by the new bounds. `W4NonLostRun` is
unchanged. -/

theorem w4uFgRoot_preceq_openingProposal_at_read
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {p : Round} {P : NamedBlock V}
    (hp : fgSafetyProgressDeadline S rho rGST gap delayExtra + 2 ≤ p)
    (hheads : ∀ v ∈ rho.honest,
      voteDutyHead S rho v (S.hc.opening_slot p) = P.erase)
    (hsource : ∀ w ∈ rho.honest, ∀ X : Block V,
      actionFGSource S (actionStoreAt S rho w p) = some X → X = P.erase)
    {read : Time}
    (hreadLow : S.a p ≤ read)
    (hreadHigh : read ≤ S.a (p + 1))
    (hhor : read ≤ rho.horizon)
    {u : V} (hu : u ∈ rho.honest) :
    Block.Preceq
      (Protocol.get_fg_root
        (rho.storeBeforeTime S u (read)).toHealing.toFG) P.erase := by
  classical
  have hpD : fgSafetyProgressDeadline S rho rGST gap delayExtra < p :=
    lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide : 0 < 2)) hp
  have hread : S.a (fgSafetyProgressDeadline S rho rGST gap delayExtra) ≤
      read :=
    ((action_strictMono S).monotone hpD.le).trans hreadLow
  have hactionP : S.a p ≤ read := hreadLow
  have hshor : Protocol.vote_time S.E (S.hc.opening_slot p) + S.E.Δ ≤
      rho.horizon := by
    rw [vote_time_add_delta]
    refine (support_cutoff_le_confirmation_time S.E (S.hc.opening_slot p)).trans ?_
    rw [opening_confirmation_time_eq_action]
    exact hactionP.trans hhor
  have hs : S.hc.opening_slot (fgSafetyProgressDeadline S rho rGST gap delayExtra)
      + 1 ≤ S.hc.opening_slot p :=
    (Nat.add_le_add_left (by decide : (1 : Nat) ≤ 2) _).trans
      (w4uOpeningSlotAddTwoLe S hpD)
  obtain ⟨blocked, first, Tprev, hfirst, hbase⟩ :=
    exists_namedHeightRegimeBaseRun_before_fgSafetyProgressDeadline
      S adm hcom hbelow hrec hdelay hpost (hread.trans hhor)
  have hgst := gstLagged_le_Γ_neg1_of_gst_le_a S rGST hpost
  let R := Protocol.get_fg_root
    (rho.storeBeforeTime S u (read)).toHealing.toFG
  change Block.Preceq R P.erase
  rcases fgRoot_confirmationWitness_at_read S adm.toNamedAdmissibleCore
      (AlignedRoundLemmas.honestWeightMajority_of_belowOneThird hbelow)
      hu (read) with
    hgen | ⟨C, hC, hJ, b, tb, hb, hemit, hbt, hpair, hW⟩
  · rw [show R = Block.genesis from hgen]
    exact Protocol.preceq_genesis _
  · have hrowHeight : b.height_pair.erase.height? =
        some (Protocol.derive_named S.E S.cfg C).h_j := by
      rw [hpair]
      rfl
    by_cases hsmall :
        (Protocol.derive_named S.E S.cfg C).h_j ≤ blocked
    · obtain ⟨i, a, ta, Cfg, T, hreg, ha⟩ :=
        hbase.exists_regime_before_deadline adm hbelow hgst hfirst
      have hRT := w4uFgRootCompatibleAfterSourceRun adm hcom hbelow hreg
        (((action_strictMono S).monotone ha).trans hread) hhor hu
      have hRTpre : Block.Preceq R T.erase := by
        by_cases hz : (Protocol.derive_named S.E S.cfg C).h_j = 0
        · have hgenJ :=
            NamedJustificationCertificates.justified_zero_is_genesis
              S.E S.cfg C hz
          have hRgen : R = Block.genesis := by
            dsimp only [R]
            exact hJ.symm.trans hgenJ
          rw [hRgen]
          exact Protocol.preceq_genesis _
        · obtain ⟨J, hJC, hJerase, hJheight⟩ :=
            (NamedCheckpointHeights.justified_ancestor_height
              S.E S.cfg C).resolve_left hz
          have hCrun : RunBlock S rho C :=
            w4RunBlockOfMemStoreBeforeTime S adm hu hC
          have hJrun : RunBlock S rho J :=
            Proofs.NamedRuntime.blockInRun_of_ancestor S rho hCrun hJC
          obtain ⟨hTrun, hTheight⟩ := hreg.checkpoint_runBlock adm
          rcases (show Block.Preceq R T.erase ∨ Block.Preceq T.erase R by
            simpa only [Block.compatible, Bool.or_eq_true] using hRT) with
            hRT | hTR
          · exact hRT
          · have hTJ : NamedBlock.Preceq T J :=
              Protocol.namedPreceq_of_runBlock_erase_preceq
                adm hTrun hJrun (by simpa only [hJ, hJerase] using hTR)
            have hmono := Proofs.NamedEntryHeight.derive_height_mono
              S.E S.cfg hTJ
            rw [hTheight, hJheight] at hmono
            exact False.elim
              (Nat.not_succ_le_self blocked (hmono.trans hsmall))
      have hopen : S.hc.opening_slot a.round + 1 ≤ S.hc.opening_slot p :=
        (Nat.add_le_add_right (Nat.mul_le_mul_right S.hc.R ha) 1).trans hs
      refine Block.preceq_trans hRTpre ?_
      rw [← hheads u hu]
      exact hreg.heads_from_firstInterior adm hcom hbelow hopen hshor u hu
    · have hactLt : S.a b.round < read := by
        simpa only [(Proofs.Optimistic.emits_attest_shape S hemit).2] using hbt
      have hbp : b.round ≤ p :=
        Nat.le_of_lt_succ ((action_strictMono S).lt_iff_lt.mp (hactLt.trans_le hreadHigh))
      rcases lt_or_eq_of_le hbp with hlt | hlast
      · let n := (Protocol.derive_named S.E S.cfg C).h_j - (blocked + 1)
        have heqn : blocked + n + 1 =
            (Protocol.derive_named S.E S.cfg C).h_j := by
          calc
            _ = n + (blocked + 1) := by ac_rfl
            _ = (Protocol.derive_named S.E S.cfg C).h_j :=
              Nat.sub_add_cancel (Nat.lt_of_not_ge hsmall)
        have hrow : b.height_pair.erase.height? = some (blocked + n + 1) := by
          rw [hrowHeight]
          exact congrArg some heqn.symm
        obtain ⟨first_n, i, a, ta, Cfg, T, Tprev', c0, hreg⟩ :=
          hbase.exists_regime_of_row_named adm hcom hbelow hgst n hb hemit hrow
        have hTR : T.erase = R := Option.some.inj
          ((hreg.witness_eq adm hcom hbelow hb hemit hrow).symm.trans hW)
        have hab : a.round ≤ b.round := hreg.minimal b tb hb hemit hrow
        have hopen : S.hc.opening_slot a.round + 1 ≤ S.hc.opening_slot p :=
          (Nat.add_le_add_left (by decide : (1 : Nat) ≤ 2) _).trans
            (w4uOpeningSlotAddTwoLe S (lt_of_le_of_lt hab hlt))
        rw [← hTR, ← hheads u hu]
        exact hreg.heads_from_firstInterior adm hcom hbelow hopen hshor u hu
      · obtain ⟨Db, Kb, hfg, hDb, hsrc, hDbh, hKb, hKerase, hKh, hKD, -⟩ :=
          honestHeightRow_confirmationWitness S adm hb hemit hrowHeight
        have hRK : R = (Protocol.derive_named S.E S.cfg Kb).T_h :=
          Option.some.inj (hW.symm.trans hfg)
        have hDbP : Db.erase = P.erase :=
          hsource b.val_index hb Db.erase (by rw [← hlast]; exact hsrc)
        rw [hRK, ← hDbP]
        exact Block.preceq_trans
          (Proofs.Optimistic.derive_named_T_h_preceq S.E S.cfg Kb) hKD


#print axioms w4uFgRoot_preceq_openingProposal_at_read



theorem namedGradeFormsAt_prevOpeningProposal_of_lifecycle
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    (hmajority : HonestWeightMajority S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {q0 r : Round} (hr : 0 < r) {Pprev : NamedBlock V} {End : Block V}
    (hm : fgSafetyProgressDeadline S rho rGST gap delayExtra + 2 ≤ r - 1)
    (hopeningPrev : S.E.proposer (S.hc.opening_slot (r - 1)) ∈ rho.honest)
    (hP : proposedBlockAt S rho (S.hc.opening_slot (r - 1)) = some Pprev)
    (hhorOpen : Protocol.confirmation_time S.E
      (S.hc.opening_slot (r - 1)) ≤ rho.horizon)
    (hheads : ∀ v ∈ rho.honest,
      voteDutyHead S rho v (S.hc.opening_slot (r - 1)) = Pprev.erase)
    (hsource : ∀ w ∈ rho.honest, ∀ X : Block V,
      actionFGSource S (actionStoreAt S rho w (r - 1)) = some X →
        X = Pprev.erase)
    (hhorAction : S.a r ≤ rho.horizon)
    (hcarrierRec : MovingChainAtCarrierFor S rho q0 r Pprev.erase End)
    (hnotLost : ¬ LostRoundAt S rho r)
    (hband : ∀ w ∈ rho.honest,
      (rho.storeBeforeTime S w
          (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2)).core.h_max - 1 ≤
        ((rho.storeBeforeTime S w
            (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2)).core.σ
          (actionSGBlockAt S rho w (r - 1))).h)
    (hwitness : ∀ v ∈ rho.honest,
      CanonicalConeWitness (rho.storeBeforeTime S v (S.a r)).core Pprev.erase)
    (hpostPrev : S.E.t_GST ≤ S.a (r - 1))
    (hcut : S.hc.Γ_neg1 S.E.Δ r ≤ rho.horizon) :
    NamedGradeFormsAt S rho r Pprev.erase := by
  have hr1 : r - 1 + 1 = r := Nat.succ_pred_eq_of_pos hr
  have hdomainLow : S.a (r - 1) ≤ DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2 :=
    action_pred_le_domain_g2 S hr
  have hdomainHigh : DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2 ≤ S.a r := by
    have h := next_Γ_neg1_lt_action S (r - 1)
    rw [gammaNeg1_eq_domain_g2_succ S (r - 1), hr1] at h
    exact le_of_lt h
  have hcover : ActionCarriersCover S rho (r - 1) Pprev.erase := by
    intro v hv
    rw [(honestProposal_actionSelectors_after_SG_healing_named_of_openingProposer
      S adm hcom hbelow hrec hdelay hpost hm hopeningPrev hP hhorOpen v hv).1]
    exact Block.preceq_self _
  have hactionHigh : S.a r ≤ S.a (r - 1 + 1) := by rw [hr1]
  have hdomainRoots : ∀ w ∈ rho.honest,
      Block.Preceq
        (Protocol.get_fg_root
          (rho.storeBeforeTime S w
            (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2)).core.toHealing.toFG)
        Pprev.erase := by
    intro w hw
    exact w4uFgRoot_preceq_openingProposal_at_read S adm hcom hbelow hrec
      hdelay hpost hm hheads hsource hdomainLow
      (hdomainHigh.trans hactionHigh) (hdomainHigh.trans hhorAction) hw
  have hactionRoots : ∀ v ∈ rho.honest,
      Block.Preceq
        (Protocol.get_fg_root
          (rho.storeBeforeTime S v (S.a r)).core.toHealing.toFG)
        Pprev.erase := by
    intro v hv
    exact w4uFgRoot_preceq_openingProposal_at_read S adm hcom hbelow hrec
      hdelay hpost hm hheads hsource
      ((action_strictMono S).monotone (Nat.pred_le r)) hactionHigh hhorAction hv
  exact namedGradeFormsAt_prevOpeningProposal_of_carrierBand S adm hmajority hr
    hcover hdomainRoots hcarrierRec hnotLost hband hactionRoots hwitness
    hpostPrev hcut

#print axioms namedGradeFormsAt_prevOpeningProposal_of_lifecycle



theorem namedGradeFormsAt_prevOpeningProposal_of_record
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    (hmajority : HonestWeightMajority S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {q0 r : Round} (hr : 0 < r) {Pprev Pr : NamedBlock V} {End : Block V}
    (hm : fgSafetyProgressDeadline S rho rGST gap delayExtra + 2 ≤ r - 1)
    (hopeningPrev : S.E.proposer (S.hc.opening_slot (r - 1)) ∈ rho.honest)
    (hP : proposedBlockAt S rho (S.hc.opening_slot (r - 1)) = some Pprev)
    (hhorOpen : Protocol.confirmation_time S.E
      (S.hc.opening_slot (r - 1)) ≤ rho.horizon)
    (hheads : ∀ v ∈ rho.honest,
      voteDutyHead S rho v (S.hc.opening_slot (r - 1)) = Pprev.erase)
    (hsource : ∀ w ∈ rho.honest, ∀ X : Block V,
      actionFGSource S (actionStoreAt S rho w (r - 1)) = some X →
        X = Pprev.erase)
    (hhorAction : S.a r ≤ rho.horizon)
    (hcarrierRec : MovingChainAtCarrierFor S rho q0 r Pprev.erase End)
    (hnotLost : ¬ LostRoundAt S rho r)
    (hband : ∀ w ∈ rho.honest,
      (rho.storeBeforeTime S w
          (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2)).core.h_max - 1 ≤
        ((rho.storeBeforeTime S w
            (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2)).core.σ
          (actionSGBlockAt S rho w (r - 1))).h)
    (hPrevPr : Block.Preceq Pprev.erase Pr.erase)
    (hbodies : ∀ v ∈ rho.honest,
      Pr ∈ (rho.storeBeforeTime S v (S.a r)).bodies)
    (hbandR : ∀ v ∈ rho.honest,
      (rho.storeBeforeTime S v (S.a r)).h_max - 1 ≤
        (Protocol.derive_named S.E S.cfg Pr).h)
    (hpostPrev : S.E.t_GST ≤ S.a (r - 1))
    (hcut : S.hc.Γ_neg1 S.E.Δ r ≤ rho.horizon) :
    NamedGradeFormsAt S rho r Pprev.erase := by
  have hwitness : ∀ v ∈ rho.honest,
      CanonicalConeWitness (rho.storeBeforeTime S v (S.a r)).core
        Pprev.erase := by
    intro v hv
    exact canonicalConeWitness_of_bandDescendant S hPrevPr (hbodies v hv)
      (hbandR v hv)
  exact namedGradeFormsAt_prevOpeningProposal_of_lifecycle S adm hcom hbelow
    hmajority hrec hdelay hpost hr hm hopeningPrev hP hhorOpen hheads hsource
    hhorAction hcarrierRec hnotLost hband hwitness hpostPrev hcut

#print axioms namedGradeFormsAt_prevOpeningProposal_of_record













/-- **The grade from the height gates at the G2-domain read.**

`hgates` and `hmemDomain` are w4-h1's two hypotheses at `t:= Γ[-1] r`; the cap
they give bounds the honest sup of the strict stores there, which is the band.

The binder list is `_of_frontierCap`'s with `hfrontier` replaced in place, so a
caller swaps one hypothesis and one name and nothing else: the honest quorum
w4-h1's cap needs comes from `hbelow` in this leaf
(`AlignedRoundLemmas.honestQuorum_of_belowOneThird`). -/
theorem namedGradeFormsAt_prevOpeningProposal_of_heightGates
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    (hmajority : HonestWeightMajority S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {q0 r : Round} (hr : 0 < r) {Pprev Pr : NamedBlock V} {End : Block V}
    (hm : fgSafetyProgressDeadline S rho rGST gap delayExtra + 2 ≤ r - 1)
    (hopeningPrev : S.E.proposer (S.hc.opening_slot (r - 1)) ∈ rho.honest)
    (hP : proposedBlockAt S rho (S.hc.opening_slot (r - 1)) = some Pprev)
    (hhorOpen : Protocol.confirmation_time S.E
      (S.hc.opening_slot (r - 1)) ≤ rho.horizon)
    (hheads : ∀ v ∈ rho.honest,
      voteDutyHead S rho v (S.hc.opening_slot (r - 1)) = Pprev.erase)
    (hsource : ∀ w ∈ rho.honest, ∀ X : Block V,
      actionFGSource S (actionStoreAt S rho w (r - 1)) = some X →
        X = Pprev.erase)
    (hhorAction : S.a r ≤ rho.horizon)
    (hcarrierRec : MovingChainAtCarrierFor S rho q0 r Pprev.erase End)
    (hnotLost : ¬ LostRoundAt S rho r)
    (hgates : Protocol.PastHonestHeightGatesBelow S rho
      (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2) Pprev)
    (hcarrierEq : ∀ w ∈ rho.honest,
      actionSGBlockAt S rho w (r - 1) = Pprev.erase)
    (hmemDomain : ∀ w ∈ rho.honest,
      Pprev ∈ (rho.storeBeforeTime S w
        (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2)).bodies)
    (hPrevPr : Block.Preceq Pprev.erase Pr.erase)
    (hbodies : ∀ v ∈ rho.honest,
      Pr ∈ (rho.storeBeforeTime S v (S.a r)).bodies)
    (hbandR : ∀ v ∈ rho.honest,
      (rho.storeBeforeTime S v (S.a r)).h_max - 1 ≤
        (Protocol.derive_named S.E S.cfg Pr).h)
    (hpostPrev : S.E.t_GST ≤ S.a (r - 1))
    (hcut : S.hc.Γ_neg1 S.E.Δ r ≤ rho.horizon) :
    NamedGradeFormsAt S rho r Pprev.erase := by
  have hheld : ∀ v ∈ rho.honest,
      Pprev ∈ (rho.stateBeforeTime S (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2) v).st.bodies := by
    intro v hv
    simpa only [Run.storeBeforeTime] using hmemDomain v hv
  have hcap := w4HonestFrontier_le_succ_of_heightGates S adm hcom
    (AlignedRoundLemmas.honestQuorum_of_belowOneThird hbelow) hgates hheld
  have hband : ∀ w ∈ rho.honest,
      (rho.storeBeforeTime S w (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2)).core.h_max - 1 ≤
        ((rho.storeBeforeTime S w (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2)).core.σ
          (actionSGBlockAt S rho w (r - 1))).h := by
    intro w hw
    have hsup : (rho.storeBeforeTime S w (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2)).core.h_max ≤
        honestHMaxBeforeIndex S rho (strictEventIndex rho (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2)) := by
      rw [storeBeforeTime_eq_stateBefore_strictEventIndex S
        adm.toNamedScheduleWellFormed w (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2)]
      simpa only [honestHMaxBeforeIndex] using
        (Finset.le_sup
          (f := fun v => (rho.stateBefore S (strictEventIndex rho (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2)) v).st.h_max)
          hw)
    have hview : (rho.storeBeforeTime S w (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2)).core.σ Pprev.erase =
        Protocol.derive_named S.E S.cfg Pprev := by
      simpa only [Run.storeBeforeTime] using
        Proofs.NamedStoreBridge.derivedView_stateBeforeTime S rho (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2) w Pprev
          (by simpa only [Run.storeBeforeTime] using hmemDomain w hw)
    rw [hcarrierEq w hw, hview]
    exact Nat.sub_le_iff_le_add.mpr (le_trans hsup hcap)
  exact namedGradeFormsAt_prevOpeningProposal_of_record S adm hcom hbelow
    hmajority hrec hdelay hpost hr hm hopeningPrev hP hhorOpen hheads hsource
    hhorAction hcarrierRec hnotLost hband hPrevPr hbodies hbandR hpostPrev hcut

#print axioms namedGradeFormsAt_prevOpeningProposal_of_heightGates




end HealingSurface
end Proofs
end DecoupledConsensusModel

end
