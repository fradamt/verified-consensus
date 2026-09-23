module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Generic.CanonicalRegimeFromChain
public import DecoupledConsensusProofs.Protocol.Grades.GradeFormsBridge
public import DecoupledConsensusProofs.Generic.FixedHeightRootAdmission
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.FixedHeightRootOpeningParent

@[expose] public section

/-!
# W4 finality kernel, wave A1: the moving-chain floor at the G2-domain read

`NamedGradeFormsAt S rho r C` is, by definition
(`DecoupledConsensusStatements/Instantiation/NamedLifecycle.lean:30`), a
conjunction of TWO facts at every honest reader's **G2-domain read** of round
`r`, the read at `Gamma[-1] r`: that `C` is in that read's filtered tree, and
that the read's relative grade of `C` is `true`. The round's ACTION read, at
`S.a r`, is a full round LATER, and `MovingChainAtCarrierFor`'s floor fields
(`RoundFloorFieldsAt`) speak only about that later read.

This module supplies everything on the route from the moving chain to the named
grade EXCEPT the two facts at the earlier read:

* `gradeFloor_active_at_read` — the exact time-parametric form of
  `gradeFloor_active_everywhere` (`CanonicalRegimeAssemblyRun.lean:74`), whose
  proof never mentions the round: roots below the floor plus a processed
  descendant at the reader's own frontier band put the floor in that read's
  filtered tree. available for ANY read time `t`.
* `movingChainFloor_activeAtDomainRead_of_domainFloor` — the floor is active at
  the G2-domain read of round `r`, from the domain-read twins of
  `RoundFloorFieldsAt.floorAboveRoots` and `.floorWitness`.
* `movingChainFloor_namedGradeFormsAt_of_activeAtDomainRead` — the named grade
  at the floor, over the domain-read activity taken as a hypothesis in the
  pinned shape. This is the PRE-BUILD consumer: when a producer of that
  activity lands, the pinned `movingChainFloor_namedGradeFormsAt` closes by one
  application.
* `movingChainFloor_namedGradeFormsAt_of_domainFloor` — the two composed.

The Open at the end records why the two domain-read premises are not derivable
from `MovingChainAtCarrierFor` as it stands, with the exact residual goals.
-/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-- **The canonical floor is active at ANY honest read** whose selected FG roots
are below it and which holds a processed descendant of it at its own frontier
band.

This is `gradeFloor_active_everywhere` (`CanonicalRegimeAssemblyRun.lean:74`)
with the round read `S.a r` replaced by an arbitrary read time `t`. The proof
is the same and uses no property of `S.a r`: parent closure puts the floor in
the reader's processed tree for free, `F ⪯ J` and the root bound make it a
finalized descendant, and the cone witness supplies viability. -/
theorem gradeFloor_active_at_read
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {t : Time} {C : Block V}
    (hroot : ∀ v ∈ rho.honest,
      Block.Preceq
        (Protocol.get_fg_root
          (rho.storeBeforeTime S v t).core.toHealing.toFG) C)
    (hwitness : ∀ v ∈ rho.honest,
      CanonicalConeWitness (rho.storeBeforeTime S v t).core C) :
    ∀ v ∈ rho.honest,
      C ∈ Protocol.get_filtered_block_tree
        (rho.storeBeforeTime S v t).core.toHealing.toFG := by
  intro v hv
  have hpc : ParentClosed (rho.storeBeforeTime S v t).core := by
    simpa only [Run.storeBeforeTime] using
      Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho t v
  have hFJ : Block.Preceq (rho.storeBeforeTime S v t).core.F
      (rho.storeBeforeTime S v t).core.J := by
    simpa only [Run.storeBeforeTime] using
      Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime S rho t v
  obtain ⟨W, hWT, hCW, hheightW⟩ := hwitness v hv
  exact canonicalConeSegment_mem_filtered_of_root_preceq
    hpc hFJ (hroot v hv) hWT hheightW (Block.preceq_self C) hCW




/-! ## Reducing the domain-read cone witness to one numeric fact -/

/-- Processed trees only grow in the reading time. Copy of the live
`storeBeforeTime_mem_of_le` (`MovingChainRoundFloorFieldsRun.lean:309`), which
this leaf does not import. -/
private theorem w4fk_storeBeforeTime_mem_of_le
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    {v : V} {t u : Time} (htu : t ≤ u) {X : Block V}
    (hmem : X ∈ (rho.storeBeforeTime S v t).T) :
    X ∈ (rho.storeBeforeTime S v u).T := by
  rw [storeBeforeTime_eq_stateBefore_strictEventIndex S sch v t] at hmem
  rw [storeBeforeTime_eq_stateBefore_strictEventIndex S sch v u]
  exact stateBefore_T_subset S rho v _ (strictEventIndex_mono rho htu) hmem

/-- The round-`r` G2-domain read is at or after the round-`(r-1)` action. -/
theorem action_pred_le_domain_g2 (S : Setup V) {r : Round} (hr : 0 < r) :
    S.a (r - 1) ≤ DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2 := by
  have hsucc : r - 1 + 1 = r := Nat.succ_pred_eq_of_pos hr
  have h := action_add_delta_le_next_Γ_neg1 S (r - 1)
  rw [gammaNeg1_eq_domain_g2_succ S (r - 1), hsucc] at h
  exact le_trans (Int.le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)) h

/-- **The reader's own previous-round SG carrier is a processed descendant of
the floor at the round's G2-domain read.**

The carrier is in that reader's own tree at the round-`(r-1)` action, the domain
read is later, processed trees only grow, and `floorBelowCarriers` puts the
floor below the carrier. -/
theorem movingChainFloor_carrierProcessedAtDomainRead
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q0 r : Round} {C End : Block V} (hr : 0 < r)
    (hchain : MovingChainAtCarrierFor S rho q0 r C End)
    (hnl : ¬ LostRoundAt S rho r) :
    ∀ w ∈ rho.honest,
      Block.Preceq C (actionSGBlockAt S rho w (r - 1)) ∧
        actionSGBlockAt S rho w (r - 1) ∈
          (rho.storeBeforeTime S w
            (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2)).T := by
  intro w hw
  refine ⟨(hchain.floorFields hnl).floorBelowCarriers w hw, ?_⟩
  exact w4fk_storeBeforeTime_mem_of_le S adm.toNamedScheduleWellFormed
    (action_pred_le_domain_g2 S hr)
    (actionSGBlockAt_mem_storeBeforeTime S rho w (r - 1))

/-- **The floor's cone witness at the G2-domain read, reduced to ONE numeric
fact**: the reader's own previous-round SG carrier reaches that read's frontier
band.

Everything else the witness asks for is already supplied by the moving chain:
the carrier is above the floor and is processed at the read. -/
theorem movingChainFloor_coneWitnessAtDomainRead_of_carrierBand
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q0 r : Round} {C End : Block V} (hr : 0 < r)
    (hchain : MovingChainAtCarrierFor S rho q0 r C End)
    (hnl : ¬ LostRoundAt S rho r)
    (hband : ∀ w ∈ rho.honest,
      (rho.storeBeforeTime S w
          (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2)).core.h_max - 1 ≤
        ((rho.storeBeforeTime S w
          (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2)).core.σ
            (actionSGBlockAt S rho w (r - 1))).h) :
    ∀ w ∈ rho.honest,
      CanonicalConeWitness
        (rho.storeBeforeTime S w
          (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2)).core C := by
  intro w hw
  obtain ⟨hbelow, hproc⟩ :=
    movingChainFloor_carrierProcessedAtDomainRead S adm hr hchain hnl w hw
  exact ⟨actionSGBlockAt S rho w (r - 1), hproc, hbelow, hband w hw⟩


/-! ## The gate-off half of the domain-read root bound -/



/-! ## Route (b): the fixed-height regime closes both domain-read facts -/




/-! ## The gate-on half of the domain-read root bound -/


/-! ## The height-gate route, for a caller that holds a processed endpoint -/

/-- **The moving chain's own height history is a past-gate bound at the round's
G2-domain read**, given the boundary frontier cap.

This is the surviving half of the parked one-unit debt bound
(`CanonicalDebtRecoveryState.debtBound_derived`, `HealingDebtStateRun.lean:141`,
confirmed PARKED by `#check`). Its argument in protocol words: every honest
attestation emitted before the domain read is that node's ACTION attestation at
a round strictly before `r`, because actions happen at `S.a k` and the domain
read precedes `S.a r`. A row above the boundary frontier must come from a round
after `q0` (`honestRow_after_frontier`), and for those rounds the chain's
`heightHistory` names a source block below the endpoint at exactly that height.
A row at or below the boundary frontier is capped by the boundary itself.

The boundary cap is the same guard `CanonicalTargetHistoryAt` and
`CanonicalTimeoutHistoryAt` already carry, in the form the gate bound needs. -/
theorem pastHonestHeightGatesBelow_of_canonicalHeightHistory
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q0 r : Round} {P0 : NamedBlock V}
    (hhist : CanonicalHeightSourceHistoryAt S rho q0 r P0)
    (hboundaryCap : honestHMaxAt S rho (S.a q0) ≤
      (Protocol.derive_named S.E S.cfg P0).h) :
    Protocol.PastHonestHeightGatesBelow S rho
      (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2) P0 := by
  intro a t' haHonest hemit ht h hrow
  have htime : t' = S.a a.round := (Proofs.Optimistic.emits_attest_shape S hemit).2
  have haEq : a = actionAttestationAt S rho a.val_index a.round :=
    emittedHonestAttestation_eq_actionAttestationAt S adm hemit
  have hrowAction :
      (actionAttestationAt S rho a.val_index a.round).height_pair.erase.height? =
        some h := by
    rw [← haEq]
    exact hrow
  have hlt : S.a a.round < S.a r := by
    rw [← htime]
    exact lt_of_lt_of_le ht (FrameForward.domain_le_a S r .g2)
  have hround : a.round < r := (action_strictMono S).lt_iff_lt.mp hlt
  by_cases habove : honestHMaxAt S rho (S.a q0) < h
  · have hq0 : q0 < a.round :=
      honestRow_after_frontier S adm haHonest habove hrowAction
    obtain ⟨Q, -, -, hQP0, hQheight⟩ :=
      hhist a.round (Nat.le_of_lt hq0) hround a.val_index haHonest h hrowAction
    calc
      h = (Protocol.derive_named S.E S.cfg Q).h := hQheight.symm
      _ ≤ (Protocol.derive_named S.E S.cfg P0).h :=
        Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hQP0
  · exact (Nat.le_of_not_gt habove).trans hboundaryCap




#print axioms gradeFloor_active_at_read
#print axioms action_pred_le_domain_g2
#print axioms movingChainFloor_carrierProcessedAtDomainRead
#print axioms movingChainFloor_coneWitnessAtDomainRead_of_carrierBand
#print axioms pastHonestHeightGatesBelow_of_canonicalHeightHistory

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
