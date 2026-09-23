module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Handlers.W4FKChainHandlerAdvance
public import DecoupledConsensusProofs.Protocol.Schedule.NamedTick
public import DecoupledConsensusProofs.Execution.Runtime
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge
public import DecoupledConsensusProofs.Protocol.Evidence.ProvenanceBridge
public import DecoupledConsensusProofs.Execution.W4FKChainStoreFinality

@[expose] public section

/-! # W4 branches fk-chain: the reader finality advance, transition by transition

`W4ProcessedFinalityAdvancePin` is a store invariant of the named runtime: a
reader that holds a named body has processed that body's rows, so its own
finalized block dominates the body's candidate checkpoint. This file proves it
in the shape of `NamedFinalityMonotone.node_process_F`: one statement per named
transition, then the world fold, then the transport to `Run.storeAt`.

Only one transition adds a body, `Protocol.NamedStore.process_block_core`, and
its step is `processBlockCore_advance`
(`W4FKChainHandlerAdvanceRun.lean`). Every other duty either leaves the bodies
alone and the finalized block alone, or leaves the bodies alone and advances the
finalized block, so the invariant rides through by finality monotonicity.

The side conditions the block step needs — coherence, the maximum carrier,
provenance, and the bodies being run blocks — all have premise-free producers at
`stateBefore`, and all four are invariant under `setClock`, which is the only
staging between a tick's prefix state and its proposal duty.
-/



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Protocol (derive_named)

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The invariant: every held named body's candidate checkpoint is at or below
the store's finalized block. -/
def NamedFinalityAdvance (S : Setup V) (st : Protocol.NamedStore V) : Prop :=
  ∀ D ∈ st.bodies, Block.Preceq (derive_named S.E S.cfg D).F st.core.F

/-! ## 1. Transitions that keep the bodies -/

theorem advance_of_bodies_eq_of_F
    (S : Setup V) {st st' : Protocol.NamedStore V}
    (hbodies : st'.bodies = st.bodies)
    (hF : Block.Preceq st.core.F st'.core.F)
    (hadv : NamedFinalityAdvance S st) : NamedFinalityAdvance S st' := by
  intro D hD
  rw [hbodies] at hD
  exact Block.preceq_trans (hadv D hD) hF

theorem advance_setClock (S : Setup V) (st : Protocol.NamedStore V) (t : Time)
    (hadv : NamedFinalityAdvance S st) :
    NamedFinalityAdvance S (Protocol.NamedStore.setClock S.E st t) :=
  advance_of_bodies_eq_of_F S rfl (Block.preceq_self _) hadv

theorem advance_admit_row (S : Setup V) (st : Protocol.NamedStore V)
    (row : NamedAttestation V) (hadv : NamedFinalityAdvance S st) :
    NamedFinalityAdvance S (Protocol.NamedAdmission.admit_row S.hc st row) := by
  refine advance_of_bodies_eq_of_F S (NamedAdmission.admit_row_bodies S.hc st row) ?_ hadv
  rw [NamedAdmission.admit_row_core, on_sg_vote_F]
  exact Block.preceq_self _

theorem advance_admit_rows (S : Setup V) (rows : List (NamedAttestation V)) :
    ∀ st : Protocol.NamedStore V, NamedFinalityAdvance S st →
      NamedFinalityAdvance S (Protocol.NamedAdmission.admit_rows S.hc st rows) := by
  induction rows with
  | nil => intro st h; exact h
  | cons row rows ih =>
      intro st h
      exact ih _ (advance_admit_row S st row h)

theorem advance_admit_carried (S : Setup V) (admission : Protocol.CarriedAdmission)
    (before after : Protocol.NamedStore V) (B : NamedBlock V)
    (hadv : NamedFinalityAdvance S after) :
    NamedFinalityAdvance S
      (Protocol.NamedAdmission.admit_carried admission S.hc before after B) := by
  cases admission with
  | alsoCarried =>
      simp only [Protocol.NamedAdmission.admit_carried]
      split_ifs
      · exact advance_admit_rows S B.attestations after hadv
      · exact hadv

/-! ## 2. The block transition -/

theorem admit_rows_bodies_eq (S : Setup V) (rows : List (NamedAttestation V)) :
    ∀ st : Protocol.NamedStore V,
      (Protocol.NamedAdmission.admit_rows S.hc st rows).bodies = st.bodies := by
  induction rows with
  | nil => intro st; rfl
  | cons row rows ih =>
      intro st
      show (Protocol.NamedAdmission.admit_rows S.hc
        (Protocol.NamedAdmission.admit_row S.hc st row) rows).bodies = st.bodies
      rw [ih, NamedAdmission.admit_row_bodies]

theorem admit_carried_bodies_eq (S : Setup V) (admission : Protocol.CarriedAdmission)
    (before after : Protocol.NamedStore V) (B : NamedBlock V) :
    (Protocol.NamedAdmission.admit_carried admission S.hc before after B).bodies =
      after.bodies := by
  cases admission with
  | alsoCarried =>
      simp only [Protocol.NamedAdmission.admit_carried]
      split_ifs
      · exact admit_rows_bodies_eq S B.attestations after
      · rfl

theorem on_block_with_bodies_eq (S : Setup V) (admission : Protocol.CarriedAdmission)
    (st : Protocol.NamedStore V) (B : NamedBlock V) :
    (Protocol.NamedAdmission.on_block_with admission S.E S.hc S.cfg st B).bodies =
      (Protocol.NamedStore.process_block_core S.E S.hc S.cfg st B).bodies := by
  simp only [Protocol.NamedAdmission.on_block_with]
  exact admit_carried_bodies_eq S admission st _ B

theorem advance_on_block_with
    (S : Setup V) {rho : Run V}
    (hsb : SlashableBound S rho) (hcf : RootCollisionFree S rho)
    (admission : Protocol.CarriedAdmission)
    {st : Protocol.NamedStore V} {B : NamedBlock V}
    (hcoh : Proofs.NamedStore.Coherent S.E S.cfg st)
    (hmax : ∃ D ∈ st.bodies, (derive_named S.E S.cfg D).h = st.core.h_max)
    (hprov : Proofs.Bridges.NamedProvenance S st)
    (hBrun : B ∈ (Protocol.NamedAdmission.on_block_with admission S.E S.hc S.cfg st B).bodies →
      RunBlock S rho B)
    (hRun : ∀ D ∈ st.bodies, RunBlock S rho D)
    (hadv : NamedFinalityAdvance S st) :
    NamedFinalityAdvance S
      (Protocol.NamedAdmission.on_block_with admission S.E S.hc S.cfg st B) := by
  simp only [Protocol.NamedAdmission.on_block_with]
  refine advance_admit_carried S admission st _ B
    (processBlockCore_advance S hsb hcf hcoh hmax hprov ?_ hRun hadv)
  intro hmem
  exact hBrun (by rw [on_block_with_bodies_eq]; exact hmem)

/-! ## 3. The remaining duties -/

theorem advance_goldfish_vote_with (S : Setup V) (gc : Protocol.GradeContract V)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (hadv : NamedFinalityAdvance S st) :
    NamedFinalityAdvance S
      (Protocol.NamedDuties.goldfish_vote_with gc S.E S.hc nd st).1 := by
  refine advance_of_bodies_eq_of_F S (st := st) rfl ?_ hadv
  rw [NamedDuties.goldfish_vote_core]
  simp only [Protocol.goldfish_vote_with]
  split_ifs <;>
    simp only [on_goldfish_vote_checked_F] <;> exact Block.preceq_self _

theorem advance_update_confirmation_with (S : Setup V) (gc : Protocol.GradeContract V)
    (st : Protocol.NamedStore V) (u : Slot)
    (hadv : NamedFinalityAdvance S st) :
    NamedFinalityAdvance S
      (Protocol.NamedDuties.update_confirmation_with gc S.E S.hc st u) := by
  refine advance_of_bodies_eq_of_F S (st := st) rfl ?_ hadv
  show Block.Preceq st.core.F (Protocol.update_confirmation_with gc S.E S.hc st.core u).F
  have hF : (Protocol.update_confirmation_with gc S.E S.hc st.core u).F = st.core.F := rfl
  rw [hF]
  exact Block.preceq_self _

theorem advance_attest_with (S : Setup V) (gc : Protocol.GradeContract V)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (record : Protocol.NamedRecord)
    (hadv : NamedFinalityAdvance S st) :
    NamedFinalityAdvance S
      (Protocol.NamedDuties.attest_with gc S.E S.hc nd st record).1 :=
  advance_admit_row S st _ hadv

theorem advance_propose_block_with
    (S : Setup V) {rho : Run V}
    (hsb : SlashableBound S rho) (hcf : RootCollisionFree S rho)
    (gc : Protocol.GradeContract V) (nd : Protocol.Node V)
    {st : Protocol.NamedStore V}
    (hcoh : Proofs.NamedStore.Coherent S.E S.cfg st)
    (hmax : ∃ D ∈ st.bodies, (derive_named S.E S.cfg D).h = st.core.h_max)
    (hprov : Proofs.Bridges.NamedProvenance S st)
    (hRun : ∀ D ∈ st.bodies, RunBlock S rho D)
    (hBrun : ∀ D ∈ (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg nd st).1.bodies,
      RunBlock S rho D)
    (hadv : NamedFinalityAdvance S st) :
    NamedFinalityAdvance S
      (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg nd st).1 := by
  cases hp : Protocol.NamedActions.proposal_with gc .poolAndCarried S.E S.hc nd st with
  | none =>
      have hEq : (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg nd st).1 = st := by
        simp only [Protocol.NamedDuties.propose_block_with, hp]
      rw [hEq]
      exact hadv
  | some B =>
      have hEq : (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg nd st).1 =
          Protocol.NamedAdmission.on_block_with .alsoCarried S.E S.hc S.cfg st B := by
        simp only [Protocol.NamedDuties.propose_block_with, hp]
      rw [hEq] at hBrun ⊢
      exact advance_on_block_with S hsb hcf .alsoCarried hcoh hmax hprov
        (fun hmem => hBrun B hmem) hRun hadv


/-! ## 4. The tick, stage by stage

The three stage definitions and `tick_eq_stage3` are the `let` chain of
`NamedFinalityMonotone.tick_F`, named so that the bodies equation and the
advance can both be read off the same computation. -/

def tickStage1 (S : Setup V) (gc : Protocol.GradeContract V) (nd : Protocol.Node V)
    (st : Protocol.NamedStore V) (t : Time) : Protocol.NamedStore V :=
  if 0 < S.E.slotOf t ∧ t = Protocol.proposal_time S.E (S.E.slotOf t) ∧
      S.E.proposer (S.E.slotOf t) = nd.val_index then
    (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg nd
      (Protocol.NamedStore.setClock S.E st t)).1
  else Protocol.NamedStore.setClock S.E st t

def tickStage2 (S : Setup V) (gc : Protocol.GradeContract V) (nd : Protocol.Node V)
    (st : Protocol.NamedStore V) (t : Time) : Protocol.NamedStore V :=
  if 0 < S.E.slotOf t ∧ t = Protocol.vote_time S.E (S.E.slotOf t) then
    (Protocol.NamedDuties.goldfish_vote_with gc S.E S.hc nd
      (tickStage1 S gc nd st t)).1
  else tickStage1 S gc nd st t

def tickStage3 (S : Setup V) (gc : Protocol.GradeContract V) (nd : Protocol.Node V)
    (st : Protocol.NamedStore V) (t : Time) : Protocol.NamedStore V :=
  if 0 < S.E.slotOf t ∧ t = Protocol.support_cutoff S.E (S.E.slotOf t) then
    Protocol.NamedDuties.update_confirmation_with gc S.E S.hc
      (tickStage2 S gc nd st t) (S.E.slotOf t - 1)
  else tickStage2 S gc nd st t

theorem tick_eq_stage3 (S : Setup V) (gc : Protocol.GradeContract V)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (record : Protocol.NamedRecord) (t : Time) :
    (Protocol.NamedTick.tick gc S.E S.hc S.cfg nd st record t).1 =
      (if t = S.hc.a S.E.Δ (S.hc.round_of (tickStage3 S gc nd st t).core.s) ∧
          nd.awake (S.hc.round_of (tickStage3 S gc nd st t).core.s) = true then
        (Protocol.NamedDuties.attest_with gc S.E S.hc nd
          (tickStage3 S gc nd st t) record).1
      else tickStage3 S gc nd st t) := by
  rw [NamedTick.tick_computed_duties]
  dsimp only [tickStage3, tickStage2, tickStage1]
  split_ifs <;> rfl

theorem tick_bodies_stage1 (S : Setup V) (gc : Protocol.GradeContract V)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (record : Protocol.NamedRecord) (t : Time) :
    (Protocol.NamedTick.tick gc S.E S.hc S.cfg nd st record t).1.bodies =
      (tickStage1 S gc nd st t).bodies := by
  have hb2 : (tickStage2 S gc nd st t).bodies = (tickStage1 S gc nd st t).bodies := by
    dsimp only [tickStage2]; split_ifs <;> rfl
  have hb3 : (tickStage3 S gc nd st t).bodies = (tickStage1 S gc nd st t).bodies := by
    dsimp only [tickStage3]; split_ifs <;> exact hb2
  rw [tick_eq_stage3]
  split_ifs
  · show (Protocol.NamedAdmission.admit_row S.hc (tickStage3 S gc nd st t) _).bodies = _
    rw [NamedAdmission.admit_row_bodies]
    exact hb3
  · exact hb3

theorem advance_tick_of_stage1 (S : Setup V) (gc : Protocol.GradeContract V)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (record : Protocol.NamedRecord) (t : Time)
    (hadv1 : NamedFinalityAdvance S (tickStage1 S gc nd st t)) :
    NamedFinalityAdvance S
      (Protocol.NamedTick.tick gc S.E S.hc S.cfg nd st record t).1 := by
  have hadv2 : NamedFinalityAdvance S (tickStage2 S gc nd st t) := by
    dsimp only [tickStage2]
    split_ifs
    · exact advance_goldfish_vote_with S gc nd _ hadv1
    · exact hadv1
  have hadv3 : NamedFinalityAdvance S (tickStage3 S gc nd st t) := by
    dsimp only [tickStage3]
    split_ifs
    · exact advance_update_confirmation_with S gc _ _ hadv2
    · exact hadv2
  rw [tick_eq_stage3]
  split_ifs
  · exact advance_attest_with S gc nd _ record hadv3
  · exact hadv3

theorem advance_stage1
    (S : Setup V) {rho : Run V}
    (hsb : SlashableBound S rho) (hcf : RootCollisionFree S rho)
    (gc : Protocol.GradeContract V) (nd : Protocol.Node V)
    {st : Protocol.NamedStore V} {t : Time}
    (hcoh : Proofs.NamedStore.Coherent S.E S.cfg (Protocol.NamedStore.setClock S.E st t))
    (hmax : ∃ D ∈ (Protocol.NamedStore.setClock S.E st t).bodies,
      (derive_named S.E S.cfg D).h =
        (Protocol.NamedStore.setClock S.E st t).core.h_max)
    (hprov : Proofs.Bridges.NamedProvenance S (Protocol.NamedStore.setClock S.E st t))
    (hRun : ∀ D ∈ (Protocol.NamedStore.setClock S.E st t).bodies, RunBlock S rho D)
    (hBrun : ∀ D ∈ (tickStage1 S gc nd st t).bodies, RunBlock S rho D)
    (hadv : NamedFinalityAdvance S st) :
    NamedFinalityAdvance S (tickStage1 S gc nd st t) := by
  have hadv0 : NamedFinalityAdvance S (Protocol.NamedStore.setClock S.E st t) :=
    advance_setClock S st t hadv
  simp only [tickStage1] at hBrun ⊢
  split_ifs at hBrun ⊢ with hprop
  · exact advance_propose_block_with S hsb hcf gc nd hcoh hmax hprov hRun hBrun hadv0
  · exact hadv0

/-! ## 5. The receipt and the node transitions -/

theorem advance_receipt
    (S : Setup V) {rho : Run V}
    (hsb : SlashableBound S rho) (hcf : RootCollisionFree S rho)
    (st : Protocol.NamedStore V) (o : NamedObject V)
    (hcoh : Proofs.NamedStore.Coherent S.E S.cfg st)
    (hmax : ∃ D ∈ st.bodies, (derive_named S.E S.cfg D).h = st.core.h_max)
    (hprov : Proofs.Bridges.NamedProvenance S st)
    (hRun : ∀ D ∈ st.bodies, RunBlock S rho D)
    (hBrun : ∀ D ∈ (NamedReceipt.process S st o).bodies, RunBlock S rho D)
    (hadv : NamedFinalityAdvance S st) :
    NamedFinalityAdvance S (NamedReceipt.process S st o) := by
  cases o with
  | block B =>
      exact advance_on_block_with S hsb hcf .alsoCarried hcoh hmax hprov
        (fun hmem => hBrun B hmem) hRun hadv
  | gfVote u =>
      refine advance_of_bodies_eq_of_F S (st := st) rfl ?_ hadv
      show Block.Preceq st.core.F (Protocol.on_goldfish_vote_checked S.E st.core u).F
      rw [on_goldfish_vote_checked_F]
      exact Block.preceq_self _
  | attest row => exact advance_admit_row S st row hadv

theorem advance_node_process
    (S : Setup V) {rho : Run V}
    (hsb : SlashableBound S rho) (hcf : RootCollisionFree S rho)
    (n : NamedNodeState V) (o : NamedObject V)
    (hcoh : Proofs.NamedStore.Coherent S.E S.cfg n.st)
    (hmax : ∃ D ∈ n.st.bodies, (derive_named S.E S.cfg D).h = n.st.core.h_max)
    (hprov : Proofs.Bridges.NamedProvenance S n.st)
    (hRun : ∀ D ∈ n.st.bodies, RunBlock S rho D)
    (hBrun : ∀ D ∈ (NamedNode.process S n o).st.bodies, RunBlock S rho D)
    (hadv : NamedFinalityAdvance S n.st) :
    NamedFinalityAdvance S (NamedNode.process S n o).st :=
  advance_receipt S hsb hcf n.st o hcoh hmax hprov hRun hBrun hadv

theorem advance_node_tick
    (S : Setup V) {rho : Run V}
    (hsb : SlashableBound S rho) (hcf : RootCollisionFree S rho)
    (v : V) (n : NamedNodeState V) (t : Time)
    (hcoh : Proofs.NamedStore.Coherent S.E S.cfg
      (Protocol.NamedStore.setClock S.E n.st t))
    (hmax : ∃ D ∈ (Protocol.NamedStore.setClock S.E n.st t).bodies,
      (derive_named S.E S.cfg D).h =
        (Protocol.NamedStore.setClock S.E n.st t).core.h_max)
    (hprov : Proofs.Bridges.NamedProvenance S (Protocol.NamedStore.setClock S.E n.st t))
    (hRun : ∀ D ∈ (Protocol.NamedStore.setClock S.E n.st t).bodies, RunBlock S rho D)
    (hBrun : ∀ D ∈ (NamedNode.tick S v n t).1.st.bodies, RunBlock S rho D)
    (hadv : NamedFinalityAdvance S n.st) :
    NamedFinalityAdvance S (NamedNode.tick S v n t).1.st := by
  set gc := NamedProfile.gradeContract
    (DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache) with hgc
  have hsame : (NamedNode.tick S v n t).1.st =
      (Protocol.NamedTick.tick gc S.E S.hc S.cfg (S.node v) n.st n.record t).1 := rfl
  rw [hsame] at hBrun ⊢
  refine advance_tick_of_stage1 S gc (S.node v) n.st n.record t ?_
  refine advance_stage1 S hsb hcf gc (S.node v) hcoh hmax hprov hRun ?_ hadv
  intro D hD
  refine hBrun D ?_
  rw [tick_bodies_stage1]
  exact hD

/-! ## 6. The run -/

theorem advance_stateBefore
    (S : Setup V) {rho : Run V}
    (sch : ScheduleWellFormed S rho)
    (hsb : SlashableBound S rho) (hcf : RootCollisionFree S rho)
    {v : V} (hv : v ∈ rho.honest) :
    ∀ i : Nat, NamedFinalityAdvance S (NamedRun.stateBefore S rho i v).st := by
  intro i
  induction i with
  | zero =>
      intro D hD
      have hDg : D = NamedBlock.genesis := by
        simpa only [Proofs.NamedRuntime.stateBefore_zero, NamedWorld.init,
          NamedNode.initial, Protocol.NamedStore.initial, Finset.mem_singleton]
          using hD
      subst hDg
      exact Block.preceq_self _
  | succ i ih =>
      rcases hev : rho.events[i]? with _ | e
      · have hsame : NamedRun.stateBefore S rho (i + 1) v = NamedRun.stateBefore S rho i v := by
          rw [Proofs.NamedRuntime.stateBefore_succ, hev]
          rfl
        rw [hsame]
        exact ih
      · by_cases hvn : v = e.node
        · have hcohBase : Proofs.NamedStore.Coherent S.E S.cfg (NamedRun.stateBefore S rho i v).st :=
            (Proofs.NamedRuntime.stateBefore_invariants S rho i v).1.1.1
          have hmaxBase := Proofs.NamedStoreBridge.maximum_carrier_stateBefore S rho i v
          have hprovBase := Proofs.Bridges.namedProvenance_stateBefore S rho i v
          have hRunBase : ∀ D ∈ (NamedRun.stateBefore S rho i v).st.bodies, RunBlock S rho D :=
            fun D hD => Proofs.Bridges.runBlock_of_stateBefore_mem S hv hD
          cases e with
          | tick u tt =>
              have hvu : v = u := hvn
              subst hvu
              have hstep := Proofs.NamedRuntime.stateBefore_tick S rho hev
              rw [hstep]
              refine advance_node_tick S hsb hcf v (NamedRun.stateBefore S rho i v) tt
                (NamedStore.coherent_clock S.E S.cfg _ tt hcohBase)
                hmaxBase hprovBase hRunBase ?_ ih
              intro D hD
              refine Proofs.Bridges.runBlock_of_stateBefore_mem S hv (i := i + 1) ?_
              show D ∈ (NamedRun.stateBefore S rho (i + 1) v).st.bodies
              rw [hstep]
              exact hD
          | deliver u o tt =>
              have hvu : v = u := hvn
              subst hvu
              have hstep := Proofs.NamedRuntime.stateBefore_deliver S rho hev
              rw [hstep]
              refine advance_node_process S hsb hcf (NamedRun.stateBefore S rho i v) o
                hcohBase hmaxBase hprovBase hRunBase ?_ ih
              intro D hD
              refine Proofs.Bridges.runBlock_of_stateBefore_mem S hv (i := i + 1) ?_
              show D ∈ (NamedRun.stateBefore S rho (i + 1) v).st.bodies
              rw [hstep]
              exact hD
        · rw [Proofs.NamedRuntime.stateBefore_other S rho hev v hvn]
          exact ih

/-- `W4ProcessedFinalityAdvancePin`, proved. -/
theorem w4ProcessedFinalityAdvancePin_of_slashableBound
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hsb : SlashableBound S rho) :
    W4ProcessedFinalityAdvancePin S rho := by
  intro v hv t B hB
  obtain ⟨n, hn, -⟩ := Proofs.NamedRuntime.readAt_eq_prefix S rho
    adm.toNamedScheduleWellFormed.sorted t
  have hstore : rho.storeAt S v t = (NamedRun.stateBefore S rho n v).st := by
    show (NamedRun.readAt S rho t v).st = _
    rw [hn]
  rw [hstore] at hB ⊢
  exact advance_stateBefore S adm.toNamedScheduleWellFormed hsb
    adm.toNamedAdmissibleCore.toNamedRootCollisionFree hv n B hB

#print axioms advance_on_block_with
#print axioms advance_tick_of_stage1
#print axioms advance_stage1
#print axioms advance_node_tick
#print axioms advance_stateBefore
#print axioms w4ProcessedFinalityAdvancePin_of_slashableBound

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
