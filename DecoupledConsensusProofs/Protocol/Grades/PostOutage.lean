module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.Persistence
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.ActionHistory
public import DecoupledConsensusProofs.Generic.EvaluationStore
public import DecoupledConsensusProofs.Protocol.Grades.GradeFormsProducers
public import DecoupledConsensusProofs.Protocol.Grades.FrameCompleted
public import DecoupledConsensusProofs.Protocol.Grades.FrameForward
public import DecoupledConsensusProofs.Protocol.Grades.Interpolation
public import DecoupledConsensusProofs.Protocol.Grades.Q10Frame
public import DecoupledConsensusProofs.Protocol.ChainState.ProposalBridge
public import DecoupledConsensusProofs.Protocol.Grades.GradeFormsBridge
public import DecoupledConsensusProofs.Protocol.Grades.RelativeSupporter
public import DecoupledConsensusProofs.Protocol.ValidatorClient.Schedule
public import DecoupledConsensusProofs.Protocol.Handlers.FrameFloorBridge
public import DecoupledConsensusProofs.Protocol.Schedule.RecordAtBoundary
public import DecoupledConsensusInternal.Legacy.Definitions.NamedHeadReads
public import DecoupledConsensusInternal.Definitions.NamedLifecycle

@[expose] public section

/-!
# Post-outage persistence

This module records the post-outage certificate at its producer reads. The raw
G2 and G1 freezes are read at their domain times. Stable output is read at every
time in the round interval. Prepared anchor floors are derived separately from
the raw roots.
-/
namespace DecoupledConsensusModel.Proofs.NamedOutageClosure

open Internal Execution Internal.PhaseGrades Internal.NamedRecoveryRead
open Internal.NamedStableChainOutage
open DecoupledConsensusModel.Protocol
open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

def postOutageReadAt (S : Setup V) (rho : NamedRun V) (w : V) (r : Round) :
    NamedNodeState V :=
  Proofs.HealingSurface.relativeG2Read S rho r w


def postOutageVoteDutyReadAt (S : Setup V) (rho : NamedRun V) (v : V) (s : Slot) :
    NamedNodeState V :=
  voteDutyRead S rho v s

def postOutageFrozenG2At (S : Setup V) (rho : NamedRun V) (w : V) (r : Round) :
    Option (Block V) :=
  DecoupledConsensusModel.Protocol.freezeRoot S.E
    (postOutageReadAt S rho w r).st.core.toHealing.gradeView
    (postOutageReadAt S rho w r).st.core.F S.hc.η_SG r
    (early S.E S.hc r .g2) (late S.E S.hc r .g2)

def postOutageFrozenG1At (S : Setup V) (rho : NamedRun V) (w : V) (r : Round) :
    Option (Block V) :=
  DecoupledConsensusModel.Protocol.freezeRoot S.E
    (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1) w).st.core.toHealing.gradeView
    (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1) w).st.core.F S.hc.η_SG r
    (early S.E S.hc r .g1) (late S.E S.hc r .g1)



/-- The post-outage certificate is stated at the reads that produce it.

The two root clauses use the raw domain freezes. Each clause records that the
raw root or the finalized root at the same domain read covers `P`. The stable
clause is horizon-local between consecutive G2 domains. Anchor floors at
prepared reads are derived from these clauses and are not stored here. -/
def PostOutageAbove (S : Setup V) (rho : NamedRun V) (P : Block V) (r : Round) : Prop :=
  (∀ w ∈ rho.honest,
      Block.Preceq P (postOutageReadAt S rho w r).st.core.F ∨
        ∃ R, postOutageFrozenG2At S rho w r = some R ∧ Block.Preceq P R) ∧
  (∀ w ∈ rho.honest, Block.Preceq P
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1) w).st.core.F ∨
        ∃ R, postOutageFrozenG1At S rho w r = some R ∧ Block.Preceq P R) ∧
  (∀ w ∈ rho.honest, ∀ t,
      domain S.E S.hc r .g2 ≤ t → t ≤ domain S.E S.hc (r + 1) .g2 →
      Block.Preceq P
        (Protocol.get_stable (NamedRun.stateBeforeTime S rho t w).st.core))

/-- Every honest carrier emitted in round `r` is above the protected prefix.
This is the vote-facing input of the post-outage successor. -/
def HonestCarriersAbove (S : Setup V) (rho : NamedRun V) (P : Block V)
    (r : Round) : Prop :=
  ∀ u ∈ Internal.NamedOutageEntry.honestRoundVoters S rho r,
    Block.Preceq P (Proofs.HealingSurface.actionSGBlockAt S rho u r)

/- A support cutoff inside two consecutive G2 domains belongs to the round
between those domains. -/
theorem support_cutoff_round_of_domain_window
    (S : Setup V) (r : Round) (u : Time)
    (hlo : domain S.E S.hc r .g2 ≤ u)
    (hhi : u < domain S.E S.hc (r + 1) .g2)
    (hcut : u = Protocol.support_cutoff S.E (S.E.slotOf u)) :
    S.hc.round_of (S.E.slotOf u) = r := by
  have htimeLo := hlo
  have htimeHi := hhi
  rw [hcut] at htimeLo htimeHi
  simp only [domain, Phase.domainOffset, opening, Protocol.proposal_time,
    Protocol.support_cutoff, Env.t, slotStart,
    Protocol.HealConfig.opening_slot] at htimeLo htimeHi
  have hcoef : (0 : Int) ≤ 4 * S.E.Δ :=
    Int.mul_nonneg (by norm_num) S.E.Δ_pos.le
  have hslotLo : S.hc.opening_slot r ≤ S.E.slotOf u := by
    by_contra hnot
    have hsucc : S.E.slotOf u + 1 ≤ S.hc.opening_slot r :=
      Nat.succ_le_of_lt (Nat.lt_of_not_ge hnot)
    have hcast : (((S.E.slotOf u + 1 : Nat) : Int)) ≤
        ((S.hc.opening_slot r : Nat) : Int) := by
      exact_mod_cast hsucc
    have hmul := Int.mul_le_mul_of_nonneg_left hcast hcoef
    simp only [Protocol.HealConfig.opening_slot] at hmul
    norm_num [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at htimeLo hmul
    nlinarith [S.E.Δ_pos]
  have hslotHi : S.E.slotOf u < S.hc.opening_slot (r + 1) := by
    by_contra hnot
    have hle : S.hc.opening_slot (r + 1) ≤ S.E.slotOf u :=
      Nat.le_of_not_gt hnot
    have hcast : ((S.hc.opening_slot (r + 1) : Nat) : Int) ≤
        ((S.E.slotOf u : Nat) : Int) := by
      exact_mod_cast hle
    have hmul := Int.mul_le_mul_of_nonneg_left hcast hcoef
    simp only [Protocol.HealConfig.opening_slot] at hmul
    norm_num [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at htimeHi hmul
    nlinarith [S.E.Δ_pos]
  simp only [Protocol.HealConfig.round_of]
  apply Nat.eq_of_le_of_lt_succ
  · exact (Nat.le_div_iff_mul_le
      (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)).mpr
      (by simpa only [Protocol.HealConfig.opening_slot] using hslotLo)
  · exact (Nat.div_lt_iff_lt_mul
      (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)).mpr
      (by simpa only [Protocol.HealConfig.opening_slot] using hslotHi)

/- A support cutoff at or after a G2 domain is strictly after that domain. -/
theorem domain_g2_lt_support_cutoff_of_le
    (S : Setup V) (r : Round) (u : Time)
    (hlo : domain S.E S.hc r .g2 ≤ u)
    (hcut : u = Protocol.support_cutoff S.E (S.E.slotOf u)) :
    domain S.E S.hc r .g2 < u := by
  have htime := hlo
  rw [hcut] at htime
  rw [hcut]
  simp only [domain, Phase.domainOffset, opening, Protocol.proposal_time,
    Protocol.support_cutoff, Env.t, slotStart,
    Protocol.HealConfig.opening_slot] at htime ⊢
  have hcoef : (0 : Int) ≤ 4 * S.E.Δ :=
    Int.mul_nonneg (by norm_num) S.E.Δ_pos.le
  have hslotLo : r * S.hc.R ≤ S.E.slotOf u := by
    by_contra hnot
    have hsucc : S.E.slotOf u + 1 ≤ r * S.hc.R :=
      Nat.succ_le_of_lt (Nat.lt_of_not_ge hnot)
    have hcast : (((S.E.slotOf u + 1 : Nat) : Int)) ≤
        (((r * S.hc.R : Nat) : Int)) := by
      exact_mod_cast hsucc
    have hmul := Int.mul_le_mul_of_nonneg_left hcast hcoef
    norm_num [Nat.cast_mul, Nat.cast_add, Nat.cast_one] at htime hmul
    nlinarith [S.E.Δ_pos]
  have hcast : (((r * S.hc.R : Nat) : Int)) ≤
      ((S.E.slotOf u : Nat) : Int) := by
    exact_mod_cast hslotLo
  have hmul := Int.mul_le_mul_of_nonneg_left hcast hcoef
  norm_num [Nat.cast_mul] at hmul ⊢
  nlinarith [S.E.Δ_pos]

/- The viability witness for a descendant also witnesses every processed
ancestor. This is the monotonicity used by the filtered-tree consumer. -/

/- The filtered-tree consumer only needs one viable descendant of P. Keeping
   that witness explicit separates the tree construction from its run-level
   producer. -/



/- This is the definition-level filtered-tree route. The remaining run-level
producer is the viability of the stored stable output at this read. -/

/-- The named vote-duty head is above the prepared contract anchor. -/
theorem voteDutyHead_preceq_voteDutyAnchor
    (S : Setup V) (rho : Run V) (v : V) (s : Slot) :
    Block.Preceq
      (DecoupledConsensusModel.Proofs.HealingSurface.voterAnchorAt S rho v s)
      (voterHeadAt S rho v s) := by
  let n := voteDutyRead S rho v s
  change Block.Preceq
    (Protocol.get_sg_root_with (NamedProfile.gradeContract n.cache) S.E S.hc
      n.st.core.toHealing (S.hc.round_of n.st.core.s))
    (Protocol.get_head_in_tree_with_layer (NamedProfile.gradeContract n.cache) S.E S.hc
      n.st.core.toHealing (Protocol.voter_filtered_block_tree S.E n.st.core n.st.core.s)
      (Protocol.voter_view S.E n.st.core.toHealing.toFG.toSG.toGoldfishStore n.st.core.s)
      (Protocol.voter_support_view S.E n.st.core.toHealing.toFG.toSG.toGoldfishStore n.st.core.s)
      (n.st.core.s - 1))
  exact Protocol.ghost_preceq _ _ _ _

/-- A protected block below the vote-duty anchor is below the named vote head. -/
theorem preceq_voteDutyHead_of_preceq_voteDutyAnchor
    (S : Setup V) (rho : Run V) (v : V) (s : Slot) {P : Block V}
    (hP : Block.Preceq P
      (DecoupledConsensusModel.Proofs.HealingSurface.voterAnchorAt S rho v s)) :
    Block.Preceq P (voterHeadAt S rho v s) :=
  Block.preceq_trans hP (voteDutyHead_preceq_voteDutyAnchor S rho v s)




omit [Fintype V] in
/-- A comparable candidate cannot remove a prefix that the previous record holds. -/
theorem advance_confirmed_retains_of_comparable
    {P old G : Block V} (hold : Block.Preceq P old)
    (hG : Block.Preceq P G ∨ Block.Preceq G P) :
    Block.Preceq P (Protocol.advance_confirmed old G) := by
  apply Proofs.ConfirmationPolicy.prefix_preceq_advance_of_compatible hold
  simpa only [Block.compatible, Bool.or_eq_true] using hG

/-- A comparable stable root preserves a covering old stable record. -/
theorem confirmation_write_stable_of_comparable
    (S : Setup V) (m : NamedNodeState V) (sl : Slot) {P : Block V}
    (hold : Block.Preceq P m.st.core.latest_stable)
    (hcomp : ∀ G, dutyStableRoot S m = some G →
      Block.Preceq P G ∨ Block.Preceq G P) :
    Block.Preceq P
      (Protocol.NamedDuties.update_confirmation_with
        (NamedProfile.gradeContract m.cache) S.E S.hc m.st sl).core.latest_stable := by
  show Block.Preceq P
    (match dutyStableRoot S m with
      | some G => Protocol.advance_confirmed m.st.core.latest_stable G
      | none => m.st.core.latest_stable)
  cases hq : dutyStableRoot S m with
  | none => exact hold
  | some G => exact advance_confirmed_retains_of_comparable hold (hcomp G hq)

/- The projection is the deepest member that precedes `raw`. Thus its output
and any other prefix of `raw` are comparable. The fallback uses the exact
FG-root compatibility residual. -/
theorem duty_root_comparable_of_frame
    (S : Setup V) (n : NamedNodeState V) {P raw G : Block V}
    (hframe : (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing
      (S.hc.round_of n.st.core.s)).g2 = some (some raw))
    (hPraw : Block.Preceq P raw)
    (hfg : Block.compatible P
      (Protocol.get_fg_root n.st.core.toHealing.toFG) = true)
    (hG : dutyStableRoot S n = some G) :
    Block.Preceq P G ∨ Block.Preceq G P := by
  rw [dutyStableRoot_of_frame S n hframe] at hG
  cases hactive : DecoupledConsensusModel.Protocol.activePrefix
      (Protocol.get_filtered_block_tree n.st.core.toHealing.toFG) raw with
  | none =>
      simp only [hactive] at hG
      have hEq := Option.some_inj.mp hG
      subst G
      simpa only [Block.compatible, Bool.or_eq_true] using hfg
  | some A =>
      simp only [hactive] at hG
      have hEq := Option.some_inj.mp hG
      subst G
      have hAraw : Block.Preceq A raw := by
        exact (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hactive)).2
      exact Block.preceq_linear hPraw hAraw

/-- A confirmation root is comparable with the protected prefix. The raw-root
arm uses the clipped freeze chain. The finalized arm already puts the root
above the prefix. -/
theorem confirmationDutyRoot_above_of_postOutageG2
    (S : Setup V) (rho : NamedRun V) (P : Block V) (r : Round)
    (core : NamedAdmissibleCore S rho) (w : V) (hw : w ∈ rho.honest)
    (hr : 0 < r) (u : Time)
    (hround : S.hc.round_of (S.E.slotOf u) = r)
    (ht : domain S.E S.hc r .g2 < u)
    (hta : u ≤ opening S.E S.hc (r + 1))
    (hhor : domain S.E S.hc r .g2 ≤ rho.horizon)
    (hroot : Block.Preceq P
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) w).st.core.F ∨
      ∃ R, postOutageFrozenG2At S rho w r = some R ∧ Block.Preceq P R)
    (hstable : Block.Preceq P
      (Protocol.get_stable (NamedRun.stateBeforeTime S rho u w).st.core))
    (hfg : Block.compatible P
      (Protocol.get_fg_root
        (NamedActionReads.confirmationReadAt S rho w u).st.core.toHealing.toFG) = true)
    {G : Block V}
    (hG : dutyStableRoot S (NamedActionReads.confirmationReadAt S rho w u) = some G) :
    Block.Preceq P G ∨ Block.Preceq G P := by
  let n := NamedActionReads.confirmationReadAt S rho w u
  rcases hroot with hPF | ⟨raw, hraw, hPraw⟩
  · have hPFnow : Block.Preceq P
        (NamedRun.stateBeforeTime S rho u w).st.core.F :=
      Block.preceq_trans hPF
        (incl_strict_F_mono S rho core.toNamedScheduleWellFormed w ht.le)
    have hFJ : Block.preceq n.st.core.F n.st.core.J = true := by
      change Block.preceq
        (NamedRun.stateBeforeTime S rho u w).st.core.F
        (NamedRun.stateBeforeTime S rho u w).st.core.J = true
      exact Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime S rho u w
    have hFroot : Block.Preceq n.st.core.F
        (Protocol.get_fg_root n.st.core.toHealing.toFG) :=
      Proofs.Records.preceq_get_fg_root_of_F (st := n.st.core.toHealing.toFG)
        (by simpa only [Protocol.Store.toHealing] using hFJ)
    have hPFn : Block.Preceq P n.st.core.F := by
      simpa only [n, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom] using hPFnow
    exact Or.inl (Block.preceq_trans hPFn
      (Block.preceq_trans hFroot (fgRoot_preceq_dutyStableRoot S n hG)))
  · have hFstable : Block.Preceq
        (NamedRun.stateBeforeTime S rho u w).st.core.F
        (Protocol.get_stable (NamedRun.stateBeforeTime S rho u w).st.core) := by
      unfold Protocol.get_stable
      split
      · assumption
      · exact Block.preceq_self _
    have hcompat : Block.compatible P
        (NamedRun.stateBeforeTime S rho u w).st.core.F = true :=
      Block.compatible_of_preceq_common hstable hFstable
    have hclip : Block.Preceq P
        (DecoupledConsensusModel.Protocol.clipGrade raw
          (NamedRun.stateBeforeTime S rho u w).st.core.F) :=
      (q10_retained_prefix raw
        (NamedRun.stateBeforeTime S rho u w).st.core.F P hcompat).mpr hPraw
    have hfreeze : DecoupledConsensusModel.Protocol.freezeRoot S.E
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc r .g2) w).st.core.toHealing.gradeView
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc r .g2) w).st.core.F S.hc.η_SG r
        (early S.E S.hc r .g2) (late S.E S.hc r .g2) = some raw := by
      simpa only [postOutageFrozenG2At, postOutageReadAt] using hraw
    have hbase := FrameCompleted.frame_g2_completed_in_round
      S rho core w hw r hr u ht hta hhor
    have hframe := frame_phase_prepared_eq S rho w r .g2 u hround _ hbase
    rw [hfreeze] at hframe
    have hnround : S.hc.round_of n.st.core.s = r := by
      simpa only [n, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom] using hround
    have hframe' : (DecoupledConsensusModel.Protocol.readFrame n.cache
        n.st.core.toHealing r).g2 =
        some (some (DecoupledConsensusModel.Protocol.clipGrade raw
          (NamedRun.stateBeforeTime S rho u w).st.core.F)) := by
      simpa only [n, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom] using hframe
    apply duty_root_comparable_of_frame S n
    · rw [hnround]
      exact hframe'
    · exact hclip
    · exact hfg
    · exact hG





theorem PostOutageAbove.anchor
    (S : Setup V) (rho : NamedRun V) (P : Block V) (r : Round)
    (h : PostOutageAbove S rho P r) (n : NamedNodeState V)
    (hPtree : P ∈ Protocol.get_filtered_block_tree n.st.core.toHealing.toFG)
    (hcase :
      (∃ root, (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing r).g1 =
        some (some root) ∧ Block.Preceq P root) ∨
      Block.Preceq P (Protocol.get_fg_root n.st.core.toHealing.toFG)) :
    Block.Preceq P (nodeAnchor S n r) :=
  Proofs.HealingSurface.anchor_preceq_of_frame_floor S n r P hPtree hcase

theorem PostOutageAbove.anchor_at_prepared_read
    (S : Setup V) (rho : NamedRun V) (P : Block V) (r : Round)
    (h : PostOutageAbove S rho P r) (core : NamedAdmissibleCore S rho)
    (w : V) (hw : w ∈ rho.honest) (t : Time) (hr : 0 < r)
    (hround : S.hc.round_of (S.E.slotOf t) = r)
    (ht : domain S.E S.hc r .g1 < t) (hta : t ≤ S.a r)
    (hhor : domain S.E S.hc r .g1 ≤ rho.horizon)
    (hPtree : P ∈ Protocol.get_filtered_block_tree
      (NamedActionReads.confirmationReadAt S rho w t).st.core.toHealing.toFG) :
    Block.Preceq P (nodeAnchor S (NamedActionReads.confirmationReadAt S rho w t) r) := by
  let n := NamedActionReads.confirmationReadAt S rho w t
  rcases h.2.1 w hw with hPF | ⟨raw, hfreeze, hPraw⟩
  · have hPF' : Block.Preceq P n.st.core.F := by
      exact Block.preceq_trans hPF
        (incl_strict_F_mono S rho core.toNamedScheduleWellFormed w ht.le)
    have hFJ : Block.Preceq n.st.core.F n.st.core.J := by
      simpa only [n, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom,
        NamedActionReads.preparedCache, Protocol.NamedStore.setClock] using
        Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime S rho t w
    have hfg : Block.Preceq P
        (Protocol.get_fg_root n.st.core.toHealing.toFG) := by
      exact Block.preceq_trans hPF'
        (Proofs.Records.preceq_get_fg_root_of_F
          (st := n.st.core.toHealing.toFG) (by exact hFJ))
    exact Proofs.HealingSurface.anchor_preceq_of_frame_floor S n r P hPtree (Or.inr hfg)
  · have hfreeze' : DecoupledConsensusModel.Protocol.freezeRoot S.E
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc r .g1) w).st.core.toHealing.gradeView
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc r .g1) w).st.core.F S.hc.η_SG r
        (early S.E S.hc r .g1) (late S.E S.hc r .g1) = some raw := by
      simpa only [postOutageFrozenG1At] using hfreeze
    obtain ⟨root, hroot, hProot⟩ :=
      Proofs.HealingSurface.frameG1_preceq_of_freezeRoot_prepared
        S rho core w hw r hr t hround ht hta hhor hPtree hfreeze' hPraw
    exact Proofs.HealingSurface.anchor_preceq_of_frame_floor S n r P hPtree
      (Or.inl ⟨root, by simpa only [n] using hroot, hProot⟩)

/-- The action read has the same frame, candidate tree, and finalized root as
its prepared confirmation read. The confirmation write changes only records. -/
theorem PostOutageAbove.anchor_at_action_read
    (S : Setup V) (rho : NamedRun V) (P : Block V) (r : Round)
    (h : PostOutageAbove S rho P r) (core : NamedAdmissibleCore S rho)
    (w : V) (hw : w ∈ rho.honest) (hr : 0 < r) (hhor : S.a r ≤ rho.horizon)
    (hPtree : P ∈ Protocol.get_filtered_block_tree
      (NamedActionReads.actionReadAt S rho w r).st.core.toHealing.toFG) :
    Block.Preceq P (nodeAnchor S (NamedActionReads.actionReadAt S rho w r) r) := by
  have hPtree' : P ∈ Protocol.get_filtered_block_tree
      (NamedActionReads.confirmationReadAt S rho w (S.a r)).st.core.toHealing.toFG := by
    simpa only [NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadAt,
      Protocol.NamedDuties.update_confirmation_with] using hPtree
  have hanchor := h.anchor_at_prepared_read S rho P r core w hw (S.a r) hr
    (Proofs.HealingLemmas.round_of_slotOf_a S r) (q10_domain_lt_a S r .g1) le_rfl
    ((q10_domain_lt_a S r .g1).le.trans hhor) hPtree'
  simpa only [NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
    NamedActionReads.confirmationReadAt, nodeAnchor, nodeRead,
    Protocol.NamedDuties.update_confirmation_with] using hanchor

/-- The action SG carrier is above `P`. The finalized arm uses the FG-root
floor. The raw-root arm projects the saved G2 root into the action tree. -/
theorem PostOutageAbove.actionSGBlock_floor
    (S : Setup V) (rho : NamedRun V) (P : Block V) (r : Round)
    (h : PostOutageAbove S rho P r) (core : NamedAdmissibleCore S rho)
    (w : V) (hw : w ∈ rho.honest) (hr : 0 < r) (hhor : S.a r ≤ rho.horizon)
    (hPtree : P ∈ Protocol.get_filtered_block_tree
      (NamedActionReads.actionReadAt S rho w r).st.core.toHealing.toFG) :
    Block.Preceq P (Proofs.HealingSurface.actionSGBlockAt S rho w r) := by
  let action := NamedActionReads.actionReadAt S rho w r
  have hPprepared : P ∈ Protocol.get_filtered_block_tree
      (NamedActionReads.confirmationReadAt S rho w (S.a r)).st.core.toHealing.toFG := by
    simpa only [action, NamedActionReads.actionReadAt,
      NamedActionReads.actionReadFrom, NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, Protocol.NamedStore.setClock,
      Protocol.NamedDuties.update_confirmation_with] using hPtree
  rcases h.1 w hw with hPF | ⟨raw, hfreeze, hPraw⟩
  · have hPFaction : Block.Preceq P action.st.core.F := by
      exact Block.preceq_trans hPF
        (incl_strict_F_mono S rho core.toNamedScheduleWellFormed w
          (q10_domain_lt_a S r .g2).le)
    have hFJaction : Block.preceq action.st.core.F action.st.core.J = true := by
      simpa only [action, NamedActionReads.actionReadAt,
        NamedActionReads.actionReadFrom, NamedActionReads.confirmationReadFrom,
        NamedActionReads.preparedCache, Protocol.NamedStore.setClock,
        Protocol.NamedDuties.update_confirmation_with] using
        Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime S rho (S.a r) w
    exact Block.preceq_trans hPFaction
      (Block.preceq_trans
        (Proofs.Records.preceq_get_fg_root_of_F (st := action.st.core.toHealing.toFG)
          (by simpa only [Protocol.Store.toHealing] using hFJaction))
        (by simpa only [Proofs.HealingSurface.actionStoreAt, action] using
          Proofs.HealingSurface.actionFGRoot_preceq_actionSGBlockAt S rho w r))
  · have hfreeze' : DecoupledConsensusModel.Protocol.freezeRoot S.E
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc r .g2) w).st.core.toHealing.gradeView
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc r .g2) w).st.core.F S.hc.η_SG r
        (early S.E S.hc r .g2) (late S.E S.hc r .g2) = some raw := by
      simpa only [postOutageFrozenG2At, postOutageReadAt] using hfreeze
    obtain ⟨root, hframe, hProot⟩ :=
      Proofs.HealingSurface.frameG2_preceq_of_freezeRoot_prepared
        S rho core w hw r hr (S.a r) (Proofs.HealingLemmas.round_of_slotOf_a S r)
        (q10_domain_lt_a S r .g2) le_rfl
        ((q10_domain_lt_a S r .g2).le.trans hhor) hPprepared hfreeze' hPraw
    have hframeAction : (DecoupledConsensusModel.Protocol.readFrame action.cache
        action.st.core.toHealing r).g2 = some (some root) := by
      simpa only [action, NamedActionReads.actionReadAt,
        NamedActionReads.actionReadFrom, NamedActionReads.confirmationReadFrom,
        NamedActionReads.preparedCache, Protocol.NamedStore.setClock,
        Protocol.NamedDuties.update_confirmation_with] using hframe
    obtain ⟨A, hA, hPA⟩ := activePrefix_covers hPtree hProot
    have hQ : Internal.PhaseGrades.nodeQ2 S action r = some A := by
      simp only [Internal.PhaseGrades.nodeQ2, Internal.PhaseGrades.nodeRead,
        NamedProfile.gradeContract, DecoupledConsensusModel.Protocol.frameContract,
        Protocol.grade2_block_with, DecoupledConsensusModel.Protocol.frameGradeRead,
        DecoupledConsensusModel.Protocol.grade2Block, hframeAction, Option.bind_some, id_eq]
      have hclosed : DecoupledConsensusModel.Protocol.allClosed
          (DecoupledConsensusModel.Protocol.readFrame action.cache action.st.core.toHealing r) = true := by
        simpa only [action] using
          Proofs.HealingSurface.actionFrame_allClosed S core hw hr hhor
      rw [if_pos hclosed]
      simpa only [action] using hA
    exact Proofs.HealingSurface.preceq_actionSGBlockAt_of_actionQ2 S core hw hr hhor
      (by simpa only [action] using hQ) hPA

/-- Every honest attestation emitted in the certified round confirms the
action SG carrier, which is above `P`. -/
theorem PostOutageAbove.emitted_vote_floor
    (S : Setup V) (rho : NamedRun V) (P : Block V) (r : Round)
    (h : PostOutageAbove S rho P r) (core : NamedAdmissibleCore S rho)
    (w : V) (hw : w ∈ rho.honest) (hr : 0 < r) (hhor : S.a r ≤ rho.horizon)
    {a : NamedAttestation V} (haround : a.round = r)
    (hemit : NamedRun.emits S rho w (.attest a) (S.a r))
    (hPtree : P ∈ Protocol.get_filtered_block_tree
      (NamedActionReads.actionReadAt S rho w r).st.core.toHealing.toFG) :
    a.confirmed = some (Proofs.HealingSurface.actionSGBlockAt S rho w r).root ∧
      Block.Preceq P (Proofs.HealingSurface.actionSGBlockAt S rho w r) := by
  have hawake : (S.node w).awake r = true := by
    simpa only [haround] using Proofs.Optimistic.emits_attest_awake S hemit
  have hcanonical := Proofs.HealingSurface.honest_emits_exact_actionAttestationAt_of_awake
    S core.toNamedScheduleWellFormed hw r hawake hhor
  have ha : a = Proofs.HealingSurface.actionAttestationAt S rho w r := by
    apply Proofs.Optimistic.emits_attest_unique S core.toNamedScheduleWellFormed hemit hcanonical
    simpa only [haround] using
      (Proofs.HealingSurface.actionAttestationAt_shape S rho w r).2.1.symm
  constructor
  · rw [ha]
    exact (Proofs.HealingSurface.actionAttestationAt_shape S rho w r).2.2
  · exact h.actionSGBlock_floor S rho P r core w hw hr hhor hPtree

/-- The K6-facing form: finality has already passed `P`, or `P` is active in
the prepared action tree. -/
theorem PostOutageAbove.emitted_vote_floor_of_finalized_or_active
    (S : Setup V) (rho : NamedRun V) (P : Block V) (r : Round)
    (h : PostOutageAbove S rho P r) (core : NamedAdmissibleCore S rho)
    (w : V) (hw : w ∈ rho.honest) (hr : 0 < r) (hhor : S.a r ≤ rho.horizon)
    {a : NamedAttestation V} (haround : a.round = r)
    (hemit : NamedRun.emits S rho w (.attest a) (S.a r))
    (hcase : Block.Preceq P (NamedActionReads.actionReadAt S rho w r).st.core.F ∨
      P ∈ Protocol.get_filtered_block_tree
        (NamedActionReads.actionReadAt S rho w r).st.core.toHealing.toFG) :
    a.confirmed = some (Proofs.HealingSurface.actionSGBlockAt S rho w r).root ∧
      Block.Preceq P (Proofs.HealingSurface.actionSGBlockAt S rho w r) := by
  rcases hcase with hPF | hPtree
  · have htarget := Block.preceq_trans hPF
      (Block.preceq_trans
        (Proofs.Records.preceq_get_fg_root_of_F
          (st := (NamedActionReads.actionReadAt S rho w r).st.core.toHealing.toFG)
          (by
            exact Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
              S rho (S.a r) w))
        (by simpa only [Proofs.HealingSurface.actionStoreAt] using
          Proofs.HealingSurface.actionFGRoot_preceq_actionSGBlockAt S rho w r))
    have hawake : (S.node w).awake r = true := by
      simpa only [haround] using Proofs.Optimistic.emits_attest_awake S hemit
    have hcanonical := Proofs.HealingSurface.honest_emits_exact_actionAttestationAt_of_awake
      S core.toNamedScheduleWellFormed hw r hawake hhor
    have ha := Proofs.Optimistic.emits_attest_unique S core.toNamedScheduleWellFormed
      hemit hcanonical (by simpa only [haround] using
        (Proofs.HealingSurface.actionAttestationAt_shape S rho w r).2.1.symm)
    refine ⟨?_, htarget⟩
    rw [ha]
    exact (Proofs.HealingSurface.actionAttestationAt_shape S rho w r).2.2
  · exact h.emitted_vote_floor S rho P r core w hw hr hhor haround hemit hPtree

theorem PostOutageAbove.frameG2_floor_at_read
    (S : Setup V) (rho : NamedRun V) (P : Block V) (r : Round)
    (h : PostOutageAbove S rho P r) (core : NamedAdmissibleCore S rho)
    (w : V) (hw : w ∈ rho.honest) (t : Time) (hr : 0 < r)
    (ht : domain S.E S.hc r .g2 < t) (hta : t ≤ S.a r)
    (hhor : domain S.E S.hc r .g2 ≤ rho.horizon)
    (hPtree : P ∈ Protocol.get_filtered_block_tree
      (NamedRun.stateBeforeTime S rho t w).st.core.toHealing.toFG)
    {root : Block V}
    (hframe : (DecoupledConsensusModel.Protocol.readFrame
      (NamedRun.stateBeforeTime S rho t w).cache
      (NamedRun.stateBeforeTime S rho t w).st.core.toHealing r).g2 =
      some (some root)) :
    Block.Preceq P root ∨ Block.Preceq P
      (NamedRun.stateBeforeTime S rho t w).st.core.F := by
  rcases h.1 w hw with hPF | ⟨raw, hfreeze, hPraw⟩
  · exact Or.inr (Block.preceq_trans hPF
      (incl_strict_F_mono S rho core.toNamedScheduleWellFormed w ht.le))
  ·
    have hfreeze' : DecoupledConsensusModel.Protocol.freezeRoot S.E
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) w).st.core.toHealing.gradeView
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) w).st.core.F S.hc.η_SG r
        (early S.E S.hc r .g2) (late S.E S.hc r .g2) = some raw := by
      simpa only [postOutageFrozenG2At] using hfreeze
    obtain ⟨root', hroot', hProot⟩ := Proofs.HealingSurface.frameG2_preceq_of_freezeRoot
      S rho core w hw r hr t ht hta hhor hPtree hfreeze' hPraw
    have heq : root' = root :=
      Option.some.inj (Option.some.inj (hroot'.symm.trans hframe))
    exact Or.inl (heq ▸ hProot)

theorem PostOutageAbove.frameG1_floor_at_read
    (S : Setup V) (rho : NamedRun V) (P : Block V) (r : Round)
    (h : PostOutageAbove S rho P r) (core : NamedAdmissibleCore S rho)
    (w : V) (hw : w ∈ rho.honest) (t : Time) (hr : 0 < r)
    (ht : domain S.E S.hc r .g1 < t) (hta : t ≤ S.a r)
    (hhor : domain S.E S.hc r .g1 ≤ rho.horizon)
    (hPtree : P ∈ Protocol.get_filtered_block_tree
      (NamedRun.stateBeforeTime S rho t w).st.core.toHealing.toFG)
    {root : Block V}
    (hframe : (DecoupledConsensusModel.Protocol.readFrame
      (NamedRun.stateBeforeTime S rho t w).cache
      (NamedRun.stateBeforeTime S rho t w).st.core.toHealing r).g1 =
      some (some root)) :
    Block.Preceq P root ∨ Block.Preceq P
      (NamedRun.stateBeforeTime S rho t w).st.core.F := by
  rcases h.2.1 w hw with hPF | ⟨raw, hfreeze, hPraw⟩
  · exact Or.inr (Block.preceq_trans hPF
      (incl_strict_F_mono S rho core.toNamedScheduleWellFormed w ht.le))
  ·
    have hfreeze' : DecoupledConsensusModel.Protocol.freezeRoot S.E
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1) w).st.core.toHealing.gradeView
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1) w).st.core.F S.hc.η_SG r
        (early S.E S.hc r .g1) (late S.E S.hc r .g1) = some raw := by
      simpa only [postOutageFrozenG1At] using hfreeze
    obtain ⟨root', hroot', hProot⟩ := Proofs.HealingSurface.frameG1_preceq_of_freezeRoot
      S rho core w hw r hr t ht hta hhor hPtree hfreeze' hPraw
    have heq : root' = root :=
      Option.some.inj (Option.some.inj (hroot'.symm.trans hframe))
    exact Or.inl (heq ▸ hProot)

theorem PostOutageAbove.stable
    (S : Setup V) (rho : NamedRun V) (P : Block V) (r : Round)
    (h : PostOutageAbove S rho P r) (w : V) (hw : w ∈ rho.honest) (t : Time)
    (hlo : domain S.E S.hc r .g2 ≤ t)
    (hhi : t ≤ domain S.E S.hc (r + 1) .g2) :
    Block.Preceq P
      (Protocol.get_stable (NamedRun.stateBeforeTime S rho t w).st.core) :=
  h.2.2 w hw t hlo hhi

theorem PostOutageAbove.stable_at_voteDuty
    (S : Setup V) (rho : NamedRun V) (P : Block V) (r : Round)
    (h : PostOutageAbove S rho P r) (v : V) (hv : v ∈ rho.honest)
    (s : Slot) (hlo : domain S.E S.hc r .g2 ≤ Protocol.vote_time S.E s)
    (hhi : Protocol.vote_time S.E s ≤ domain S.E S.hc (r + 1) .g2) :
    Block.Preceq P
      (Protocol.get_stable (postOutageVoteDutyReadAt S rho v s).st.core) := by
  apply h.2.2 v hv (Protocol.vote_time S.E s)
  · exact hlo
  · exact hhi

theorem PostOutageAbove.stable_at_relativeG2
    (S : Setup V) (rho : NamedRun V) (P : Block V) (r : Round)
    (h : PostOutageAbove S rho P r) (w : V) (hw : w ∈ rho.honest) :
    Block.Preceq P
      (Protocol.get_stable (postOutageReadAt S rho w r).st.core) := by
  exact h.2.2 w hw (domain S.E S.hc r .g2) le_rfl
    (base_domain_g2_mono S (Nat.le_succ r))

theorem PostOutageAbove.stable_at_read_of_write_floors
    (S : Setup V) (rho : NamedRun V) (P : Block V) (r : Round)
    (h : PostOutageAbove S rho P r) (core : NamedAdmissibleCore S rho)
    (w : V) (hw : w ∈ rho.honest)
    (hviable : P ∈ filteredTree
      (Proofs.HealingSurface.relativeG2Read S rho (r + 1) w))
    (t : Time) (hlo : domain S.E S.hc r .g2 ≤ t)
    (hhi : t ≤ domain S.E S.hc (r + 1) .g2)
    (hwrite : ∀ (k : Nat) (u : Time),
      (rho.events[k]? = some (.tick w u)) →
      0 < S.E.slotOf u → u = Protocol.support_cutoff S.E (S.E.slotOf u) →
      ∀ G, dutyStableRoot S
        (NamedActionReads.confirmationReadFrom
          S (NamedRun.stateBefore S rho k w) u) = some G →
        Block.Preceq P G) :
    Block.Preceq P
      (Protocol.get_stable (NamedRun.stateBeforeTime S rho t w).st.core) := by
  let start := domain S.E S.hc r .g2
  let stop := domain S.E S.hc (r + 1) .g2
  let i := (rho.events.filter (fun e => decide (e.time < start))).length
  let j := (rho.events.filter (fun e => decide (e.time < t))).length
  have hi : NamedRun.stateBeforeTime S rho start w = NamedRun.stateBefore S rho i w := by
    exact congrFun
      (Proofs.Optimistic.stateBeforeTime_eq_take S core.toNamedScheduleWellFormed start) w
  have hj : NamedRun.stateBeforeTime S rho t w = NamedRun.stateBefore S rho j w := by
    exact congrFun
      (Proofs.Optimistic.stateBeforeTime_eq_take S core.toNamedScheduleWellFormed t) w
  have hij : i ≤ j := by
    dsimp only [i, j]
    exact strict_lengths_mono rho hlo
  have hFstop : Block.Preceq
      (NamedRun.stateBeforeTime S rho t w).st.core.F
      (NamedRun.stateBeforeTime S rho stop w).st.core.F := by
    exact incl_strict_F_mono S rho core.toNamedScheduleWellFormed w hhi
  have hPtree : P ∈ Protocol.get_filtered_block_tree
      (NamedRun.stateBeforeTime S rho stop w).st.core.toHealing.toFG := by
    simpa only [stop, Proofs.HealingSurface.relativeG2Read, Internal.PhaseGrades.filteredTree] using hviable
  have hFleP : Block.Preceq
      (NamedRun.stateBeforeTime S rho stop w).st.core.F P :=
    NamedOutageClosure.q10_filtered_F hPtree
  have hcompat : Block.compatible P
      (NamedRun.stateBeforeTime S rho t w).st.core.F = true := by
    simp only [Block.compatible, Bool.or_eq_true]
    exact Or.inr (Block.preceq_trans hFstop hFleP)
  exact Proofs.HealingSurface.stable_preceq_of_stable_writes_above_at_time S rho w hi hj hij
    (by simpa only [start] using
      PostOutageAbove.stable_at_relativeG2 S rho P r h w hw)
    (fun k u hk hkj he hpos hcut G hG => hwrite k u he hpos hcut G hG) hcompat

theorem PostOutageAbove.frozenG2
    (S : Setup V) (rho : NamedRun V) (P : Block V) (r : Round)
    (h : PostOutageAbove S rho P r) (w : V) (hw : w ∈ rho.honest)
    (G : Block V) (hG : postOutageFrozenG2At S rho w r = some G) :
    Block.Preceq P G ∨
      Block.Preceq P (postOutageReadAt S rho w r).st.core.F := by
  rcases h.1 w hw with hPF | ⟨R, hR, hPR⟩
  · exact Or.inr hPF
  · exact Or.inl (Option.some.inj (hR.symm.trans hG) ▸ hPR)

theorem PostOutageAbove.frozenG1
    (S : Setup V) (rho : NamedRun V) (P : Block V) (r : Round)
    (h : PostOutageAbove S rho P r) (w : V) (hw : w ∈ rho.honest)
    (G : Block V) (hG : postOutageFrozenG1At S rho w r = some G) :
    Block.Preceq P G ∨ Block.Preceq P
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1) w).st.core.F := by
  rcases h.2.1 w hw with hPF | ⟨R, hR, hPR⟩
  · exact Or.inr hPF
  · exact Or.inl (Option.some.inj (hR.symm.trans hG) ▸ hPR)

/-! ## Prepared selector floors -/



/-! ## Prepared SG target transport -/


/-! ## The common-ancestor half of the frozen-root comparison -/



/-! ## S1--S5 transport lemmas -/

/- S1 is the final raw-freeze transport. The positive and opposition facts
   remain explicit because they are the run-level input to the frozen-root
   producer, not a standing assumption of the public statement. -/


/- S2 transports the frame-floor case split to the prepared vote-duty anchor. -/

/- S3 is the prepared selector transport for one emitted honest attestation. -/


/- S4 is the raw G2 freeze transport once the interpreted inputs and their
   resolved heads have been supplied. -/




/- Comparable confirmation roots preserve the stable record through an index
interval. Deliveries and unrelated events preserve the record exactly. -/
theorem stateBefore_stable_covered_of_comparable
    (S : Setup V) (rho : NamedRun V) (w : V) {P : Block V}
    (i j : Nat) (hij : i ≤ j)
    (hold : Block.Preceq P (NamedRun.stateBefore S rho i w).st.core.F ∨
      Block.Preceq P (NamedRun.stateBefore S rho i w).st.core.latest_stable)
    (hcov : ∀ (k : Nat) (t : Time), i ≤ k → k < j →
      rho.events[k]? = some (.tick w t) →
      0 < S.E.slotOf t → t = Protocol.support_cutoff S.E (S.E.slotOf t) →
      ∀ G, dutyStableRoot S
        (NamedActionReads.confirmationReadFrom
          S (NamedRun.stateBefore S rho k w) t) = some G →
        Block.Preceq P (NamedRun.stateBefore S rho k w).st.core.latest_stable →
        Block.Preceq P G ∨ Block.Preceq G P) :
    Block.Preceq P (NamedRun.stateBefore S rho j w).st.core.F ∨
    Block.Preceq P (NamedRun.stateBefore S rho j w).st.core.latest_stable := by
  induction j, hij using Nat.le_induction with
  | base => exact hold
  | succ j hij ih =>
      have hstep := ih (fun k t hk hkj => hcov k t hk (Nat.lt_succ_of_lt hkj))
      have hFmono : Block.Preceq (NamedRun.stateBefore S rho j w).st.core.F
          (NamedRun.stateBefore S rho (j + 1) w).st.core.F :=
        Proofs.NamedRuntime.stateBefore_F_mono S rho w (Nat.le_succ j)
      rcases hstep with hF | hlat
      · exact Or.inl (Block.preceq_trans hF hFmono)
      have hgoal : Block.Preceq P (NamedRun.stateBefore S rho j w).st.core.F ∨
          Block.Preceq P
            (NamedRun.stateBefore S rho (j + 1) w).st.core.latest_stable := by
        cases he : rho.events[j]? with
        | none =>
            refine Or.inr ?_
            rw [Proofs.NamedRuntime.stateBefore_succ]
            simpa only [he, Option.toList_none, List.foldl_nil] using hlat
        | some e =>
            cases e with
            | deliver u o t' =>
                refine Or.inr ?_
                by_cases hu : u = w
                · have he' : rho.events[j]? = some (.deliver w o t') := by
                    rw [← hu]
                    exact he
                  rw [Proofs.NamedRuntime.stateBefore_deliver S rho he', node_process_stable]
                  exact hlat
                · rw [Proofs.NamedRuntime.stateBefore_other S rho he w (fun h => hu h.symm)]
                  exact hlat
            | tick u t' =>
                by_cases hu : u = w
                · have he' : rho.events[j]? = some (.tick w t') := by
                    rw [← hu]
                    exact he
                  rcases node_tick_stable_cases S w
                      (NamedRun.stateBefore S rho j w) t' with
                    ⟨-, heq⟩ | ⟨⟨hpos, hcut⟩, heq⟩
                  · refine Or.inr ?_
                    rw [Proofs.NamedRuntime.stateBefore_tick S rho he', heq]
                    exact hlat
                  · refine Or.inr ?_
                    rw [Proofs.NamedRuntime.stateBefore_tick S rho he', heq]
                    exact confirmation_write_stable_of_comparable S _ _ hlat
                      (fun G hG => hcov j t' hij (Nat.lt_succ_self j)
                        he' hpos hcut G hG hlat)
                · rw [Proofs.NamedRuntime.stateBefore_other S rho he w (fun h => hu h.symm)]
                  exact Or.inr hlat
      rcases hgoal with hF | hlat'
      · exact Or.inl (Block.preceq_trans hF hFmono)
      · exact Or.inr hlat'

/- S5 keeps the stable output above P through the confirmation writes of the
   successor round. Only the preceding stable interval is needed. -/
theorem stable_above_P_through_succ_of_floor
    (S : Setup V) {rho : Run V} (P : Block V) (r : Round)
    (hstable : ∀ w ∈ rho.honest, ∀ t,
      domain S.E S.hc r .g2 ≤ t → t ≤ domain S.E S.hc (r + 1) .g2 →
      Block.Preceq P
        (Protocol.get_stable (NamedRun.stateBeforeTime S rho t w).st.core))
    (core : NamedAdmissibleCore S rho)
    {w : V} (hw : w ∈ rho.honest)
    (hviable : ∀ u ∈ rho.honest,
      Block.Preceq P
          (Protocol.get_fg_root
            (Proofs.HealingSurface.relativeG2Read S rho (r + 2) u).st.core.toHealing.toFG) ∨
        P ∈ filteredTree (Proofs.HealingSurface.relativeG2Read S rho (r + 2) u))
    (t : Time) (hlo : domain S.E S.hc (r + 1) .g2 ≤ t)
    (hhi : t ≤ domain S.E S.hc (r + 2) .g2)
    (hwrite : ∀ (k : Nat) (u : Time),
      domain S.E S.hc (r + 1) .g2 ≤ u → u < t →
      rho.events[k]? = some (.tick w u) →
      0 < S.E.slotOf u → u = Protocol.support_cutoff S.E (S.E.slotOf u) →
      ∀ G, dutyStableRoot S
        (NamedActionReads.confirmationReadFrom
          S (NamedRun.stateBefore S rho k w) u) = some G →
        Block.Preceq P (NamedRun.stateBefore S rho k w).st.core.latest_stable →
        Block.Preceq P G ∨ Block.Preceq G P) :
    Block.Preceq P
      (Protocol.get_stable (NamedRun.stateBeforeTime S rho t w).st.core) :=
  by
    let start := domain S.E S.hc (r + 1) .g2
    let stop := domain S.E S.hc (r + 2) .g2
    let i := (rho.events.filter (fun e => decide (e.time < start))).length
    let j := (rho.events.filter (fun e => decide (e.time < t))).length
    have hi : NamedRun.stateBeforeTime S rho start w =
        NamedRun.stateBefore S rho i w := by
      exact congrFun
        (Proofs.Optimistic.stateBeforeTime_eq_take S core.toNamedScheduleWellFormed start) w
    have hj : NamedRun.stateBeforeTime S rho t w =
        NamedRun.stateBefore S rho j w := by
      exact congrFun
        (Proofs.Optimistic.stateBeforeTime_eq_take S core.toNamedScheduleWellFormed t) w
    have hij : i ≤ j := by
      dsimp only [i, j]
      exact strict_lengths_mono rho hlo
    have hhold : Block.Preceq P
        (Protocol.get_stable (NamedRun.stateBeforeTime S rho start w).st.core) := by
      exact hstable w hw start
        (base_domain_g2_mono S (Nat.le_succ r)) le_rfl
    have hFstop : Block.Preceq
        (NamedRun.stateBeforeTime S rho t w).st.core.F
        (NamedRun.stateBeforeTime S rho stop w).st.core.F := by
      exact incl_strict_F_mono S rho core.toNamedScheduleWellFormed w hhi
    have hcompat : Block.compatible P
        (NamedRun.stateBeforeTime S rho t w).st.core.F = true := by
      rcases hviable w hw with hroot | hPtree
      · have hFJ := Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
          S rho stop w
        have hFroot := Proofs.Records.preceq_get_fg_root_of_F
          (st := (NamedRun.stateBeforeTime S rho stop w).st.core.toHealing.toFG)
          (by simpa only [Protocol.Store.toHealing] using hFJ)
        have hroot' : Block.Preceq P
            (Protocol.get_fg_root
              (NamedRun.stateBeforeTime S rho stop w).st.core.toHealing.toFG) := by
          simpa only [stop, Proofs.HealingSurface.relativeG2Read,
            Internal.PhaseGrades.filteredTree] using hroot
        exact Block.compatible_of_preceq_common hroot'
          (Block.preceq_trans hFstop hFroot)
      · have hFleP : Block.Preceq
            (NamedRun.stateBeforeTime S rho stop w).st.core.F P :=
          NamedOutageClosure.q10_filtered_F (by
            simpa only [stop, Proofs.HealingSurface.relativeG2Read,
              Internal.PhaseGrades.filteredTree] using hPtree)
        simp only [Block.compatible, Bool.or_eq_true]
        exact Or.inr (Block.preceq_trans hFstop hFleP)
    have hstart : Block.Preceq P (NamedRun.stateBefore S rho i w).st.core.F ∨
        Block.Preceq P (NamedRun.stateBefore S rho i w).st.core.latest_stable := by
      rw [← hi]
      unfold Protocol.get_stable at hhold
      split at hhold
      · exact Or.inr hhold
      · exact Or.inl hhold
    have hcases := stateBefore_stable_covered_of_comparable S rho w i j hij hstart
      (fun k u hk hkj he hpos hcut G hG hlat => by
        have huLo : start ≤ u := Proofs.Optimistic.le_time_of_index_ge S
          core.toNamedScheduleWellFormed (t := start) (j := k) hk he
        have huHi : u < t := by
          have hinside := Proofs.Optimistic.filter_true_of_index_lt S
            core.toNamedScheduleWellFormed (fun e => decide (e.time < t))
            (Proofs.Optimistic.downward_lt t) hkj he
          simpa only [decide_eq_true_eq, NamedEvent.time] using hinside
        exact hwrite k u (by simpa only [start] using huLo) huHi
          he hpos hcut G hG hlat)
    rw [hj]
    rw [hj] at hcompat
    rcases hcases with hF | hstable
    · have hFstable : Block.Preceq
          (NamedRun.stateBefore S rho j w).st.core.F
          (Protocol.get_stable (NamedRun.stateBefore S rho j w).st.core) := by
        unfold Protocol.get_stable
        split
        · assumption
        · exact Block.preceq_self _
      exact Block.preceq_trans hF hFstable
    · exact preceq_get_stable_of_cases _ (Or.inr hstable) hcompat


/- Once the five producer outputs are available, the successor is only the
   definition-level assembly. This theorem does not manufacture any of the
   five outputs. -/
theorem postOutageAbove_succ_of_chain
    (S : Setup V) (rho : Run V) (P : Block V) (r : Round)
    (hG2 : ∀ w ∈ rho.honest, Block.Preceq P
      (postOutageReadAt S rho w (r + 1)).st.core.F ∨
        ∃ R, postOutageFrozenG2At S rho w (r + 1) = some R ∧ Block.Preceq P R)
    (hG1 : ∀ w ∈ rho.honest, Block.Preceq P
      (NamedRun.stateBeforeTime S rho
        (domain S.E S.hc (r + 1) .g1) w).st.core.F ∨
        ∃ R, postOutageFrozenG1At S rho w (r + 1) = some R ∧ Block.Preceq P R)
    (hstable : ∀ w ∈ rho.honest, ∀ t,
      domain S.E S.hc (r + 1) .g2 ≤ t → t ≤ domain S.E S.hc (r + 2) .g2 →
      Block.Preceq P
        (Protocol.get_stable (NamedRun.stateBeforeTime S rho t w).st.core)) :
    PostOutageAbove S rho P (r + 1) :=
  ⟨hG2, hG1, hstable⟩










#print axioms support_cutoff_round_of_domain_window
#print axioms domain_g2_lt_support_cutoff_of_le
#print axioms voteDutyHead_preceq_voteDutyAnchor
#print axioms preceq_voteDutyHead_of_preceq_voteDutyAnchor
#print axioms advance_confirmed_retains_of_comparable
#print axioms confirmation_write_stable_of_comparable
#print axioms duty_root_comparable_of_frame
#print axioms confirmationDutyRoot_above_of_postOutageG2
#print axioms PostOutageAbove.anchor
#print axioms PostOutageAbove.anchor_at_prepared_read
#print axioms PostOutageAbove.anchor_at_action_read
#print axioms PostOutageAbove.actionSGBlock_floor
#print axioms PostOutageAbove.emitted_vote_floor
#print axioms PostOutageAbove.emitted_vote_floor_of_finalized_or_active
#print axioms PostOutageAbove.frameG2_floor_at_read
#print axioms PostOutageAbove.frameG1_floor_at_read
#print axioms PostOutageAbove.stable
#print axioms PostOutageAbove.stable_at_voteDuty
#print axioms PostOutageAbove.stable_at_relativeG2
#print axioms PostOutageAbove.stable_at_read_of_write_floors
#print axioms PostOutageAbove.frozenG2
#print axioms PostOutageAbove.frozenG1
#print axioms stable_above_P_through_succ_of_floor
#print axioms stateBefore_stable_covered_of_comparable
#print axioms postOutageAbove_succ_of_chain

end DecoupledConsensusModel.Proofs.NamedOutageClosure

end
