module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ValidatorClient.SeedPredPromotion
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.HeightProgressCompose
public import DecoupledConsensusProofs.Protocol.ChainState.HeightProgressFixedRootRows
public import DecoupledConsensusProofs.Execution.FixedRootCarrierChain
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.FixedHeightRootRelativeAnchor

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Internal.PhaseGrades
open Protocol
open Proofs.HealingLemmas
open DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}

/-! ## The round arithmetic, stated at `Nat`

`Round` and `Height` are `abbrev`s of `Nat`, but `omega` matches the syntactic
type and reports `No usable constraints found` on a goal whose variables carry
the abbreviation. Every arithmetic step of the route is therefore stated once
here over bare `Nat` and applied at `Round`/`Height`, exactly as
`HeightProgressComposeRun` does. -/

private theorem fixedRootPred_le_nat {r k : Nat} (h : r + 1 ≤ k) :
    r ≤ k - 1 := by omega

private theorem fixedRootWindow_nat {r k : Nat} (h : r + 2 ≤ k) :
    0 < k ∧ r + 1 ≤ k ∧ r + 1 ≤ k - 1 ∧ r ≤ k - 1 := by omega

private theorem fixedClaimOneBound_nat {r gap endpoint : Nat}
    (h : r + 3 * gap + 8 + 2 * delayExtra ≤ endpoint) :
    r + 4 + gap ≤ endpoint := by omega

private theorem fixedFirstBounds_nat {r gap endpoint q1 : Nat}
    (hbound : r + 3 * gap + 8 + 2 * delayExtra ≤ endpoint)
    (hlo : r + 3 ≤ q1) (hhi : q1 ≤ r + 3 + gap) :
    0 < q1 ∧ q1 ≤ endpoint ∧ r + 1 ≤ q1 - 1 ∧ r ≤ q1 - 1 ∧
      r + 1 ≤ q1 ∧ r ≤ q1 ∧ q1 + delayExtra + 4 + gap ≤ endpoint ∧
        r ≤ q1 + 1 ∧ r + 2 ≤ q1 := by
  omega

private theorem fixedSecondBounds_nat {r gap endpoint q1 q2 : Nat}
    (hbound : r + 3 * gap + 8 + 2 * delayExtra ≤ endpoint)
    (hq1lo : r + 3 ≤ q1)
    (hq1hi : q1 ≤ r + 3 + gap)
    (hq2lo : q1 + delayExtra + 3 ≤ q2)
    (hq2hi : q2 ≤ q1 + delayExtra + 3 + gap) :
    0 < q2 ∧ q1 < q2 ∧ q2 ≤ endpoint ∧ r + 1 ≤ q2 - 1 ∧
      r + 1 ≤ q2 + 1 ∧ r ≤ q2 + 1 ∧ r ≤ q2 ∧ q1 + 1 ≤ q2 - 1 ∧
        0 < q2 - 1 ∧ q1 + 2 + delayExtra ≤ q2 := by
  omega

private theorem fixedThirdEnd_nat {r gap endpoint q1 q2 q3 : Nat}
    (hbound : r + 3 * gap + 8 + 2 * delayExtra ≤ endpoint)
    (hq1lo : r + 3 ≤ q1)
    (hq1hi : q1 ≤ r + 3 + gap)
    (hq2lo : q1 + delayExtra + 3 ≤ q2)
    (hq2hi : q2 ≤ q1 + delayExtra + 3 + gap)
    (hq3lo : q2 + 2 + delayExtra ≤ q3)
    (hq3hi : q3 ≤ q2 + 2 + delayExtra + gap) :
    q3 ≤ endpoint ∧ r + 3 ≤ q3 := by omega

private theorem fixedExactEnd_nat {r gap endpoint q1 q2 : Nat}
    (hbound : r + 3 * gap + 8 + 2 * delayExtra ≤ endpoint)
    (hq1lo : r + 3 ≤ q1)
    (hq1hi : q1 ≤ r + 3 + gap)
    (hq2lo : q1 + 2 + delayExtra ≤ q2)
    (hq2hi : q2 ≤ q1 + 2 + delayExtra + gap) :
    q2 ≤ endpoint ∧ r + 3 ≤ q2 := by omega

private theorem fixedRootLockRounds_nat {r q : Nat} (h : r + 3 ≤ q) :
    r < q ∧ r + 2 ≤ q - 1 ∧ 0 < q - 1 := by omega

private theorem fixedRootCarrierSpacing_nat {entry q : Nat}
    (h : entry + 2 + delayExtra ≤ q) : entry < q ∧ entry + 2 ≤ q := by omega

private theorem fixedRootSeedWindow_nat {entry q : Nat}
    (h : entry + 2 + delayExtra ≤ q) :
    0 < q ∧ entry + 1 ≤ q ∧ entry + 1 ≤ q - 1 ∧ entry < q ∧
      q - 1 + 1 = q := by omega


private theorem fixedRootWindowLower_nat {r q1 r' : Nat}
    (hr : r + 1 ≤ q1) (hq1 : q1 + 1 ≤ r') : r + 1 ≤ r' := by omega

private theorem fixedRootParentHeight_nat {a b c m : Nat}
    (h1 : b ≤ a) (h2 : a ≤ c) (h3 : c = m) (h4 : b = m) : a = b := by omega

/-! ## Local copies of the composition helpers

`HeightProgressComposeRun` keeps these `private`, so the restated route needs its
own copies. They are byte-identical to the originals. -/

private theorem fixedRootParent_preceq_namedProposal
    (S : Setup V) (rho : Run V) (s : Slot) {B : NamedBlock V}
    (hB : proposedBlockAt S rho s = some B) :
    Block.Preceq (proposedParent S rho s) B.erase := by
  obtain ⟨p, hp, hpe⟩ := proposedBlockAt_parent S rho s hB
  cases B with
  | genesis => cases hp
  | node parent slot root votes support rows proposer =>
      have hparent : parent = p := Option.some.inj hp
      subst p
      rw [← hpe]
      exact Proofs.NamedWire.erase_preceq (by
        simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true]
        exact Or.inr (Proofs.NamedAncestry.named_self parent))

omit [Fintype V] in
private theorem fixedRootNamedParent_preceq_of_parent?
    {B P : NamedBlock V} (h : NamedBlock.parent? B = some P) :
    NamedBlock.Preceq P B := by
  cases B with
  | genesis => cases h
  | node parent slot root votes support rows proposer =>
      have hparent : parent = P := Option.some.inj h
      subst P
      simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true]
      exact Or.inr (Proofs.NamedAncestry.named_self parent)

private theorem fixedRootJustificationRoot_target_named
    (S : Setup V) {rho : Run V} {H : Height} {w : V} {read : Time}
    (h : FixedHeightJustificationRootAtRead S rho H w read) :
    ∃ J : NamedBlock V,
      J.erase = (rho.storeBeforeTime S w read).J ∧
        RunBlock S rho J ∧
          (Protocol.derive_named S.E S.cfg J).h = H - 1 := by
  obtain ⟨D, _hDbody, hDrun, hjust⟩ := h.carrierExists
  have hhj : (Protocol.derive_named S.E S.cfg D).h_j = H - 1 :=
    hjust.2.trans (by simpa only using h.fixedTarget.justificationHeight)
  have hhjNe : (Protocol.derive_named S.E S.cfg D).h_j ≠ 0 := by
    rw [hhj]
    exact Nat.ne_of_gt h.targetHeightPositive
  obtain ⟨J, hJD, hJerase, hJheight⟩ :=
    (NamedCheckpointHeights.justified_ancestor_height S.E S.cfg D).resolve_left hhjNe
  refine ⟨J, hJerase.trans hjust.1, ?_, ?_⟩
  · exact Proofs.NamedRuntime.blockInRun_of_ancestor S rho hDrun hJD
  · rw [hJheight, hhj]

/-- A named Claim-4 lifecycle under the justification-root-only record has a
proposal at the fixed frontier or one height below it. -/
private theorem fixedRootClaimFour_height_pred_or_current
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {M : Height} {w : V} {read : Time}
    (hfix : FixedHeightJustificationRootAtRead S rho M w read)
    {q : Round} (hq : 0 < q) {B : NamedBlock V}
    (hpacket : NamedSGProposalLifecyclePacket S rho (q - 1)
      (S.hc.opening_slot q - 1) B)
    (hactionExact : ∀ v ∈ rho.honest,
      Protocol.get_fg_root
          (rho.storeBeforeTime S v (S.a (q - 1))).toHealing.toFG =
        (rho.storeBeforeTime S w read).J ∧
      (rho.storeBeforeTime S v (S.a (q - 1))).h_max = M)
    {endpoint : Time}
    (hproposalEndpoint :
      Protocol.proposal_time S.E (S.hc.opening_slot q) ≤ endpoint)
    (hcap : honestHMaxAt S rho endpoint ≤ M) :
    Block.Preceq (rho.storeBeforeTime S w read).J B.erase ∧
      ((Protocol.derive_named S.E S.cfg B).h = M - 1 ∨
        (Protocol.derive_named S.E S.cfg B).h = M) := by
  have hqPredAdd : q - 1 + 1 = q := Nat.sub_add_cancel hq
  have hlifecycle : NamedRawOpeningLifecycleAt S rho q B := by
    simpa only [hqPredAdd] using hpacket.lifecycle
  let p := S.E.proposer (S.hc.opening_slot q)
  have hp : p ∈ rho.honest := by
    simpa only [p] using hlifecycle.proposerHonest
  have hrootAction :
      Protocol.get_fg_root
          (actionStoreAt S rho p (q - 1)).toHealing.toFG =
        (rho.storeBeforeTime S w read).J := by
    rw [actionStoreAt_fgRoot_eq_storeBeforeTime S rho p (q - 1)]
    exact (hactionExact p hp).1
  have htargetParent : Block.Preceq
      (actionSGBlockAt S rho p (q - 1))
      (proposedParent S rho (S.hc.opening_slot q)) := by
    simpa only [hqPredAdd] using hpacket.actionTargetParent p hp
  have hJtarget : Block.Preceq (rho.storeBeforeTime S w read).J
      (actionSGBlockAt S rho p (q - 1)) := by
    rw [← hrootAction]
    exact actionFGRoot_preceq_actionSGBlockAt S rho p (q - 1)
  have hJB : Block.Preceq (rho.storeBeforeTime S w read).J B.erase :=
    Block.preceq_trans (Block.preceq_trans hJtarget htargetParent)
      (fixedRootParent_preceq_namedProposal S rho _ hlifecycle.proposal)
  obtain ⟨J, hJerase, hJrun, hJheight⟩ :=
    fixedRootJustificationRoot_target_named S hfix
  obtain ⟨J', hJ'B, hJ'erase⟩ :=
    Proofs.NamedAncestry.erased_ancestor_lift B hJB
  have hJ'run : RunBlock S rho J' :=
    Proofs.NamedRuntime.blockInRun_of_ancestor S rho hlifecycle.runBlock hJ'B
  have hrootEq : J'.root = J.root := by
    rw [← Proofs.NamedWire.erase_root J', ← Proofs.NamedWire.erase_root J,
      hJ'erase, hJerase]
  have hJ'eq : J' = J :=
    adm.toNamedRootCollisionFree.root_injective J' J hJ'run hJrun J' J
      (Or.inl (Proofs.NamedAncestry.named_self J'))
      (Or.inr (Proofs.NamedAncestry.named_self J)) hrootEq
  have hheightLower : M - 1 ≤
      (Protocol.derive_named S.E S.cfg B).h := by
    rw [← hJheight, ← hJ'eq]
    exact Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hJ'B
  have hspos : 0 < S.hc.opening_slot q := by
    unfold Protocol.HealConfig.opening_slot
    exact Nat.mul_pos hq
      (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
  have hpublicProposalCap : honestHMaxAt S rho
      (Protocol.proposal_time S.E (S.hc.opening_slot q)) ≤ M :=
    (honestHMaxAt_mono S adm.toNamedScheduleWellFormed
      hproposalEndpoint).trans hcap
  have hheightUpper : (Protocol.derive_named S.E S.cfg B).h ≤ M :=
    (honestProposedBlock_height_le_honestHMaxAt
      S adm hspos hlifecycle.proposerHonest hlifecycle.proposalInHorizon
        hlifecycle.proposal).trans hpublicProposalCap
  refine ⟨hJB, ?_⟩
  let x : Nat := (Protocol.derive_named S.E S.cfg B).h
  let H : Nat := M
  have hlower : H - 1 ≤ x := by
    simpa only [H, x] using hheightLower
  have hupper : x ≤ H := by
    simpa only [H, x] using hheightUpper
  have hx : x = H - 1 ∨ x = H := by omega
  simpa only [H, x] using hx

/-! ## The opening cone-root lock at any window round

`fixedHeightJustificationRoot_boundedOpeningConeRootLock_of_proposerRecurrence_of_faultBound`
(`FixedHeightRootClaimOneRun.lean:388`) searches for its round with the proposer
recurrence, and returns the lock only at the round it found. Its lock
construction never uses the carrier: it needs the round's own predecessor
grade at the fixed target plus the no-rise window facts. Those the route has at
every window round, so the same construction is repeated here per round. The
proof body is the original one, with the recurrence endpoint generalised. -/

private theorem fixedRootRunBlock_of_body_at_read
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {w : V} (hw : w ∈ rho.honest) {read : Time} {B : NamedBlock V}
    (hB : B ∈ (rho.storeBeforeTime S w read).bodies) :
    RunBlock S rho B := by
  obtain ⟨i, hi, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
    adm.toNamedAdmissibleCore.toNamedScheduleWellFormed.sorted read
  apply Proofs.Bridges.runBlock_of_stateBefore_mem S hw
  have hB' := hB
  change B ∈ (NamedRun.stateBeforeTime S rho read w).st.bodies at hB'
  rw [congrFun hi w] at hB'
  exact hB'

private theorem fixedRootNamed_run_eq_of_erase
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    {A B : NamedBlock V} (hA : RunBlock S rho A) (hB : RunBlock S rho B)
    (herase : A.erase = B.erase) : A = B :=
  adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective A B hA hB A B
    (Or.inl (Proofs.NamedAncestry.named_self A)) (Or.inr (Proofs.NamedAncestry.named_self B))
    (by rw [← Proofs.NamedWire.erase_root A, ← Proofs.NamedWire.erase_root B, herase])

private theorem fixedRootNamedGradeProcessedAtAction
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} {C : Block V} (hforms : NamedGradeFormsAt S rho r C)
    {v : V} (hv : v ∈ rho.honest) :
    C ∈ (rho.storeBeforeTime S v (S.a r)).core.T := by
  have hsource : C ∈ (rho.storeBeforeTime S v
      (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g2)).core.T := by
    have hfiltered := (hforms v hv).1
    have htree := Proofs.Records.get_filtered_block_tree_subset _ hfiltered
    simpa only [PhaseGrades.filteredTree, PhaseGrades.readAt,
      Run.storeBeforeTime] using htree
  rw [storeBeforeTime_eq_storeAt_sub_one_recovery] at hsource ⊢
  apply StoreFinality.stateAt_T_subset
    S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed v
      (Int.sub_le_sub_right (FrameForward.domain_le_a S r .g2) 1) hsource

/-- The Claim-1 opening cone-root lock at one window round. -/
private theorem fixedRootConeRootLock_at_windowRound
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {H : Height} {w : V} {read : Time}
    (h : FixedHeightJustificationRootAtRead S rho H w read)
    {r q endRound : Round}
    (hpost : S.E.t_GST ≤ read) (hreadAction : read ≤ S.a r)
    (hqlo : r + 3 ≤ q) (hqEnd : q ≤ endRound)
    (hendHor : S.a endRound ≤ rho.horizon)
    (hcapEnd : honestHMaxAt S rho (S.a endRound) ≤ H)
    (hforms : NamedGradeFormsAt S rho (q - 1)
      (rho.storeBeforeTime S w read).J) :
    S.E.t_GST ≤ Protocol.vote_time S.E (S.hc.opening_slot q - 1) ∧
      SGTargetOpeningConeRootLock S rho H (q - 1)
        (S.hc.opening_slot q - 1) := by
  obtain ⟨Jn, hJnErase, hJnRun, hJnHeight⟩ :=
    fixedRootJustificationRoot_target_named S h
  have hformsNamed : NamedGradeFormsAt S rho (q - 1) Jn.erase := by
    simpa only [hJnErase] using hforms
  have hqlo' : r + 1 + 2 ≤ q := by
    simpa only [Nat.add_assoc] using hqlo
  have hqTwo : 2 ≤ q :=
    (Nat.le_add_left 2 (r + 1)).trans hqlo'
  have hqOne : 1 ≤ q :=
    (by decide : 1 ≤ 2).trans hqTwo
  have hqPos : 0 < q :=
    (by decide : 0 < 2).trans_le hqTwo
  have hqPredPos : 0 < q - 1 :=
    Nat.sub_pos_of_lt (show 1 < q from hqTwo)
  have hqActionLower : r + 1 ≤ q - 2 :=
    Nat.le_sub_of_add_le hqlo'
  have hqActionSucc : q - 2 ≤ q - 1 :=
    Nat.sub_le_sub_left (by decide : 1 ≤ 2) q
  have hqReadyLower : r + 1 ≤ q - 1 :=
    hqActionLower.trans hqActionSucc
  have hqPred : q - 2 + 1 = q - 1 := by
    have hqEq : q - 2 + 2 = q := Nat.sub_add_cancel hqTwo
    rw [← hqEq]
    simp
  have hqPredAdd : q - 1 + 1 = q :=
    Nat.sub_add_cancel hqOne
  have hqActionEnd : q - 2 ≤ endRound :=
    (Nat.sub_le q 2).trans hqEnd
  have hqNextEnd : q - 1 ≤ endRound :=
    (Nat.sub_le q 1).trans hqEnd
  have hactionAtEnd : S.a (q - 2) ≤ S.a (endRound) :=
    Assembly.a_mono S hqActionEnd
  have hnextAtEnd : S.a (q - 1) ≤ S.a (endRound) :=
    Assembly.a_mono S hqNextEnd
  have hqAtEnd : S.a q ≤ S.a (endRound) :=
    Assembly.a_mono S hqEnd
  have hdelayAction : read + S.E.Δ ≤ S.a (q - 2) := by
    calc
      read + S.E.Δ ≤ S.a r + S.E.Δ :=
        Int.add_le_add_right hreadAction S.E.Δ
      _ ≤ S.hc.Γ_neg1 S.E.Δ (r + 1) :=
        action_add_delta_le_next_Γ_neg1 S r
      _ ≤ S.a (r + 1) :=
        le_of_lt (next_Γ_neg1_lt_action S r)
      _ ≤ S.a (q - 2) := Assembly.a_mono S hqActionLower
  have hdelayNext : read + S.E.Δ ≤ S.a (q - 1) :=
    hdelayAction.trans (Assembly.a_mono S hqActionSucc)
  have hnextHor : S.a (q - 1) ≤ rho.horizon :=
    hnextAtEnd.trans hendHor
  have hnextCap : honestHMaxAt S rho (S.a (q - 1)) ≤ H :=
    (honestHMaxAt_mono S adm.toNamedScheduleWellFormed hnextAtEnd).trans hcapEnd
  have hready : GradeRoundReady S rho (q - 1) :=
    ⟨(gst_le_Γ_neg1_succ S r (hpost.trans hreadAction)).trans
        (by
          have hnextRound : r + 2 ≤ q - 1 := by
            simpa only [hqPred] using Nat.add_le_add_right hqActionLower 1
          have hmono := Γ_neg1_mono S.hc S.E.Δ_pos hnextRound
          have hround := Γ_neg1_add_rounds S.hc S.E.Δ (r + 1) 1
          have hR : (1 : Time) ≤ (S.hc.R : Nat) := by
            exact_mod_cast (le_trans (by decide : 1 ≤ 2) S.hc.R_ge_two)
          have hshift : 4 * S.E.Δ ≤
              4 * S.E.Δ * (S.hc.R * 1 : Nat) := by
            calc
              4 * S.E.Δ = 4 * S.E.Δ * 1 := by ring
              _ ≤ 4 * S.E.Δ * (S.hc.R * 1 : Nat) :=
                mul_le_mul_of_nonneg_left
                  (by simpa only [Nat.mul_one] using hR)
                  (by linarith [S.E.Δ_pos])
          have hbase : S.hc.Γ_neg1 S.E.Δ (r + 1) + 4 * S.E.Δ ≤
              S.hc.Γ_neg1 S.E.Δ (r + 2) := by
            rw [hround]
            linarith
          have hsub : S.hc.Γ_neg1 S.E.Δ (r + 1) ≤
              S.hc.Γ_neg1 S.E.Δ (r + 2) - 4 * S.E.Δ := by
            exact (le_sub_iff_add_le).2 hbase
          have hsub' := sub_le_sub_right hmono (4 * S.E.Δ)
          rw [early_g2_eq_Γ_neg1_sub]
          exact hsub.trans hsub'),
      (by
        rw [domain_g0_eq_Γ_1]
        have hΓ12 : S.hc.Γ_1 S.E.Δ (q - 1) ≤
            S.hc.Γ_2 S.E.Δ (q - 1) := by
          have h := Γ_1_add_Δ S.hc S.E.Δ (q - 1)
          linarith [S.E.Δ_pos]
        exact hΓ12.trans ((Γ_2_le_a S.hc S.E.Δ_pos (q - 1)).trans hnextHor))⟩
  obtain ⟨hslo, hshi, hsucc⟩ :=
    lastInteriorSlot_before_opening S.hc hqPos
  have hslotPrev : S.hc.opening_slot (q - 2) + 2 ≤
      S.hc.opening_slot (q - 1) := by
    calc
      S.hc.opening_slot (q - 2) + 2 ≤
          S.hc.opening_slot (q - 2) + S.hc.R :=
        Nat.add_le_add_left S.hc.R_ge_two _
      _ = S.hc.opening_slot ((q - 2) + 1) :=
        (opening_slot_succ_eq S.hc (q - 2)).symm
      _ = S.hc.opening_slot (q - 1) :=
        congrArg S.hc.opening_slot hqPred
  have hHone : 1 ≤ H :=
    Nat.le_of_lt (Nat.sub_pos_iff_lt.mp h.targetHeightPositive)
  have htargetHeightSucc :
      (Protocol.derive_named S.E S.cfg Jn).h + 1 = H := by
    rw [hJnHeight]
    exact Nat.sub_add_cancel hHone
  have htargetHeightLt :
      (Protocol.derive_named S.E S.cfg Jn).h < H := by
    rw [hJnHeight]
    exact Nat.sub_lt
      (Nat.zero_lt_of_lt (Nat.sub_pos_iff_lt.mp h.targetHeightPositive))
      (by decide : 0 < 1)
  have hsb : SlashableBound S rho :=
    slashableBound_of_admissible_belowOneThird S adm hfb
  have hactionExact : ∀ v ∈ rho.honest,
      Protocol.get_fg_root
          (actionStoreAt S rho v (q - 1)).toHealing.toFG =
        (rho.storeBeforeTime S w read).J ∧
      (actionStoreAt S rho v (q - 1)).h_max = H := by
    intro v hv
    obtain ⟨hroot, hmax⟩ :=
      fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRise
        S adm hsb h hv hpost hdelayNext hnextHor hnextCap
    refine ⟨?_, ?_⟩
    · rw [actionStoreAt_fgRoot_eq_storeBeforeTime S rho v (q - 1)]
      exact hroot
    · have hbridge : (actionStoreAt S rho v (q - 1)).h_max =
          (rho.storeBeforeTime S v (S.a (q - 1))).h_max := by
        rfl
      exact hbridge.trans hmax
  have hactionRoot : ∀ v ∈ rho.honest,
      Protocol.get_fg_root
          (actionStoreAt S rho v (q - 1)).toHealing.toFG = Jn.erase := by
    intro v hv
    exact (hactionExact v hv).1.trans hJnErase.symm
  have hactionCap : ∀ v ∈ rho.honest,
      (actionStoreAt S rho v (q - 1)).h_max ≤
        (Protocol.derive_named S.E S.cfg Jn).h + 1 := by
    intro v hv
    exact le_of_eq ((hactionExact v hv).2.trans htargetHeightSucc.symm)
  have hvoteDelay : ∀ d : Slot,
      S.hc.opening_slot (q - 1) + 1 ≤ d →
      d < S.hc.opening_slot ((q - 1) + 1) →
      read + S.E.Δ ≤ Protocol.vote_time S.E d := by
    intro d hdlo _
    have hprevOpeningLe : S.hc.opening_slot (q - 1) ≤ d :=
      (Nat.le_succ _).trans hdlo
    have hslot : S.hc.opening_slot (q - 2) + 2 ≤ d :=
      hslotPrev.trans hprevOpeningLe
    exact hdelayAction.trans
      ((le_of_lt (Protocol.action_lt_vote_time_two_after S (q - 2))).trans
        (Protocol.vote_time_mono_slots S.E hslot))
  have hvoteLeActionQ : ∀ d : Slot,
      S.hc.opening_slot (q - 1) + 1 ≤ d →
      d < S.hc.opening_slot ((q - 1) + 1) →
      Protocol.vote_time S.E d ≤ S.a q := by
    intro d _ hdhi
    have hdhiQ : d < S.hc.opening_slot q := by
      simpa only [hqPredAdd] using hdhi
    exact (Protocol.vote_time_mono_slots S.E (Nat.le_of_lt hdhiQ)).trans
      (le_of_lt (Protocol.opening_vote_time_lt_action S q))
  have hvoteExact : ∀ d : Slot,
      S.hc.opening_slot (q - 1) + 1 ≤ d →
      d < S.hc.opening_slot ((q - 1) + 1) →
      ∀ v ∈ rho.honest,
        Protocol.get_fg_root
            (Proofs.Optimistic.voteDutyStore S rho v d).toHealing.toFG =
          (rho.storeBeforeTime S w read).J ∧
        (Proofs.Optimistic.voteDutyStore S rho v d).h_max = H := by
    intro d hdlo hdhi v hv
    have hvoteEnd : Protocol.vote_time S.E d ≤ S.a (endRound) :=
      (hvoteLeActionQ d hdlo hdhi).trans hqAtEnd
    have hvoteHor : Protocol.vote_time S.E d ≤ rho.horizon :=
      hvoteEnd.trans hendHor
    have hvoteCap : honestHMaxAt S rho (Protocol.vote_time S.E d) ≤ H :=
      (honestHMaxAt_mono S adm.toNamedScheduleWellFormed hvoteEnd).trans hcapEnd
    obtain ⟨hroot, hmax⟩ :=
      fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRise
        S adm hsb h hv hpost (hvoteDelay d hdlo hdhi) hvoteHor hvoteCap
    refine ⟨?_, ?_⟩
    · change Protocol.get_fg_root
          (rho.storeBeforeTime S v (Protocol.vote_time S.E d)).toHealing.toFG =
        (rho.storeBeforeTime S w read).J
      exact hroot
    · change (rho.storeBeforeTime S v (Protocol.vote_time S.E d)).h_max = H
      exact hmax
  have hvoteRoot : ∀ d : Slot,
      S.hc.opening_slot (q - 1) + 1 ≤ d →
      d < S.hc.opening_slot ((q - 1) + 1) →
      ∀ v ∈ rho.honest,
        Protocol.get_fg_root
            (Proofs.Optimistic.voteDutyStore S rho v d).toHealing.toFG = Jn.erase := by
    intro d hdlo hdhi v hv
    exact (hvoteExact d hdlo hdhi v hv).1.trans hJnErase.symm
  have hvoteCap : ∀ d : Slot,
      S.hc.opening_slot (q - 1) + 1 ≤ d →
      d < S.hc.opening_slot ((q - 1) + 1) →
      ∀ v ∈ rho.honest,
        (Proofs.Optimistic.voteDutyStore S rho v d).h_max ≤
          (Protocol.derive_named S.E S.cfg Jn).h + 1 := by
    intro d hdlo hdhi v hv
    exact le_of_eq
      ((hvoteExact d hdlo hdhi v hv).2.trans htargetHeightSucc.symm)
  have hslotHor : Protocol.vote_time S.E (S.hc.opening_slot q - 1) ≤
      rho.horizon := by
    exact ((hvoteLeActionQ (S.hc.opening_slot q - 1) hslo hshi).trans
      hqAtEnd).trans hendHor
  have hcanonical : SGTargetConeCanonicality S rho (q - 1)
      (S.hc.opening_slot q - 1) :=
    sgTargetConeCanonicality_of_gradeFormsAt_exactFGRoot_heightCap
      S adm hcom hfb hqPredPos hready hJnRun hformsNamed hslo hshi hnextHor hslotHor
        hactionRoot hactionCap hvoteRoot hvoteCap
  have hJtarget : ∀ u ∈ rho.honest,
      Block.Preceq Jn.erase (actionSGBlockAt S rho u (q - 1)) := by
    intro u hu
    have hJraw := fixedRootNamedGradeProcessedAtAction S adm hformsNamed hu
    obtain ⟨J', hJ'body, hJ'erase⟩ :=
      Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime
        S rho (S.a (q - 1)) u hJraw
    have hJ'run := fixedRootRunBlock_of_body_at_read S adm hu hJ'body
    have hJ'eq := fixedRootNamed_run_eq_of_erase adm hJ'run hJnRun
      (hJ'erase.trans rfl)
    have hJbody : Jn ∈
        (rho.storeBeforeTime S u (S.a (q - 1))).bodies := by
      simpa only [hJ'eq] using hJ'body
    have hJactive : Jn.erase ∈ PhaseGrades.filteredTree
        (actionReadAt S rho u (q - 1)) := by
      have hfiltered := mem_filtered_of_mem_tree_of_exactFGRoot_heightCap
        S rho u (S.a (q - 1)) hJbody rfl (hactionRoot u hu)
          (Block.preceq_self Jn.erase) (hactionCap u hu)
      simpa only [PhaseGrades.filteredTree, PhaseGrades.readAt, actionReadAt,
        NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
        NamedActionReads.confirmationReadFrom,
        NamedActionReads.preparedCache] using hfiltered
    exact preceq_actionSGBlockAt_of_namedGradeFormsAt
      S adm.toNamedAdmissibleCore hqPredPos hnextHor hformsNamed hu hJactive
  have hrq : r < q :=
    (Nat.lt_succ_self r).trans_le
      (hqActionLower.trans (Nat.sub_le q 2))
  have hopenDelay : read + S.E.Δ ≤
      Protocol.vote_time S.E ((S.hc.opening_slot q - 1) + 1) := by
    rw [hsucc]
    exact ((Int.add_le_add_right hreadAction S.E.Δ).trans
      (Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt S hrq)).trans
        (le_of_lt (Protocol.proposal_time_lt_vote_time S.E
          (S.hc.opening_slot q)))
  have hopenEnd : Protocol.vote_time S.E
      ((S.hc.opening_slot q - 1) + 1) ≤ S.a (endRound) := by
    rw [hsucc]
    exact (le_of_lt (Protocol.opening_vote_time_lt_action S q)).trans
      hqAtEnd
  have hopenHor : Protocol.vote_time S.E
      ((S.hc.opening_slot q - 1) + 1) ≤ rho.horizon :=
    hopenEnd.trans hendHor
  have hopenCap : honestHMaxAt S rho
      (Protocol.vote_time S.E ((S.hc.opening_slot q - 1) + 1)) ≤ H :=
    (honestHMaxAt_mono S adm.toNamedScheduleWellFormed hopenEnd).trans hcapEnd
  have hopenExact : ∀ v ∈ rho.honest,
      Protocol.get_fg_root
          (Proofs.Optimistic.voteDutyStore S rho v
            ((S.hc.opening_slot q - 1) + 1)).toHealing.toFG =
        (rho.storeBeforeTime S w read).J ∧
      (Proofs.Optimistic.voteDutyStore S rho v
        ((S.hc.opening_slot q - 1) + 1)).h_max = H := by
    intro v hv
    obtain ⟨hroot, hmax⟩ :=
      fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRise
        S adm hsb h hv hpost hopenDelay hopenHor hopenCap
    refine ⟨?_, ?_⟩
    · change Protocol.get_fg_root
          (rho.storeBeforeTime S v
            (Protocol.vote_time S.E ((S.hc.opening_slot q - 1) + 1))).toHealing.toFG =
        (rho.storeBeforeTime S w read).J
      exact hroot
    · change (rho.storeBeforeTime S v
          (Protocol.vote_time S.E ((S.hc.opening_slot q - 1) + 1))).h_max = H
      exact hmax
  have hpostSlot : S.E.t_GST ≤
      Protocol.vote_time S.E (S.hc.opening_slot q - 1) := by
    have hreadDelay : read ≤ read + S.E.Δ :=
      le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)
    exact hpost.trans (hreadDelay.trans
      (hvoteDelay (S.hc.opening_slot q - 1) hslo hshi))
  have hcertNamed : Certificate S rho (H - 1) Jn.root := by
    have hroot : Jn.root = (rho.storeBeforeTime S w read).J.root := by
      rw [← Proofs.NamedWire.erase_root Jn, hJnErase]
    rw [hroot]
    exact h.fixedTarget.certificate
  exact ⟨hpostSlot,
    sgTargetOpeningConeRootLock_of_fixedFrontier_certifiedPrefix
      S adm hcom hfb hcanonical hJnRun hcertNamed htargetHeightLt
        hJtarget hpostSlot hopenHor (fun v hv => (hopenExact v hv).2)⟩





/-! ## The row source at a window round

The row's source and the round's SG target are the same walk down
`chain_of live_confirmed`, floored at the frozen grade-2 candidate and at the
anchor respectively (`Healing/GradeContract.lean:30,125`). Since the candidate
is below the anchor, lowering the floor cannot move the deepest clear block. -/





omit [Fintype V] in
private theorem fixedRootMem_named_chain_attestations_own
    {A : NamedBlock V} {a : NamedAttestation V}
    (ha : a ∈ A.attestations) :
    a ∈ Protocol.named_chain_attestations A := by
  cases A with
  | genesis => simp [NamedBlock.attestations] at ha
  | node p s r gv gsv rows proposer =>
      exact Finset.mem_union_right _ (List.mem_toFinset.mpr ha)

/-- A named justified run block yields the erased certificate interface. -/
private theorem fixedRootCertificate_of_namedJustifiedRunBlock
    (S : Setup V) {rho : Run V}
    {C : NamedBlock V} {J : Block V} {h : Height}
    (hCrun : RunBlock S rho C)
    (hjust : Internal.NamedJustifiedAt S.E S.cfg C J h)
    (hne : h ≠ 0) : Certificate S rho h J.root := by
  have hderivedNe : (Protocol.derive_named S.E S.cfg C).h_j ≠ 0 := by
    rw [hjust.2]
    exact hne
  obtain ⟨J', hJ'D, hJ'earse, Q, hQ, hsign⟩ :=
    NamedJustificationCertificates.justification_certificate S.E S.cfg C hderivedNe
  have hJroot : J'.root = J.root := by
    rw [← Proofs.NamedWire.erase_root J', hJ'earse, hjust.1]
  refine ⟨Q, hQ, ?_⟩
  intro i hi
  obtain ⟨carrier, a, hcarrier, ha, hav, hpair⟩ := hsign i hi
  have hcarrierRun : RunBlock S rho carrier :=
    Proofs.NamedRuntime.blockInRun_of_ancestor S rho hCrun hcarrier
  refine ⟨a,
    Or.inr ⟨carrier, hcarrierRun, fixedRootMem_named_chain_attestations_own ha⟩,
    hav, ?_⟩
  rw [hpair, hjust.2, hJroot]

omit [DecidableEq V] [Fintype V] in
/-- The target projection of a nonempty finality pair, the twin of
`Proofs.finality_pair_height`. -/
private theorem fixedRootFinality_pair_target {Λ : Protocol.Record}
    {h_j : Height} {J : BlockId} {h_F h : Height} {T : BlockId}
    (hp : Protocol.finality_pair Λ h_j J h_F = some ⟨h, T⟩) : J = T := by
  simp only [Protocol.finality_pair] at hp
  split_ifs at hp
  simp_all


/-- earlier's `actionFinalityPair_certificate` over named blocks: the finality pair
an honest action emits at a nonzero height is backed by a certificate. The head
the pair is read off is a retained body, and the store's own coherence turns its
`σ` fields into `derive_named` fields, which is what 1636 asks for. -/
private theorem fixedRootActionFinalityPair_certificate
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) (r : Round)
    {H : Height} {T : BlockId} (hH : H ≠ 0)
    (hpair : (actionAttestationAt S rho v r).finality_pair = some ⟨H, T⟩) :
    Certificate S rho H T := by
  let ast := actionStoreAt S rho v r
  have hJ : ast.st.core.J ∈ ast.st.core.T := by
    simpa only [ast, actionStoreAt, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache,
      NamedRun.stateBeforeTime] using
        Proofs.NamedStoreBridge.justifiedInTree_stateBeforeTime S rho (S.a r) v
  have hF : ast.st.core.F ∈ ast.st.core.T := by
    simpa only [ast, actionStoreAt, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache,
      NamedRun.stateBeforeTime] using
        Proofs.NamedStoreBridge.finalizedInTree_stateBeforeTime S rho (S.a r) v
  have hpair' :
      (Protocol.NamedActions.round_action_with
        (DecoupledConsensusModel.Protocol.frameContract ast.cache) S.E S.hc
        (S.node v) ast.st.core.toHealing ast.record).2.finality_pair =
          some ⟨H, T⟩ := by
    simpa only [ast, actionAttestationAt, actionStoreAt, actionReadAt,
      Protocol.NamedDuties.attest_with] using hpair
  obtain ⟨Hd, hHdDef, heq⟩ := Proofs.round_action_finality_pair
    (DecoupledConsensusModel.Protocol.frameContract ast.cache) S.E S.hc (S.node v)
    ast.st.core.toHealing ast.record
  have hfp : Protocol.finality_pair ast.record.legacy
      (ast.st.core.toHealing.σ Hd).h_j (ast.st.core.toHealing.σ Hd).J.root
      (ast.st.core.toHealing.σ Hd).h_F = some ⟨H, T⟩ := by
    rw [← heq]
    exact hpair'
  have hheight : (ast.st.core.σ Hd).h_j = H := Proofs.finality_pair_height hfp
  have htarget : (ast.st.core.σ Hd).J.root = T :=
    fixedRootFinality_pair_target hfp
  have hHdMem : Hd ∈ ast.st.core.T := by
    rw [hHdDef]
    refine NamedProposalParent.runtime_get_head_mem ast.cache S.E S.hc
      ast.st.core.toHealing _ _ _ ?_
    change (if ast.st.core.h_max = ast.st.core.h_j + 1 then ast.st.core.J
      else ast.st.core.F) ∈ ast.st.core.T
    split_ifs
    · exact hJ
    · exact hF
  have hinv : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg ast.st := by
    apply Proofs.NamedConfirmationMembership.invariant_update
    exact Proofs.NamedConfirmationMembership.invariant_clock S.E S.cfg _ (S.a r)
      (Proofs.NamedRuntime.stateBeforeTime_invariants S rho (S.a r) v).1
  have hcoh : Proofs.NamedStore.Coherent S.E S.cfg ast.st := hinv.1.1
  have hHdImage := hHdMem
  rw [hcoh.1] at hHdImage
  obtain ⟨D, hD, hDerase⟩ := Finset.mem_image.mp hHdImage
  have hsigma : ast.st.core.σ D.erase =
      Protocol.derive_named S.E S.cfg D := hcoh.2.2.2.2 D hD
  have hDrun : RunBlock S rho D := by
    refine fixedRootRunBlock_of_body_at_read S adm hv (read := S.a r) ?_
    simpa only [ast, actionStoreAt, actionReadAt,
      NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
      NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache,
      Run.storeBeforeTime] using hD
  have hDjust : Internal.NamedJustifiedAt S.E S.cfg D
      (Protocol.derive_named S.E S.cfg D).J H := by
    refine ⟨rfl, ?_⟩
    rw [← hsigma, hDerase]
    exact hheight
  have hroot : (Protocol.derive_named S.E S.cfg D).J.root = T := by
    rw [← hsigma, hDerase]
    exact htarget
  simpa only [hroot] using
    fixedRootCertificate_of_namedJustifiedRunBlock S hDrun hDjust hH

/-- A record lock at a height was written by an earlier tick of the same
validator, whose attestation carried that finality pair. Copied from the
`private` named induction in `RawHeightCoverageRun`, which has no consumer
outside that file. -/
private theorem fixedRootRecordLock_finalityEmission_before
    (S : Setup V) (rho : Run V) (v : V) :
    ∀ (n : Nat) {H : Height} {T : BlockId},
      (rho.stateBefore S n v).record.legacy.lock H = some T →
        ∃ (i : Nat), i < n ∧ ∃ (t : Time) (a : NamedAttestation V),
          rho.events[i]? = some (Event.tick v t) ∧
            Object.attest a ∈ (on_tick_emit S v
              (rho.stateBefore S i v) t).2 ∧
            a.finality_pair = some ⟨H, T⟩ := by
  intro n
  induction n with
  | zero =>
      intro H T hlock
      exact absurd hlock (by
        simp [Run.stateBefore, NamedRun.stateBefore, NamedWorld.init,
          NamedNode.initial, Protocol.NamedRecord.initial, Protocol.Record.initial])
  | succ n ih =>
      intro H T hlock
      change (NamedRun.stateBefore S rho (n + 1) v).record.legacy.lock H =
        some T at hlock
      cases hpre : (rho.stateBefore S n v).record.legacy.lock H with
      | some X =>
          have hmono :
              (rho.stateBefore S (n + 1) v).record.legacy.lock H = some X :=
            stateBefore_lock_mono S rho v (n + 1) (Nat.le_succ n) hpre
          have hXT : X = T := by
            rw [hlock] at hmono
            exact (Option.some.inj hmono).symm
          subst X
          obtain ⟨i, hi, t, a, hevent, hemitted, hpair⟩ := ih hpre
          exact ⟨i, Nat.lt_succ_of_lt hi, t, a, hevent, hemitted, hpair⟩
      | none =>
          change (NamedRun.stateBefore S rho n v).record.legacy.lock H =
            none at hpre
          have hstep := congrFun (Proofs.NamedRuntime.stateBefore_succ S rho n) v
          cases hevent : rho.events[n]? with
          | none =>
              rw [hstep, hevent] at hlock
              simp only [Option.toList, List.foldl_nil] at hlock
              exact absurd hlock (by rw [hpre]; simp)
          | some e =>
              cases e with
              | tick u t =>
                  by_cases huv : u = v
                  · subst u
                    have hpost :
                        (on_tick_emit S v
                          (rho.stateBefore S n v) t).1.record.legacy.lock H =
                            some T := by
                      rw [← stateBefore_succ_record S rho hevent]
                      exact hlock
                    obtain ⟨a, hemitted, hpair⟩ :=
                      Protocol.on_tick_emit_lock_introduced
                        S v (rho.stateBefore S n v) t hpre hpost
                    exact ⟨n, Nat.lt_succ_self n, t, a, hevent,
                      hemitted, hpair⟩
                  · rw [hstep, hevent] at hlock
                    simp only [Option.toList, List.foldl_cons,
                      List.foldl_nil, NamedWorld.step,
                      Function.update_of_ne (Ne.symm huv)] at hlock
                    exact absurd hlock (by rw [hpre]; simp)
              | deliver u o t =>
                  by_cases huv : u = v
                  · subst u
                    rw [hstep, hevent] at hlock
                    simp only [Option.toList, List.foldl_cons,
                      List.foldl_nil, NamedWorld.step,
                      Function.update_self] at hlock
                    change (NamedNode.process S
                      (NamedRun.stateBefore S rho n v) o).Λ.legacy.lock H =
                        some T at hlock
                    rw [process_record] at hlock
                    exact absurd hlock (by rw [hpre]; simp)
                  · rw [hstep, hevent] at hlock
                    simp only [Option.toList, List.foldl_cons,
                      List.foldl_nil, NamedWorld.step,
                      Function.update_of_ne (Ne.symm huv)] at hlock
                    exact absurd hlock (by rw [hpre]; simp)

/-- earlier's `actionOwnLock_at_fixedHeight_none_or_target` over named blocks: at
the unique fixed predecessor height an honest action's effective lock is either
absent or names the fixed target. Every lock at that height is backed by a
certificate, and the fixed-root record has only one certificate there. -/
private theorem fixedRootActionOwnLock_at_fixedHeight_none_or_target
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {M : Height} {u : V} {read : Time}
    (hfix : FixedHeightJustificationRootAtRead S rho M u read)
    {v : V} (hv : v ∈ rho.honest) (r : Round) :
    Protocol.own_lock (actionReadAt S rho v r).record.legacy (M - 1)
        (actionAttestationAt S rho v r).finality_pair = none ∨
      Protocol.own_lock (actionReadAt S rho v r).record.legacy (M - 1)
        (actionAttestationAt S rho v r).finality_pair =
          some (rho.storeBeforeTime S u read).J.root := by
  have hHne : M - 1 ≠ 0 := Nat.ne_of_gt hfix.targetHeightPositive
  have hcertOfRecordLock : ∀ {T : BlockId},
      (actionReadAt S rho v r).record.legacy.lock (M - 1) = some T →
        Certificate S rho (M - 1) T := by
    intro T hlock
    obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore
      S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed (S.a r)
    have hlockN :
        (rho.stateBefore S n v).record.legacy.lock (M - 1) = some T := by
      rw [← congrFun hn v]
      simpa only [actionReadAt, NamedActionReads.actionReadAt,
        NamedActionReads.actionReadFrom,
        NamedActionReads.confirmationReadFrom,
        NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using hlock
    obtain ⟨i, hi, t, a, hevent, hemitted, hpair⟩ :=
      fixedRootRecordLock_finalityEmission_before S rho v n hlockN
    have hemit : rho.emits S v (Object.attest a) t := ⟨i, hevent, hemitted⟩
    have hshape := Proofs.Optimistic.emits_attest_shape S hemit
    have haeq : a = actionAttestationAt S rho v a.round := by
      have hemit' : rho.emits S v (Object.attest a) (S.a a.round) := by
        rw [← hshape.2]
        exact hemit
      exact (NamedActionSources.action_run_emission S rho
        adm.toNamedAdmissibleCore.toNamedScheduleWellFormed
        v a.round a).mp hemit' |>.2.2
    refine fixedRootActionFinalityPair_certificate S adm hv a.round hHne ?_
    rw [← haeq]
    exact hpair
  cases hlock : Protocol.own_lock (actionReadAt S rho v r).record.legacy
      (M - 1) (actionAttestationAt S rho v r).finality_pair with
  | none => exact Or.inl rfl
  | some locked =>
      refine Or.inr ?_
      have hcert : Certificate S rho (M - 1) locked := by
        cases hfp : (actionAttestationAt S rho v r).finality_pair with
        | none =>
            refine hcertOfRecordLock ?_
            simpa only [Protocol.own_lock, hfp] using hlock
        | some p =>
            rcases p with ⟨h, target⟩
            by_cases hh : h = M - 1
            · subst h
              have htarget : target = locked := by
                simpa [Protocol.own_lock, hfp] using hlock
              subst target
              exact fixedRootActionFinalityPair_certificate S adm hv r hHne hfp
            · refine hcertOfRecordLock ?_
              simpa only [Protocol.own_lock, hfp, hh] using hlock
      rw [hfix.fixedTarget.uniqueAtHeight locked hcert]

/-- The honest action row at a window round, from the round's own height-pair
source alone. The lock side is discharged outright by the fixed-height own-lock
above, so the only input left is that the source sits at the fixed predecessor
height and names the fixed target. -/
theorem fixedRootWindowRows_of_source
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {M : Height} {u : V} {read : Time}
    (hfix : FixedHeightJustificationRootAtRead S rho M u read)
    {v : V} (hv : v ∈ rho.honest) {q0 : Round} {Q : Block V}
    (hsource : nodeFGSource S (actionReadAt S rho v q0) q0 = some Q)
    (hheight : ((actionReadAt S rho v q0).st.core.toHealing.σ Q).h = M - 1)
    (htarget : ((actionReadAt S rho v q0).st.core.toHealing.σ Q).T_h.root =
      (rho.storeBeforeTime S u read).J.root) :
    (actionAttestationAt S rho v q0).height_pair =
        NamedHeightPair.vote (M - 1)
          (rho.storeBeforeTime S u read).J.root false ∨
      (actionAttestationAt S rho v q0).height_pair =
        NamedHeightPair.vote (M - 1)
          (rho.storeBeforeTime S u read).J.root true := by
  have hround : S.hc.round_of
      (actionReadAt S rho v q0).st.core.toHealing.s = q0 := by
    simpa only [actionStoreAt, Protocol.Store.toHealing] using
      actionStoreAt_round S rho v q0
  have hsource' : actionSource
      (NamedProfile.gradeContract (actionReadAt S rho v q0).cache) S.E S.hc
      (actionReadAt S rho v q0).st.core.toHealing = some Q := by
    simpa only [actionSource, hround, nodeFGSource] using hsource
  have hown := fixedRootActionOwnLock_at_fixedHeight_none_or_target
    S adm hfix hv q0
  have hlock : Protocol.own_lock (actionReadAt S rho v q0).record.legacy
        ((actionReadAt S rho v q0).st.core.toHealing.σ Q).h
        (Protocol.NamedActions.round_action_with
          (NamedProfile.gradeContract (actionReadAt S rho v q0).cache) S.E S.hc
          (S.node v) (actionReadAt S rho v q0).st.core.toHealing
          (actionReadAt S rho v q0).record).2.finality_pair = none ∨
      Protocol.own_lock (actionReadAt S rho v q0).record.legacy
        ((actionReadAt S rho v q0).st.core.toHealing.σ Q).h
        (Protocol.NamedActions.round_action_with
          (NamedProfile.gradeContract (actionReadAt S rho v q0).cache) S.E S.hc
          (S.node v) (actionReadAt S rho v q0).st.core.toHealing
          (actionReadAt S rho v q0).record).2.finality_pair =
          some ((actionReadAt S rho v q0).st.core.toHealing.σ Q).T_h.root := by
    rw [hheight, htarget]
    rcases hown with h | h
    · exact Or.inl (by
        simpa only [actionAttestationAt,
          Protocol.NamedDuties.attest_with] using h)
    · exact Or.inr (by
        simpa only [actionAttestationAt,
          Protocol.NamedDuties.attest_with] using h)
  have hpairs :=
    round_action_height_pair_target_or_timeout_of_source_lock_none_or_aligned
      (NamedProfile.gradeContract (actionReadAt S rho v q0).cache) S.E S.hc
      (S.node v) (actionReadAt S rho v q0).st.core.toHealing
      (actionReadAt S rho v q0).record hsource' hlock
  rw [hheight, htarget] at hpairs
  simpa only [actionAttestationAt, Protocol.NamedDuties.attest_with] using hpairs

/-! ## Fresh rows at the later action round -/

/- The source body is obtained from the named action-source witness. This is
   kept local because the source-height split below needs the named run block
   to transport the persisted grade to the exact source. -/
private theorem fixedRootFresh_actionBody_runBlock
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) {r : Round} {D : NamedBlock V}
    (hD : D ∈ (actionReadAt S rho v r).st.bodies) : RunBlock S rho D := by
  have hDpre : D ∈ (rho.storeBeforeTime S v (S.a r)).bodies := by
    simpa only [actionStoreAt, actionReadAt, NamedActionReads.actionReadAt,
      NamedActionReads.actionReadFrom, NamedActionReads.confirmationReadFrom,
      NamedActionReads.preparedCache, NamedRun.stateBeforeTime] using hD
  exact fixedRootRunBlock_of_body_at_read S adm hv hDpre

private theorem fixedRootFresh_namedSource_witness
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) {r : Round} {Q : Block V}
    (hsource : nodeFGSource S (actionReadAt S rho v r) r = some Q) :
    ∃ D : NamedBlock V,
      D ∈ (actionReadAt S rho v r).st.bodies ∧
      D.erase = Q ∧
      RunBlock S rho D ∧
      (actionReadAt S rho v r).st.core.toHealing.σ Q =
        Protocol.derive_named S.E S.cfg D := by
  have hround : S.hc.round_of
      (actionReadAt S rho v r).st.core.toHealing.s = r := by
    simpa only [actionStoreAt, Protocol.Store.toHealing] using
      actionStoreAt_round S rho v r
  have hsource' : actionFGSource S (actionReadAt S rho v r) = some Q := by
    have hsource0 := hsource
    simp only [PhaseGrades.nodeFGSource] at hsource0
    simpa only [actionFGSource, hround] using hsource0
  obtain ⟨D, hDbody, hDerase, hσ, -⟩ :=
    NamedActionSources.action_witness S rho v r Q hsource'
  have hDrun := fixedRootFresh_actionBody_runBlock S adm hv hDbody
  refine ⟨D, hDbody, hDerase, hDrun, ?_⟩
  change (actionReadAt S rho v r).st.core.σ Q =
    Protocol.derive_named S.E S.cfg D
  exact hσ

/-- Fresh action rows at a fixed-root round. The source can differ from the
opening block, but the persisted opening grade puts the opening block below
that source. The caller supplies the local no-rise source-height cap; the
fixed-root lock then discharges the record-lock side of the height-pair codec.
No carried-row or `eta_SG` premise is used. -/
theorem fixedRootFreshActionRows_of_persistedGrade
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {M : Height} {u : V} {read : Time}
    (hfix : FixedHeightJustificationRootAtRead S rho M u read)
    {r : Round} {B0 : NamedBlock V}
    (hr : 0 < r)
    (hhor : S.a r ≤ rho.horizon)
    (hB0run : RunBlock S rho B0)
    (hB0height : (Protocol.derive_named S.E S.cfg B0).h = M - 1)
    (hB0entry : (Protocol.derive_named S.E S.cfg B0).T_h.root =
      (rho.storeBeforeTime S u read).J.root)
    (hforms : NamedGradeFormsAt S rho r B0.erase)
    (hwindow : ∀ v ∈ rho.honest,
      FinalityFilterRetainedAtRead S rho v (S.a r) B0.erase)
    (hsourceUpper : ∀ v ∈ rho.honest, ∀ Q : Block V,
      nodeFGSource S (actionReadAt S rho v r) r = some Q →
      ((actionReadAt S rho v r).st.core.toHealing.σ Q).h ≤ M - 1) :
    ∀ v ∈ rho.honest,
      (actionAttestationAt S rho v r).height_pair =
          NamedHeightPair.vote (M - 1)
            (rho.storeBeforeTime S u read).J.root false ∨
        (actionAttestationAt S rho v r).height_pair =
          NamedHeightPair.vote (M - 1)
            (rho.storeBeforeTime S u read).J.root true := by
  intro v hv
  have hactive : B0.erase ∈
      PhaseGrades.filteredTree (actionReadAt S rho v r) :=
    namedGradeFormsAt_actionStore_of_window S hforms hv (hwindow v hv)
  obtain ⟨Q, hsource⟩ := exists_actionFGSource_of_namedGradeFormsAt
    S adm.toNamedAdmissibleCore hr hhor hforms hv hactive
  obtain ⟨Qn, hQnbody, hQnerase, hQnrun, hσ⟩ :=
    fixedRootFresh_namedSource_witness S adm hv hsource
  have hB0Q : Block.Preceq B0.erase Q :=
    namedGradeFormsAt_preceq_actionSource S adm.toNamedAdmissibleCore
      hr hhor hforms hv hactive hsource
  have hB0QnErase : Block.Preceq B0.erase Qn.erase := by
    rw [hQnerase]
    exact hB0Q
  obtain ⟨A, hAQn, hAerased⟩ :=
    Proofs.NamedAncestry.erased_ancestor_lift Qn hB0QnErase
  have hArun : RunBlock S rho A :=
    Proofs.NamedRuntime.blockInRun_of_ancestor S rho hQnrun hAQn
  have hroot : A.root = B0.root := by
    rw [← Proofs.NamedWire.erase_root A, hAerased, Proofs.NamedWire.erase_root]
  have hAB0 : A = B0 :=
    adm.toNamedRootCollisionFree.root_injective A B0 hArun hB0run A B0
      (Or.inl (Proofs.NamedAncestry.named_self A))
      (Or.inr (Proofs.NamedAncestry.named_self B0)) hroot
  have hB0Qn : NamedBlock.Preceq B0 Qn := by
    simpa only [hAB0] using hAQn
  have hQnUpper : (Protocol.derive_named S.E S.cfg Qn).h ≤ M - 1 := by
    have h := hsourceUpper v hv Q hsource
    rw [hσ] at h
    exact h
  have hQnLower : M - 1 ≤
      (Protocol.derive_named S.E S.cfg Qn).h := by
    have h := Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hB0Qn
    rw [hB0height] at h
    exact h
  have hQnheight : (Protocol.derive_named S.E S.cfg Qn).h = M - 1 :=
    Nat.le_antisymm hQnUpper hQnLower
  have hsameHeight : (Protocol.derive_named S.E S.cfg B0).h =
      (Protocol.derive_named S.E S.cfg Qn).h := by
    rw [hB0height, hQnheight]
  have hentry : (Protocol.derive_named S.E S.cfg B0).T_h =
      (Protocol.derive_named S.E S.cfg Qn).T_h :=
    Proofs.NamedEntryHeight.entry_eq_on_plateau S.E S.cfg hB0Qn hsameHeight
  have hsourceHeight :
      ((actionReadAt S rho v r).st.core.toHealing.σ Q).h = M - 1 := by
    rw [hσ, hQnheight]
  have hsourceEntry :
      ((actionReadAt S rho v r).st.core.toHealing.σ Q).T_h.root =
        (rho.storeBeforeTime S u read).J.root := by
    calc
      ((actionReadAt S rho v r).st.core.toHealing.σ Q).T_h.root =
          (Protocol.derive_named S.E S.cfg Qn).T_h.root :=
        congrArg (fun x : Protocol.ChainState V => x.T_h.root) hσ
      _ = (Protocol.derive_named S.E S.cfg B0).T_h.root :=
        congrArg (fun x : Block V => x.root) hentry.symm
      _ = (rho.storeBeforeTime S u read).J.root := hB0entry
  have hrows := fixedRootWindowRows_of_source S adm hfix hv hsource
    hsourceHeight hsourceEntry
  exact hrows

private theorem fixedRootFresh_inWindow_at_pred
    (S : Setup V) (rho : Run V) (q : Round) :
    Protocol.ProposalRows.inWindow S.hc
      (proposerReadAt S rho (S.hc.opening_slot q)).st.core (q - 1) = true := by
  have hslot :
      (proposerReadAt S rho (S.hc.opening_slot q)).st.core.s =
        S.hc.opening_slot q := by
    simpa only [proposerReadAt, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using
      Proofs.Optimistic.slotOf_proposal_time S.E (S.hc.opening_slot q)
  have hround : S.hc.round_of
      (proposerReadAt S rho (S.hc.opening_slot q)).st.core.s = q := by
    rw [hslot]
    exact round_of_opening_slot_eq S.hc q
  unfold Protocol.ProposalRows.inWindow
  rw [hround]
  simp only [decide_eq_true_eq]
  have heta : 1 ≤ S.hc.η_SG := S.hc.η_SG_ge_one
  exact ⟨Nat.sub_le_sub_left heta q, Nat.sub_le q 1⟩

omit [Fintype V] in
private theorem fixedRootFresh_parent_preceq_self (B : NamedBlock V) :
    NamedBlock.Preceq B.parent B := by
  cases B with
  | genesis => exact Proofs.NamedAncestry.named_self _
  | node parent slot root votes support rows proposer =>
      exact Proofs.NamedAncestry.named_extend slot root votes support rows proposer
        (Proofs.NamedAncestry.named_self parent)

omit [DecidableEq V] [Fintype V] in
private theorem fixedRootFresh_heightCases_nat {a m : Nat} (hlo : m - 1 ≤ a)
    (hhi : a ≤ m) : a = m - 1 ∨ a = m := by
  omega

set_option maxHeartbeats 400000 in
/-- The fixed-root predecessor promotion using fresh rows from the immediately
preceding action. The source-height cap is local to the still-predecessor
parent branch; it is not a public premise. -/
private theorem fixedRootFresh_predLifecycle_promotion_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {M : Height} {u : V} {read : Time}
    (hfix : FixedHeightJustificationRootAtRead S rho M u read)
    {q' : Round} {C B2 : NamedBlock V}
    (hq' : 0 < q')
    (hq'PredPos : 0 < q' - 1)
    (hCrun : RunBlock S rho C)
    (hCheight : (Protocol.derive_named S.E S.cfg C).h = M - 1)
    (hCtarget : (Protocol.derive_named S.E S.cfg C).T_h.root =
      (rho.storeBeforeTime S u read).J.root)
    (hCP : NamedBlock.Preceq C B2.parent)
    (hsourceToParent : ∀ v ∈ rho.honest, ∀ Q : Block V,
      nodeFGSource S (actionReadAt S rho v (q' - 1)) (q' - 1) = some Q →
      ((actionReadAt S rho v (q' - 1)).st.core.toHealing.σ Q).h ≤
        (Protocol.derive_named S.E S.cfg B2.parent).h)
    (hforms : NamedGradeFormsAt S rho (q' - 1) C.erase)
    (hwindow : ∀ v ∈ rho.honest,
      FinalityFilterRetainedAtRead S rho v (S.a (q' - 1)) C.erase)
    (hpacket : NamedSGProposalLifecyclePacket S rho (q' - 1)
      (S.hc.opening_slot q' - 1) B2)
    (hmature : ProposalTimeoutMatureAt S rho (S.hc.opening_slot q'))
    (hpost : S.E.t_GST ≤ S.a (q' - 1)) :
    (Protocol.derive_named S.E S.cfg B2).h = M ∨
      M < honestHMaxAt S rho
        (Protocol.proposal_time S.E (S.hc.opening_slot q')) := by
  have hq'Pred : q' - 1 + 1 = q' := Nat.sub_add_cancel hq'
  have hlifecycle : NamedRawOpeningLifecycleAt S rho q' B2 := by
    simpa only [hq'Pred] using hpacket.lifecycle
  have hB2 : proposedBlockAt S rho (S.hc.opening_slot q') = some B2 :=
    hlifecycle.proposal
  have hprop : S.E.proposer (S.hc.opening_slot q') ∈ rho.honest :=
    hlifecycle.proposerHonest
  have hproposalHor : Protocol.proposal_time S.E
      (S.hc.opening_slot q') ≤ rho.horizon :=
    hlifecycle.proposalInHorizon
  have hspos : 0 < S.hc.opening_slot q' := by
    unfold Protocol.HealConfig.opening_slot
    exact Nat.mul_pos hq' (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
  by_cases hrise : M < honestHMaxAt S rho
      (Protocol.proposal_time S.E (S.hc.opening_slot q'))
  · exact Or.inr hrise
  · left
    have hpublicCap : honestHMaxAt S rho
        (Protocol.proposal_time S.E (S.hc.opening_slot q')) ≤ M :=
      Nat.le_of_not_gt hrise
    have hproposalUpper :
        (Protocol.derive_named S.E S.cfg B2).h ≤ M :=
      (honestProposedBlock_height_le_honestHMaxAt
        S adm hspos hprop hproposalHor hB2).trans hpublicCap
    have hparentLower : M - 1 ≤
        (Protocol.derive_named S.E S.cfg B2.parent).h := by
      rw [← hCheight]
      exact Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hCP
    have hparentUpper :
        (Protocol.derive_named S.E S.cfg B2.parent).h ≤ M :=
      (Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg
        (fixedRootFresh_parent_preceq_self B2)).trans hproposalUpper
    have hparentCases :
        (Protocol.derive_named S.E S.cfg B2.parent).h = M - 1 ∨
        (Protocol.derive_named S.E S.cfg B2.parent).h = M := by
      exact fixedRootFresh_heightCases_nat hparentLower hparentUpper
    rcases hparentCases with hparentPred | hparentExact
    · have hparentTarget :
          (Protocol.derive_named S.E S.cfg B2.parent).T_h.root =
            (Protocol.derive_named S.E S.cfg C).T_h.root := by
        rw [← Proofs.NamedEntryHeight.entry_eq_on_plateau S.E S.cfg hCP
          (by rw [hCheight, hparentPred])]
      have hdelay : S.a (q' - 1) + S.E.Δ ≤
          Protocol.proposal_time S.E (S.hc.opening_slot q') := by
        exact action_add_delta_le_openingProposal_of_round_lt S
          (Nat.sub_lt hq' (by decide))
      have hsourceUpper : ∀ v ∈ rho.honest, ∀ Q : Block V,
          nodeFGSource S (actionReadAt S rho v (q' - 1)) (q' - 1) = some Q →
          ((actionReadAt S rho v (q' - 1)).st.core.toHealing.σ Q).h ≤ M - 1 := by
        intro v hv Q hsource
        have h := hsourceToParent v hv Q hsource
        simpa only [hparentPred] using h
      have hhor : S.a (q' - 1) ≤ rho.horizon := by
        exact (Int.le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)).trans
          (hdelay.trans hproposalHor)
      have hrowsFixed := fixedRootFreshActionRows_of_persistedGrade
        S adm hfix hq'PredPos hhor hCrun hCheight hCtarget hforms hwindow
          hsourceUpper
      have hrows : ∀ v ∈ rho.honest,
          (actionAttestationAt S rho v (q' - 1)).height_pair =
              NamedHeightPair.vote (M - 1)
                (Protocol.derive_named S.E S.cfg C).T_h.root false ∨
            (actionAttestationAt S rho v (q' - 1)).height_pair =
              NamedHeightPair.vote (M - 1)
                (Protocol.derive_named S.E S.cfg C).T_h.root true := by
        intro v hv
        rw [hCtarget]
        exact hrowsFixed v hv
      have hcoverage : NamedTargetedHonestActionProposalCoverageAt
          S rho (q' - 1) B2 (M - 1)
            (Protocol.derive_named S.E S.cfg C).T_h.root := by
        intro v hv
        have hpair := hrows v hv
        refine ⟨?_, hpair⟩
        exact actionAttestationAt_coveredAtProposal
          S adm hforms hCrun hCheight rfl hB2 hCP hparentPred
            hprop hproposalHor hpost hdelay hv (hwindow v hv)
            (fixedRootFresh_inWindow_at_pred S rho q') hpair
      have hheight := named_proposedBlock_height_eq_succ_of_actionCoverage
        S hfb hB2 hmature hcoverage hparentPred hparentTarget
      have hMone : 1 ≤ M :=
        Nat.le_of_lt (Nat.sub_pos_iff_lt.mp hfix.targetHeightPositive)
      rw [Nat.sub_add_cancel hMone] at hheight
      exact hheight
    · exact Nat.le_antisymm hproposalUpper
        (by
          rw [← hparentExact]
          exact Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg
            (fixedRootFresh_parent_preceq_self B2))

#print axioms fixedRootFreshActionRows_of_persistedGrade


/-- earlier's `lifecycleAction_rows_at_pred` over named blocks. At a lifecycle
round the records fixes every honest reader's live confirmation to the round's
proposal, so the height-pair source is that proposal and no window-round source
question arises. The lock side is the restated own-lock; the only input left is
that the proposal's entry is the fixed target. -/
private theorem fixedRootLifecycleRows_at_pred
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {M : Height} {u : V} {read : Time}
    (hfix : FixedHeightJustificationRootAtRead S rho M u read)
    {q1 : Round} (hq1 : 0 < q1) (hhor : S.a q1 ≤ rho.horizon)
    {C B1 : NamedBlock V}
    (hformsJ : NamedGradeFormsAt S rho q1 C.erase)
    (hactiveJ : ∀ v ∈ rho.honest,
      C.erase ∈ PhaseGrades.filteredTree (actionReadAt S rho v q1))
    (hpacket : NamedSGProposalLifecyclePacket S rho (q1 - 1)
      (S.hc.opening_slot q1 - 1) B1)
    (hB1height : (Protocol.derive_named S.E S.cfg B1).h = M - 1)
    (hB1entry : (Protocol.derive_named S.E S.cfg B1).T_h.root =
      (rho.storeBeforeTime S u read).J.root) :
    ∀ v ∈ rho.honest,
      (actionAttestationAt S rho v q1).height_pair =
          NamedHeightPair.vote (M - 1)
            (rho.storeBeforeTime S u read).J.root false ∨
        (actionAttestationAt S rho v q1).height_pair =
          NamedHeightPair.vote (M - 1)
            (rho.storeBeforeTime S u read).J.root true := by
  intro v hv
  have hq1PredAdd : q1 - 1 + 1 = q1 := Nat.sub_add_cancel hq1
  have hlifecycle : NamedRawOpeningLifecycleAt S rho q1 B1 := by
    simpa only [hq1PredAdd] using hpacket.lifecycle
  obtain ⟨Q2, hQ2, -⟩ := namedGradeFormsAt_preceq_actionQ2 S
    adm.toNamedAdmissibleCore hq1 hhor hformsJ hv (hactiveJ v hv)
  have hsource := seedLifecycleAction_fgSource_eq_block_of_selected S hq1 hv hQ2
    (namedG1At_of_nodeQ2 S adm hq1 hhor v hv Q2 hQ2) hpacket
  have hinv : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg
      (actionReadAt S rho v q1).st := by
    apply Proofs.NamedConfirmationMembership.invariant_update
    exact Proofs.NamedConfirmationMembership.invariant_clock S.E S.cfg _ (S.a q1)
      (Proofs.NamedRuntime.stateBeforeTime_invariants S rho (S.a q1) v).1
  have hcoh := hinv.1.1
  have hLive : (actionReadAt S rho v q1).st.core.live_confirmed = B1.erase :=
    hlifecycle.liveConfirmed v hv
  have hB1mem : B1.erase ∈ (actionReadAt S rho v q1).st.core.T := by
    rw [← hLive]
    exact hinv.2.1
  have hB1image := hB1mem
  rw [hcoh.1] at hB1image
  obtain ⟨D, hD, hDerase⟩ := Finset.mem_image.mp hB1image
  have hDeq : D = B1 :=
    fixedRootNamed_run_eq_of_erase adm
      (fixedRootRunBlock_of_body_at_read S adm hv (read := S.a q1) (by
        simpa only [actionReadAt, NamedActionReads.actionReadAt,
          NamedActionReads.actionReadFrom,
          NamedActionReads.confirmationReadFrom,
          NamedActionReads.preparedCache, Run.storeBeforeTime] using hD))
      hlifecycle.runBlock hDerase
  have hsigma : (actionReadAt S rho v q1).st.core.σ B1.erase =
      Protocol.derive_named S.E S.cfg B1 := by
    have h := hcoh.2.2.2.2 D hD
    rw [hDeq] at h
    exact h
  refine fixedRootWindowRows_of_source S adm hfix hv hsource ?_ ?_
  · show ((actionReadAt S rho v q1).st.core.σ B1.erase).h = M - 1
    rw [hsigma]
    exact hB1height
  · show ((actionReadAt S rho v q1).st.core.σ B1.erase).T_h.root =
      (rho.storeBeforeTime S u read).J.root
    rw [hsigma]
    exact hB1entry

/-! ## The restated fixed-root height-progress route -/

/-- Starting from a P-free fixed-height justification root, the two Claim-4
lifecycles and the Route-B predecessor promotion force a numeric rise. This
is earlier's `heightProgress_from_fixedRoot` with the bounded lifecycle and three
helpers pinned. -/
theorem fixedRootProgress_of_lifecycle
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {gap : Round}
    (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra)
    (_of_lifecycle : ∀ {H : Height} {w : V} {read0 : Time} {base : Round},
      FixedHeightJustificationRootAtRead S rho H w read0 →
      S.E.t_GST ≤ read0 →
      read0 ≤ S.a base →
      S.a (base + 4 + gap) ≤ rho.horizon →
      H < honestHMaxAt S rho (S.a (base + 4 + gap)) ∨
        ∃ q, base + 3 ≤ q ∧ q ≤ base + 3 + gap ∧
          ProposerCarrierAt S rho q ∧
            NamedGradeFormsAt S rho (q - 1) (rho.storeBeforeTime S w read0).J ∧
              SGTargetOpeningConeRootLock S rho H (q - 1)
                (S.hc.opening_slot q - 1) ∧
                ∃ P : NamedBlock V,
                  proposedBlockAt S rho (S.hc.opening_slot q) = some P ∧
                  NamedSGProposalLifecyclePacket S rho (q - 1)
                    (S.hc.opening_slot q - 1) P)
    (_of_sourceToParent : ∀ {H : Height} {w : V} {read0 : Time}
      {r endpointRound q1 q' : Round} {B1 B2 : NamedBlock V},
      FixedHeightJustificationRootAtRead S rho H w read0 →
      S.E.t_GST ≤ read0 →
      read0 ≤ S.a r →
      r + 3 ≤ q1 →
      read0 ≤ S.a q1 →
      0 < q1 → q1 < q' →
      q' ≤ endpointRound →
      ProposerCarrierAt S rho q1 →
      S.E.t_GST ≤ S.a q1 →
      S.a endpointRound ≤ rho.horizon →
      honestHMaxAt S rho (S.a endpointRound) ≤ H →
      (∃ Bplus : NamedBlock V,
        proposedBlockAt S rho (S.hc.opening_slot q1 + 2) = some Bplus ∧
        RunBlock S rho Bplus ∧
        S.E.proposer (S.hc.opening_slot q1 + 2) ∈ rho.honest ∧
        Protocol.proposal_time S.E (S.hc.opening_slot q1 + 2) ≤ rho.horizon ∧
        Protocol.get_fg_root
            (rho.storeBeforeTime S
              (S.E.proposer (S.hc.opening_slot q1 + 2))
              (Protocol.proposal_time S.E
                (S.hc.opening_slot q1 + 2))).toHealing.toFG =
          (rho.storeBeforeTime S w read0).J ∧
        (rho.storeBeforeTime S
          (S.E.proposer (S.hc.opening_slot q1 + 2))
          (Protocol.proposal_time S.E
            (S.hc.opening_slot q1 + 2))).h_max = H) →
      NamedSGProposalLifecyclePacket S rho (q1 - 1)
        (S.hc.opening_slot q1 - 1) B1 →
      NamedSGProposalLifecyclePacket S rho (q' - 1)
        (S.hc.opening_slot q' - 1) B2 →
      (Protocol.derive_named S.E S.cfg B1).h = H - 1 →
      SGTargetOpeningConeRootLock S rho H (q1 - 1)
        (S.hc.opening_slot q1 - 1) →
      SGTargetOpeningConeRootLock S rho H (q' - 1)
        (S.hc.opening_slot q' - 1) →
      (∀ {k : Round}, r + 1 ≤ k → k ≤ endpointRound →
        ∀ v ∈ rho.honest,
          Protocol.get_fg_root
              (rho.storeBeforeTime S v (S.a k)).toHealing.toFG =
            (rho.storeBeforeTime S w read0).J ∧
          (rho.storeBeforeTime S v (S.a k)).h_max = H) →
      Protocol.get_fg_root
          (Protocol.proposerDutyStore S rho
            (S.hc.opening_slot q')).toHealing.toFG =
        (rho.storeBeforeTime S w read0).J →
      (Protocol.proposerDutyStore S rho
          (S.hc.opening_slot q')).h_max = H →
      NamedGradeFormsAt S rho (q' - 1) B1.erase →
      (∀ v ∈ rho.honest,
        B1.erase ∈ PhaseGrades.filteredTree
          (actionReadAt S rho v (q' - 1))) →
      Block.Preceq B1.erase B2.parent.erase →
      ProposalTimeoutMatureAt S rho (S.hc.opening_slot q') →
      q1 + 2 + delayExtra ≤ q' →
      ∀ v ∈ rho.honest, ∀ Q : Block V,
        nodeFGSource S (actionReadAt S rho v (q' - 1)) (q' - 1) = some Q →
        ((actionReadAt S rho v (q' - 1)).st.core.toHealing.σ Q).h ≤
          (Protocol.derive_named S.E S.cfg B2.parent).h)
    :
    ∀ {M : Height} {u : V} {read : Time}
      {r endpointRound : Round},
      FixedHeightJustificationRootAtRead S rho M u read →
      S.E.t_GST ≤ read → read ≤ S.a r →
      r + 3 * gap + 8 + 2 * delayExtra ≤ endpointRound →
      S.a endpointRound ≤ rho.horizon →
      honestHMaxAt S rho (S.a endpointRound) ≤ M →
      M < honestHMaxAt S rho (S.a endpointRound) := by
  intro M u read r endpointRound hfix hpost hreadAction hbound hendHor hcapEnd
  have hsb : SlashableBound S rho :=
    slashableBound_of_admissible_belowOneThird S adm hfb
  have hmajority : HonestWeightMajority S rho.honest :=
    AlignedRoundLemmas.honestWeightMajority_of_belowOneThird (S := S) hfb
  obtain ⟨Jn, hJnErase, hJnRun, hJnHeight⟩ :=
    fixedRootJustificationRoot_target_named S hfix
  have hcapAt : ∀ {k : Round}, k ≤ endpointRound →
      honestHMaxAt S rho (S.a k) ≤ M := by
    intro k hk
    exact (honestHMaxAt_mono S adm.toNamedScheduleWellFormed
      (Assembly.a_mono S hk)).trans hcapEnd
  have hhorAt : ∀ {k : Round}, k ≤ endpointRound →
      S.a k ≤ rho.horizon := by
    intro k hk
    exact (Assembly.a_mono S hk).trans hendHor
  have hlift : ∀ {t : Time}, t ≤ S.a endpointRound →
      M < honestHMaxAt S rho t →
      M < honestHMaxAt S rho (S.a endpointRound) := by
    intro t ht hrise
    exact hrise.trans_le
      (honestHMaxAt_mono S adm.toNamedScheduleWellFormed ht)
  have hfixedAt : ∀ {k : Round}, r + 1 ≤ k → k ≤ endpointRound →
      ∀ v ∈ rho.honest,
        Protocol.get_fg_root
            (rho.storeBeforeTime S v (S.a k)).toHealing.toFG =
          (rho.storeBeforeTime S u read).J ∧
        (rho.storeBeforeTime S v (S.a k)).h_max = M := by
    intro k hrk hkend v hv
    have hdelayRead : read + S.E.Δ ≤ S.a k := by
      calc
        read + S.E.Δ ≤ S.a r + S.E.Δ :=
          Int.add_le_add_right hreadAction S.E.Δ
        _ ≤ S.hc.Γ_neg1 S.E.Δ (r + 1) :=
          action_add_delta_le_next_Γ_neg1 S r
        _ ≤ S.a (r + 1) := le_of_lt (next_Γ_neg1_lt_action S r)
        _ ≤ S.a k := Assembly.a_mono S hrk
    exact
      fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRise
        S adm hsb hfix hv hpost hdelayRead (hhorAt hkend) (hcapAt hkend)
  have htargetActiveAt : ∀ {k : Round}, r + 1 ≤ k → k ≤ endpointRound →
      ∀ v ∈ rho.honest,
        (rho.storeBeforeTime S u read).J ∈
          Protocol.get_filtered_block_tree
            (healStoreAt S rho v k).toFG := by
    intro k hrk hkend v hv
    change (rho.storeBeforeTime S u read).J ∈
      Protocol.get_filtered_block_tree
        (rho.storeBeforeTime S v (S.a k)).toHealing.toFG
    rw [← (hfixedAt hrk hkend v hv).1]
    simpa only [Run.storeBeforeTime] using
      named_fgRoot_mem_filtered_stateBeforeTime S rho (S.a k) v
  have hdomainActiveAt : ∀ {k : Round}, r + 1 ≤ k → k ≤ endpointRound →
      ∀ v ∈ rho.honest,
        (rho.storeBeforeTime S u read).J ∈
          PhaseGrades.filteredTree (relativeG2Read S rho k v) := by
    intro k hrk hkend v hv
    have hkpos : 0 < k := Nat.lt_of_lt_of_le (Nat.succ_pos r) hrk
    have hkPredAdd : k - 1 + 1 = k := Nat.sub_add_cancel hkpos
    have hrkPred : r ≤ k - 1 := fixedRootPred_le_nat hrk
    have hdomainAction : DecoupledConsensusModel.Protocol.domain S.E S.hc k .g2 ≤ S.a k :=
      FrameForward.domain_le_a S k .g2
    have hdomainEnd : DecoupledConsensusModel.Protocol.domain S.E S.hc k .g2 ≤ S.a endpointRound :=
      hdomainAction.trans (Assembly.a_mono S hkend)
    have hdomainHor : DecoupledConsensusModel.Protocol.domain S.E S.hc k .g2 ≤ rho.horizon :=
      hdomainEnd.trans hendHor
    have hdomainCap : honestHMaxAt S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc k .g2) ≤ M :=
      (honestHMaxAt_mono S adm.toNamedScheduleWellFormed hdomainEnd).trans
        hcapEnd
    have hnext := action_add_delta_le_next_Γ_neg1 S (k - 1)
    rw [gammaNeg1_eq_domain_g2_succ S (k - 1), hkPredAdd] at hnext
    have hdelayDomain : read + S.E.Δ ≤ DecoupledConsensusModel.Protocol.domain S.E S.hc k .g2 :=
      (Int.add_le_add_right
        (hreadAction.trans (Assembly.a_mono S hrkPred)) S.E.Δ).trans hnext
    have hroot :=
      (fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRise
        S adm hsb hfix hv hpost hdelayDomain hdomainHor hdomainCap).1
    change (rho.storeBeforeTime S u read).J ∈
      Protocol.get_filtered_block_tree
        (rho.storeBeforeTime S v
          (DecoupledConsensusModel.Protocol.domain S.E S.hc k .g2)).toHealing.toFG
    rw [← hroot]
    simpa only [Run.storeBeforeTime] using
      named_fgRoot_mem_filtered_stateBeforeTime S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc k .g2) v
  -- the fixed target carries a common named grade at every window round
  have hgradeAt : ∀ {k : Round}, r + 2 ≤ k → k ≤ endpointRound →
      NamedGradeFormsAt S rho k (rho.storeBeforeTime S u read).J := by
    intro k hrk hkend
    obtain ⟨hkpos, hrOneK, hrOneKPred, hrKPred⟩ := fixedRootWindow_nat hrk
    have hkPredAdd : k - 1 + 1 = k := Nat.sub_add_cancel hkpos
    have hkPredEnd : k - 1 ≤ endpointRound := (Nat.sub_le k 1).trans hkend
    have hfloor : ∀ v ∈ rho.honest,
        Block.Preceq (rho.storeBeforeTime S u read).J
          (Protocol.get_fg_root
            (actionStoreAt S rho v (k - 1)).toHealing.toFG) := by
      intro v hv
      rw [actionStoreAt_fgRoot_eq_storeBeforeTime S rho v (k - 1),
        (hfixedAt hrOneKPred hkPredEnd v hv).1]
      exact Block.preceq_self _
    have hpostPrev : S.E.t_GST ≤ S.a (k - 1) :=
      hpost.trans (hreadAction.trans (Assembly.a_mono S hrKPred))
    have hcut : S.hc.Γ_neg1 S.E.Δ (k - 1 + 1) ≤ rho.horizon :=
      (le_of_lt (next_Γ_neg1_lt_action S (k - 1))).trans
        (by simpa only [hkPredAdd] using hhorAt hkend)
    have hactive : ∀ v ∈ rho.honest,
        (rho.storeBeforeTime S u read).J ∈
          Protocol.get_filtered_block_tree
            (healStoreAt S rho v (k - 1 + 1)).toFG := by
      simpa only [hkPredAdd] using htargetActiveAt hrOneK hkend
    have hactiveDomain : ∀ v ∈ rho.honest,
        (rho.storeBeforeTime S u read).J ∈
          PhaseGrades.filteredTree
            (relativeG2Read S rho (k - 1 + 1) v) := by
      simpa only [hkPredAdd] using hdomainActiveAt hrOneK hkend
    simpa only [hkPredAdd] using
      namedGradeFormsAt_succ_of_fgRootFloor
        (P := (rho.storeBeforeTime S u read).J)
        (F := (rho.storeBeforeTime S u read).J)
        S adm hmajority hfloor hpostPrev hcut hactive hactiveDomain
  -- earlier's `fixedRoot_timeoutMature_of_exactLifecycleSeed`, reached through the
  -- prepared opening parent rather than the ungraded tick-store head
  have htimeoutAt : ∀ {entry q : Round} {B : NamedBlock V},
      NamedRawOpeningLifecycleAt S rho entry B →
      r ≤ entry →
      read ≤ S.a entry →
      S.E.t_GST ≤ S.a (entry + 1) →
      entry + 2 + delayExtra ≤ q →
      r + 3 ≤ q →
      q ≤ endpointRound →
      ProposerCarrierAt S rho q →
      Block.Preceq (rho.storeBeforeTime S u read).J B.erase →
      (Protocol.derive_named S.E S.cfg B).h = M →
      ProposalTimeoutMatureAt S rho (S.hc.opening_slot q) := by
    intro entry q B hlifecycle hrEntry hreadBase hpostNext hspace hqlo hqEnd
      hcarrier hJB hBheight
    obtain ⟨hq, hwindow, hprevLower, hentryLt, hprevAdd⟩ :=
      fixedRootSeedWindow_nat hspace
    obtain ⟨hrq, hlockGrade, hqPredPos⟩ := fixedRootLockRounds_nat hqlo
    have hqPredEnd : q - 1 ≤ endpointRound := (Nat.sub_le q 1).trans hqEnd
    have hthin : M - 1 ≤ (Protocol.derive_named S.E S.cfg B).h := by
      rw [hBheight]
      exact Nat.sub_le M 1
    have hfixedWindow : ∀ r', entry + 1 ≤ r' → r' ≤ q →
        ∀ v ∈ rho.honest,
          Protocol.get_fg_root
              (rho.storeBeforeTime S v (S.a r')).toHealing.toFG =
            (rho.storeBeforeTime S u read).J ∧
          (rho.storeBeforeTime S v (S.a r')).h_max = M := by
      intro r' hlo hhi
      exact hfixedAt ((Nat.succ_le_succ hrEntry).trans hlo) (hhi.trans hqEnd)
    obtain ⟨hformsAll, hwindowAction⟩ := gradeFormsAt_persist_of_fixedRoot_noRise
      S adm hfb hfix hlifecycle.gradeNext hlifecycle.runBlock hpost hreadBase
        hwindow (hhorAt hqEnd) (hcapAt hqEnd) hJB hthin hfixedWindow
    obtain ⟨_, hwindowPrev⟩ := gradeFormsAt_persist_of_fixedRoot_noRise
      S adm hfb hfix hlifecycle.gradeNext hlifecycle.runBlock hpost hreadBase
        hprevLower (hhorAt hqPredEnd) (hcapAt hqPredEnd) hJB hthin
        (fun r' hlo hhi => hfixedWindow r' hlo (hhi.trans (Nat.sub_le q 1)))
    have hformsPrev : NamedGradeFormsAt S rho (q - 1) B.erase :=
      hformsAll (q - 1) hprevLower (Nat.sub_le q 1)
    have hpostPrev : S.E.t_GST ≤ S.a (q - 1) :=
      hpostNext.trans (Assembly.a_mono S hprevLower)
    have hcut : S.hc.Γ_neg1 S.E.Δ q ≤ rho.horizon := by
      have hcutRaw : S.hc.Γ_neg1 S.E.Δ (q - 1 + 1) ≤ rho.horizon :=
        (le_of_lt (next_Γ_neg1_lt_action S (q - 1))).trans
          (by simpa only [hprevAdd] using hhorAt hqEnd)
      simpa only [hprevAdd] using hcutRaw
    have hactiveAction : ∀ w ∈ rho.honest,
        B.erase ∈ Protocol.get_filtered_block_tree
          (healStoreAt S rho w q).toFG := by
      intro w hw
      simpa only [FinalityFilterRetainedAtRead, healStoreAt] using
        hwindowAction w hw
    have hactionB : ∀ w ∈ rho.honest,
        B.erase ∈ PhaseGrades.filteredTree (actionReadAt S rho w (q - 1)) := by
      intro w hw
      refine activeAtAction_of_retainedAtRead S ?_
      simpa only [FinalityFilterRetainedAtRead, healStoreAt] using
        hwindowPrev w hw
    have hdomainAction : DecoupledConsensusModel.Protocol.domain S.E S.hc q .g2 ≤ S.a q :=
      FrameForward.domain_le_a S q .g2
    have hdomainHor : DecoupledConsensusModel.Protocol.domain S.E S.hc q .g2 ≤ rho.horizon :=
      hdomainAction.trans (hhorAt hqEnd)
    have hdomainCap : honestHMaxAt S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc q .g2) ≤ M :=
      (honestHMaxAt_mono S adm.toNamedScheduleWellFormed hdomainAction).trans
        (hcapAt hqEnd)
    have hdelayDomain : read + S.E.Δ ≤
        DecoupledConsensusModel.Protocol.domain S.E S.hc q .g2 :=
      (Int.add_le_add_right hreadBase S.E.Δ).trans
        ((NamedOutageClosure.action_delta_le_early S S.hc.R_ge_three
          hentryLt).trans (NamedOutageClosure.early_le_domain S q))
    have hdomainWindow : ∀ w ∈ rho.honest,
        FinalityFilterRetainedAtRead S rho w
          (DecoupledConsensusModel.Protocol.domain S.E S.hc q .g2) B.erase := by
      intro w hw
      have hmem := fixedRootGrade_mem_filteredTree_nextG2_of_noRise
        S adm hfb hfix hformsPrev hlifecycle.runBlock hJB hthin hpost
          (by simpa only [hprevAdd] using hdelayDomain)
          (by simpa only [hprevAdd] using hdomainHor)
          (by simpa only [hprevAdd] using hdomainCap) hw
      unfold FinalityFilterRetainedAtRead
      change B.erase ∈ Protocol.get_filtered_block_tree
        (NamedRun.stateBeforeTime S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc q .g2) w).st.core.toHealing.toFG
      simpa only [hprevAdd] using hmem
    -- the duty store at the opening keeps the fixed root and frontier
    have hproposalAction : Protocol.proposal_time S.E
        (S.hc.opening_slot q) ≤ S.a q := by
      rw [Setup.a, Protocol.a_eq_confirmation_time]
      exact Protocol.proposal_time_le_confirmation_time S.E _
    have hproposalHor : Protocol.proposal_time S.E
        (S.hc.opening_slot q) ≤ rho.horizon :=
      hproposalAction.trans (hhorAt hqEnd)
    have hproposalCap : honestHMaxAt S rho
        (Protocol.proposal_time S.E (S.hc.opening_slot q)) ≤ M :=
      (honestHMaxAt_mono S adm.toNamedScheduleWellFormed
        hproposalAction).trans (hcapAt hqEnd)
    have hproposalDelay : read + S.E.Δ ≤
        Protocol.proposal_time S.E (S.hc.opening_slot q) :=
      (Int.add_le_add_right hreadAction S.E.Δ).trans
        (action_add_delta_le_openingProposal_of_round_lt S hrq)
    -- the Claim-1 lock and the frame-native prepared opening parent
    obtain ⟨hpostCone, hlock⟩ := fixedRootConeRootLock_at_windowRound
      S adm hcom hfb hfix hpost hreadAction hqlo hqEnd hendHor hcapEnd
        (hgradeAt hlockGrade hqPredEnd)
    have hqTwo : 2 ≤ q :=
      (Nat.le_add_left 2 (r + 1)).trans (by
        simpa only [Nat.add_assoc] using hqlo)
    have hformsJ : NamedGradeFormsAt S rho (q - 1)
        (rho.storeBeforeTime S u read).J := hgradeAt hlockGrade hqPredEnd
    have hJPrevLower : r + 1 ≤ q - 1 :=
      (Nat.add_le_add_left (by decide : 1 ≤ 2) r).trans hlockGrade
    have hwindowJ : ∀ v ∈ rho.honest,
        FinalityFilterRetainedAtRead S rho v (S.a (q - 1))
          (rho.storeBeforeTime S u read).J := by
      intro v hv
      simpa only [FinalityFilterRetainedAtRead, healStoreAt] using
        htargetActiveAt hJPrevLower hqPredEnd v hv
    have hdomainWindowJ : ∀ v ∈ rho.honest,
        FinalityFilterRetainedAtRead S rho v
          (DecoupledConsensusModel.Protocol.domain S.E S.hc q .g2)
          (rho.storeBeforeTime S u read).J := by
      intro v hv
      simpa only [FinalityFilterRetainedAtRead, relativeG2Read,
        PhaseGrades.filteredTree, PhaseGrades.readAt, Run.storeBeforeTime] using
        hdomainActiveAt (hJPrevLower.trans (Nat.sub_le q 1)) hqEnd v hv
    have hactiveActionJ : ∀ v ∈ rho.honest,
        (rho.storeBeforeTime S u read).J ∈
          Protocol.get_filtered_block_tree (healStoreAt S rho v q).toFG :=
      htargetActiveAt (hJPrevLower.trans (Nat.sub_le q 1)) hqEnd
    obtain ⟨hAG1, hJA, hAfiltered⟩ :=
      relativeAnchor_of_fixedRootLock S adm hfb hfix hqTwo hformsJ hwindowJ
        hdomainWindowJ hpost hpostPrev hcut (hhorAt hqEnd) hactiveActionJ
          hcarrier.1 hproposalDelay hproposalHor hproposalCap
    let A := nodeAnchor S (proposerReadAt S rho (S.hc.opening_slot q)) q
    have hAdef : nodeAnchor S
        (proposerReadAt S rho (S.hc.opening_slot q)) q = A := rfl
    have hparents :=
      fixedHeightJustificationRootOpeningParentRun_of_fixedRootLock_relative
        S adm hcom hfb hfix hqTwo hformsJ hwindowJ hdomainWindowJ
          hactiveActionJ hlock hpost hproposalDelay hproposalHor hproposalCap
            hpostCone hpostPrev hcarrier.1 hAdef hAG1 hAfiltered hJA
    have hBAction : Block.Preceq B.erase
        (actionSGBlockAt S rho (S.E.proposer (S.hc.opening_slot q)) (q - 1)) :=
      preceq_actionSGBlockAt_of_namedGradeFormsAt S
        adm.toNamedAdmissibleCore hqPredPos (hhorAt hqPredEnd) hformsPrev
          hcarrier.1 (hactionB _ hcarrier.1)
    have hpreceq : Block.Preceq B.erase
        (proposedParent S rho (S.hc.opening_slot q)) :=
      Block.preceq_trans hBAction
        (hparents.actionTargetParent _ hcarrier.1)
    -- the later opening proposal, its parent, and their heights
    obtain ⟨Q, hQ⟩ := proposedBlockAt_isSome S rho (S.hc.opening_slot q)
    obtain ⟨P, hPparent, hPerase⟩ :=
      proposedBlockAt_parent S rho (S.hc.opening_slot q) hQ
    have hBParentErase : Block.Preceq B.erase P.erase := by
      rw [hPerase]
      exact hpreceq
    obtain ⟨B', hB'P, hB'erase⟩ :=
      Proofs.NamedAncestry.erased_ancestor_lift P hBParentErase
    have hspos : 0 < S.hc.opening_slot q := by
      unfold Protocol.HealConfig.opening_slot
      exact Nat.mul_pos hq (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
    have hQRun : RunBlock S rho Q :=
      proposedBlockAt_blockInRun_of_admissible S adm.toNamedAdmissibleCore
        (S.hc.opening_slot q) hspos hcarrier.1 hproposalHor hQ
    have hPRun : RunBlock S rho P :=
      Proofs.NamedRuntime.blockInRun_of_ancestor S rho hQRun
        (fixedRootNamedParent_preceq_of_parent? hPparent)
    have hB'eq : B' = B :=
      fixedRootNamed_run_eq_of_erase adm
        (Proofs.NamedRuntime.blockInRun_of_ancestor S rho hPRun hB'P)
        hlifecycle.runBlock hB'erase
    have hBP : NamedBlock.Preceq B P := by
      simpa only [hB'eq] using hB'P
    have hlowerP : M ≤ (Protocol.derive_named S.E S.cfg P).h := by
      rw [← hBheight]
      exact Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hBP
    have hupperP : (Protocol.derive_named S.E S.cfg P).h ≤ M :=
      (Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg
        (fixedRootNamedParent_preceq_of_parent? hPparent)).trans
        ((honestProposedBlock_height_le_honestHMaxAt
          S adm hspos hcarrier.1 hproposalHor hQ).trans hproposalCap)
    have hsameHeight : (Protocol.derive_named S.E S.cfg P).h =
        (Protocol.derive_named S.E S.cfg B).h := by
      rw [hBheight]
      exact Nat.le_antisymm hupperP hlowerP
    exact laterOpening_timeoutMature_of_sameHeight
      S adm hdelay hlifecycle.roundPositive hspace hlifecycle.proposal
        hQ hPparent hBP hsameHeight
  have hclaimOneRound : r + 4 + gap ≤ endpointRound :=
    fixedClaimOneBound_nat hbound
  rcases _of_lifecycle hfix hpost hreadAction (hhorAt hclaimOneRound) with
    hrise | ⟨q1, hq1lo, hq1hi, hcarrier1, hformsJPrev, hlock1, B1, hB1, hpacket1⟩
  · exact hlift (Assembly.a_mono S hclaimOneRound) hrise
  · obtain ⟨hq1pos, hq1End, hq1PredLower, hrQ1Pred, hrOneQ1, hrQ1,
        hclaimTwoRound, hrQ1Succ, hrTwoQ1⟩ :=
      fixedFirstBounds_nat hbound hq1lo hq1hi
    have hq1PredAdd : q1 - 1 + 1 = q1 := Nat.sub_add_cancel hq1pos
    have hq1PredEnd : q1 - 1 ≤ endpointRound :=
      (Nat.sub_le q1 1).trans hq1End
    have hactionExact1 := hfixedAt hq1PredLower hq1PredEnd
    have hproposalEnd1 :
        Protocol.proposal_time S.E (S.hc.opening_slot q1) ≤
          S.a endpointRound := by
      refine le_trans ?_ (Assembly.a_mono S hq1End)
      rw [Setup.a, Protocol.a_eq_confirmation_time]
      exact Protocol.proposal_time_le_confirmation_time S.E _
    have hlifecycle1 : NamedRawOpeningLifecycleAt S rho q1 B1 := by
      simpa only [hq1PredAdd] using hpacket1.lifecycle
    obtain ⟨hJB1, hB1pred | hB1exact⟩ :=
      fixedRootClaimFour_height_pred_or_current
        S adm hfix hq1pos hpacket1 hactionExact1 hproposalEnd1 hcapEnd
    · -- the first opening sits one height below the fixed frontier
      have hpostJPrev : S.E.t_GST ≤ S.a (q1 - 1) :=
        hpost.trans (hreadAction.trans (Assembly.a_mono S hrQ1Pred))
      have hq1Hor : S.a q1 ≤ rho.horizon := hhorAt hq1End
      have hcut1 : S.hc.Γ_neg1 S.E.Δ q1 ≤ rho.horizon := by
        have hcut1Raw : S.hc.Γ_neg1 S.E.Δ (q1 - 1 + 1) ≤ rho.horizon :=
          (le_of_lt (next_Γ_neg1_lt_action S (q1 - 1))).trans
            (by simpa only [hq1PredAdd] using hq1Hor)
        simpa only [hq1PredAdd] using hcut1Raw
      have hformsJAction : NamedGradeFormsAt S rho q1
          (rho.storeBeforeTime S u read).J := hgradeAt hrTwoQ1 hq1End
      have hreadAction2 : read ≤ S.a q1 :=
        hreadAction.trans (Assembly.a_mono S hrQ1)
      have hpostQ1 : S.E.t_GST ≤ S.a q1 := hpost.trans hreadAction2
      have hreadAction2Wait : read ≤ S.a (q1 + delayExtra) :=
        hreadAction2.trans (Assembly.a_mono S (Nat.le_add_right q1 delayExtra))
      rcases _of_lifecycle hfix hpost hreadAction2Wait
          (hhorAt hclaimTwoRound) with
        hrise2 |
          ⟨q2, hq2lo, hq2hi, hcarrier2, _hformsJ2, hlock2, B2, hB2, hpacket2⟩
      · exact hlift (Assembly.a_mono S hclaimTwoRound) hrise2
      · obtain ⟨hq2pos, hq1q2, hq2End, hq2PredLower, hrOneQ2Succ, hrQ2Succ,
            hrQ2, hq2PrevLower, hq2PredPos, hq2Spacing⟩ :=
          fixedSecondBounds_nat hbound hq1lo hq1hi hq2lo hq2hi
        have hq2PredEnd : q2 - 1 ≤ endpointRound :=
          (Nat.sub_le q2 1).trans hq2End
        have hq2PredAdd : q2 - 1 + 1 = q2 := Nat.sub_add_cancel hq2pos
        have hactionExact2 := hfixedAt hq2PredLower hq2PredEnd
        have hlifecycle2 : NamedRawOpeningLifecycleAt S rho q2 B2 := by
          simpa only [hq2PredAdd] using hpacket2.lifecycle
        have hproposalEnd2 :
            Protocol.proposal_time S.E (S.hc.opening_slot q2) ≤
              S.a endpointRound := by
          refine le_trans ?_ (Assembly.a_mono S hq2End)
          rw [Setup.a, Protocol.a_eq_confirmation_time]
          exact Protocol.proposal_time_le_confirmation_time S.E _
        obtain ⟨hJB2, hB2cases⟩ :=
          fixedRootClaimFour_height_pred_or_current
            S adm hfix hq2pos hpacket2 hactionExact2 hproposalEnd2 hcapEnd
        have hreadAction3 : read ≤ S.a q2 :=
          hreadAction.trans (Assembly.a_mono S hrQ2)
        have hdelayProposal2 : read + S.E.Δ ≤
            Protocol.proposal_time S.E (S.hc.opening_slot q2) := by
          calc
            read + S.E.Δ ≤ S.a q1 + S.E.Δ :=
              Int.add_le_add_right hreadAction2 S.E.Δ
            _ ≤ Protocol.proposal_time S.E (S.hc.opening_slot q2) :=
              action_add_delta_le_openingProposal_of_round_lt S hq1q2
        have hcapProposal2 : honestHMaxAt S rho
            (Protocol.proposal_time S.E (S.hc.opening_slot q2)) ≤ M :=
          (honestHMaxAt_mono S adm.toNamedScheduleWellFormed
            hproposalEnd2).trans hcapEnd
        have hfixedProposal2 :=
          fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRise
            S adm hsb hfix hlifecycle2.proposerHonest hpost hdelayProposal2
              hlifecycle2.proposalInHorizon hcapProposal2
        have hrootDuty2 : Protocol.get_fg_root
            (Protocol.proposerDutyStore S rho
              (S.hc.opening_slot q2)).toHealing.toFG =
              (rho.storeBeforeTime S u read).J := by
          simpa only [Protocol.proposerDutyStore,
            Proofs.Optimistic.tickStore] using hfixedProposal2.1
        have hmaxDuty2 : (Protocol.proposerDutyStore S rho
            (S.hc.opening_slot q2)).h_max = M := by
          simpa only [Protocol.proposerDutyStore,
            Proofs.Optimistic.tickStore] using hfixedProposal2.2
        have hcontinue : (Protocol.derive_named S.E S.cfg B2).h = M →
            M < honestHMaxAt S rho (S.a endpointRound) := by
          intro hB2exact
          have hpostB2 : S.E.t_GST ≤ S.a (q2 + 1) :=
            hpost.trans (hreadAction.trans (Assembly.a_mono S hrQ2Succ))
          obtain ⟨q3, hq3lo, hq3hi, hcarrier3⟩ := hrec (q2 + 2 + delayExtra)
          obtain ⟨hq3End, hrThreeQ3⟩ :=
            fixedThirdEnd_nat hbound hq1lo hq1hi hq2lo hq2hi hq3lo hq3hi
          have hfixedWindow3 : ∀ r', q2 + 1 ≤ r' → r' ≤ q3 →
              ∀ v ∈ rho.honest,
                Protocol.get_fg_root
                    (rho.storeBeforeTime S v (S.a r')).toHealing.toFG =
                  (rho.storeBeforeTime S u read).J ∧
                (rho.storeBeforeTime S v (S.a r')).h_max = M := by
            intro r' hq2r' hr'q3
            exact hfixedAt (hrOneQ2Succ.trans hq2r') (hr'q3.trans hq3End)
          have hproposalEnd3 : Protocol.proposal_time S.E
              (S.hc.opening_slot q3) ≤ S.a endpointRound := by
            refine le_trans ?_ (Assembly.a_mono S hq3End)
            rw [Setup.a, Protocol.a_eq_confirmation_time]
            exact Protocol.proposal_time_le_confirmation_time S.E _
          have hdelayProposal3 : read + S.E.Δ ≤
              Protocol.proposal_time S.E (S.hc.opening_slot q3) := by
            calc
              read + S.E.Δ ≤ S.a q2 + S.E.Δ :=
                Int.add_le_add_right hreadAction3 S.E.Δ
              _ ≤ Protocol.proposal_time S.E (S.hc.opening_slot q3) :=
                action_add_delta_le_openingProposal_of_round_lt S
                  (r := q2) (q := q3) (fixedRootCarrierSpacing_nat hq3lo).1
          have hcapProposal3 : honestHMaxAt S rho
              (Protocol.proposal_time S.E (S.hc.opening_slot q3)) ≤ M :=
            (honestHMaxAt_mono S adm.toNamedScheduleWellFormed
              hproposalEnd3).trans hcapEnd
          have hfixedProposal3 :=
            fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRise
              S adm hsb hfix hcarrier3.1 hpost hdelayProposal3
                (hproposalEnd3.trans hendHor) hcapProposal3
          have hrootDuty3 : Protocol.get_fg_root
              (Protocol.proposerDutyStore S rho
                (S.hc.opening_slot q3)).toHealing.toFG =
                (rho.storeBeforeTime S u read).J := by
            simpa only [Protocol.proposerDutyStore,
              Proofs.Optimistic.tickStore] using hfixedProposal3.1
          have hmaxDuty3 : (Protocol.proposerDutyStore S rho
              (S.hc.opening_slot q3)).h_max = M := by
            simpa only [Protocol.proposerDutyStore,
              Proofs.Optimistic.tickStore] using hfixedProposal3.2
          have hmature3 := htimeoutAt hlifecycle2 hrQ2 hreadAction3 hpostB2
            hq3lo hrThreeQ3 hq3End hcarrier3 hJB2 hB2exact
          exact exactHeightAttempt_rise_of_rebased_of_fixedRoot_noRise
            S adm hfb hfix hlifecycle2.gradeNext hlifecycle2.runBlock hpost
              hreadAction3 (fixedRootCarrierSpacing_nat hq3lo).2 hcarrier3
              hmature3 hB2exact hJB2
              hfixedWindow3 (Assembly.a_mono S hq3End) hendHor hcapEnd
        rcases hB2cases with hB2pred | hB2exact
        · -- both openings sit one height below the frontier
          have hfixedWindow2Pred : ∀ r', q1 + 1 ≤ r' → r' ≤ q2 - 1 →
              ∀ v ∈ rho.honest,
                Protocol.get_fg_root
                    (rho.storeBeforeTime S v (S.a r')).toHealing.toFG =
                  (rho.storeBeforeTime S u read).J ∧
                (rho.storeBeforeTime S v (S.a r')).h_max = M := by
            intro r' hq1r' hr'q2 v hv
            exact hfixedAt (fixedRootWindowLower_nat hrOneQ1 hq1r')
              (hr'q2.trans hq2PredEnd) v hv
          have hthinB1 : M - 1 ≤
              (Protocol.derive_named S.E S.cfg B1).h := by
            rw [hB1pred]
          obtain ⟨hformsB1, hactiveB1⟩ :=
            gradeFormsAt_persist_of_fixedRoot_noRise
              S adm hfb hfix hlifecycle1.gradeNext hlifecycle1.runBlock
                hpost hreadAction2 hq2PrevLower (hhorAt hq2PredEnd)
                (hcapAt hq2PredEnd) hJB1 hthinB1 hfixedWindow2Pred
          have hformsB1Prev : NamedGradeFormsAt S rho (q2 - 1) B1.erase :=
            hformsB1 (q2 - 1) hq2PrevLower (Nat.le_refl _)
          have hactionB1 : ∀ v ∈ rho.honest,
              B1.erase ∈ PhaseGrades.filteredTree
                (actionReadAt S rho v (q2 - 1)) := by
            intro v hv
            refine activeAtAction_of_retainedAtRead S ?_
            simpa only [FinalityFilterRetainedAtRead, healStoreAt] using
              hactiveB1 v hv
          obtain ⟨P2, hP2parent, hP2erase⟩ :=
            proposedBlockAt_parent S rho (S.hc.opening_slot q2)
              hlifecycle2.proposal
          obtain ⟨v0, hv0⟩ := Protocol.honest_nonempty_of_honestCommittees hcom
          have hB1Carrier : Block.Preceq B1.erase
              (actionSGBlockAt S rho v0 (q2 - 1)) :=
            preceq_actionSGBlockAt_of_namedGradeFormsAt
              S adm.toNamedAdmissibleCore hq2PredPos (hhorAt hq2PredEnd)
                hformsB1Prev hv0 (hactionB1 v0 hv0)
          have hCarrierParent : Block.Preceq
              (actionSGBlockAt S rho v0 (q2 - 1))
              (proposedParent S rho (S.hc.opening_slot q2)) := by
            simpa only [hq2PredAdd] using hpacket2.actionTargetParent v0 hv0
          have hB1Parent : Block.Preceq B1.erase P2.erase := by
            rw [hP2erase]
            exact Block.preceq_trans hB1Carrier hCarrierParent
          obtain ⟨B1', hB1'P, hB1'erase⟩ :=
            Proofs.NamedAncestry.erased_ancestor_lift P2 hB1Parent
          have hP2Run : RunBlock S rho P2 :=
            Proofs.NamedRuntime.blockInRun_of_ancestor S rho hlifecycle2.runBlock
              (fixedRootNamedParent_preceq_of_parent? hP2parent)
          have hB1'Run : RunBlock S rho B1' :=
            Proofs.NamedRuntime.blockInRun_of_ancestor S rho hP2Run hB1'P
          have hrootEqB1 : B1'.root = B1.root := by
            rw [← Proofs.NamedWire.erase_root B1', ← Proofs.NamedWire.erase_root B1,
              hB1'erase]
          have hB1'eq : B1' = B1 :=
            adm.toNamedRootCollisionFree.root_injective B1' B1 hB1'Run
              hlifecycle1.runBlock B1' B1
              (Or.inl (Proofs.NamedAncestry.named_self B1'))
              (Or.inr (Proofs.NamedAncestry.named_self B1)) hrootEqB1
          have hlowerP2 : (Protocol.derive_named S.E S.cfg B1).h ≤
              (Protocol.derive_named S.E S.cfg P2).h := by
            have hstep := Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hB1'P
            rwa [hB1'eq] at hstep
          have hupperP2 : (Protocol.derive_named S.E S.cfg P2).h ≤
              (Protocol.derive_named S.E S.cfg B2).h :=
            Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg
              (fixedRootNamedParent_preceq_of_parent? hP2parent)
          have hsameHeight2 :
              (Protocol.derive_named S.E S.cfg P2).h =
                (Protocol.derive_named S.E S.cfg B1).h :=
            fixedRootParentHeight_nat hlowerP2 hupperP2 hB2pred hB1pred
          have hmature2 := opening_timeoutMature_of_persistedGrade
            S adm hdelay hq1pos hq2Spacing hlifecycle1.proposal
              hlifecycle1.runBlock hformsB1Prev (hactionB1 _ hcarrier2.1)
              (hhorAt hq2PredEnd) hpacket2 hP2parent hsameHeight2
          
          -- fixes every honest reader's live confirmation to `B1`
          have hJnEntry : (Protocol.derive_named S.E S.cfg Jn).T_h.root =
              (rho.storeBeforeTime S u read).J.root :=
            namedJustification_targetRoot_of_fixedRoot S adm
              hfix hJnErase hJnRun hJnHeight
          have hactiveJQ1 : ∀ v ∈ rho.honest,
              Jn.erase ∈ PhaseGrades.filteredTree
                (actionReadAt S rho v q1) := by
            intro v hv
            refine activeAtAction_of_retainedAtRead S ?_
            rw [hJnErase]
            simpa only [FinalityFilterRetainedAtRead, healStoreAt] using
              htargetActiveAt hrOneQ1 hq1End v hv
          have hJnB1 : NamedBlock.Preceq Jn B1 := by
            obtain ⟨Jn', hJn'B1, hJn'erase⟩ :=
              Proofs.NamedAncestry.erased_ancestor_lift B1
                (show Block.Preceq Jn.erase B1.erase by
                  rw [hJnErase]; exact hJB1)
            have hJn'eq : Jn' = Jn :=
              fixedRootNamed_run_eq_of_erase adm
                (Proofs.NamedRuntime.blockInRun_of_ancestor S rho
                  hlifecycle1.runBlock hJn'B1) hJnRun hJn'erase
            simpa only [hJn'eq] using hJn'B1
          have hB1entry :
              (Protocol.derive_named S.E S.cfg B1).T_h.root =
                (rho.storeBeforeTime S u read).J.root := by
            rw [← hJnEntry]
            exact congrArg Block.root
              (Proofs.NamedEntryHeight.entry_eq_on_plateau S.E S.cfg hJnB1
                (by rw [hJnHeight, hB1pred])).symm
          have hrowsJ := fixedRootLifecycleRows_at_pred S adm hfix hq1pos
            (hhorAt hq1End)
            (by rw [hJnErase]; exact hformsJAction) hactiveJQ1 hpacket1
            hB1pred hB1entry
          have hrows : ∀ v ∈ rho.honest,
              (actionAttestationAt S rho v q1).height_pair =
                  NamedHeightPair.vote (M - 1)
                    (Protocol.derive_named S.E S.cfg Jn).T_h.root false ∨
                (actionAttestationAt S rho v q1).height_pair =
                  NamedHeightPair.vote (M - 1)
                    (Protocol.derive_named S.E S.cfg Jn).T_h.root true := by
            rw [hJnEntry]
            exact hrowsJ
          have hCcoreQ1 : ∀ v ∈ rho.honest,
              Jn.erase ∈ (actionStoreAt S rho v q1).st.core.T := by
            intro v hv
            simpa only [actionStoreAt, actionReadAt,
              NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
              NamedActionReads.confirmationReadFrom,
              NamedActionReads.preparedCache, Run.storeBeforeTime] using
              fixedRootNamedGradeProcessedAtAction S adm
                (by rw [hJnErase]; exact hformsJAction) hv
          have hq1SuccEnd : q1 + 1 ≤ endpointRound := by
            have hsmall : 1 ≤ delayExtra + 4 + gap := by omega
            calc
              q1 + 1 ≤ q1 + (delayExtra + 4 + gap) :=
                Nat.add_le_add_left hsmall q1
              _ = q1 + delayExtra + 4 + gap := by
                simp only [Nat.add_assoc]
              _ ≤ endpointRound := hclaimTwoRound
          have hdelayPlusTwo : read + S.E.Δ ≤
              Protocol.proposal_time S.E
                (S.hc.opening_slot q1 + 2) := by
            calc
              read + S.E.Δ ≤ S.a q1 + S.E.Δ :=
                Int.add_le_add_right hreadAction2 S.E.Δ
              _ ≤ Protocol.proposal_time S.E
                  (S.hc.opening_slot q1 + 2) :=
                action_add_delta_le_plusTwo_proposal_time S q1
          have hplusTwoFacts := fixedRoot_plusTwoProposal_facts
            S adm hfb hfix hpost hdelayPlusTwo hcarrier1 hq1SuccEnd
              hendHor hcapEnd
          have hparentEq : B2.parent = P2 := by
            cases B2 with
            | genesis => cases hP2parent
            | node p slot root votes support rows proposer =>
                exact Option.some.inj hP2parent
          have hB1ParentRows : Block.Preceq B1.erase B2.parent.erase := by
            rw [hparentEq]
            exact hB1Parent
          have hsourceToParent :=
            _of_sourceToParent hfix hpost hreadAction hq1lo hreadAction2 hq1pos
              hq1q2 hq2End
              hcarrier1 hpostQ1 hendHor hcapEnd hplusTwoFacts hpacket1 hpacket2
              hB1pred hlock1 hlock2 hfixedAt hrootDuty2 hmaxDuty2 hformsB1Prev
              hactionB1 hB1ParentRows hmature2 hq2Spacing
          have hwindowB1 : ∀ v ∈ rho.honest,
              FinalityFilterRetainedAtRead S rho v (S.a (q2 - 1)) B1.erase := by
            intro v hv
            simpa only [FinalityFilterRetainedAtRead, healStoreAt] using
              hactionB1 v hv
          have hpostQ2Pred : S.E.t_GST ≤ S.a (q2 - 1) := by
            have hq1Le : q1 ≤ q2 - 1 :=
              (Nat.le_succ q1).trans hq2PrevLower
            exact hpostQ1.trans (Assembly.a_mono S hq1Le)
          have hB1ParentNamed : NamedBlock.Preceq B1 B2.parent := by
            have hparentEq : B2.parent = P2 := by
              cases B2 with
              | genesis => cases hP2parent
              | node p slot root votes support rows proposer =>
                  exact Option.some.inj hP2parent
            have h := Protocol.namedPreceq_of_runBlock_erase_preceq adm
              hlifecycle1.runBlock hP2Run hB1Parent
            simpa only [hparentEq] using h
          rcases fixedRootFresh_predLifecycle_promotion_named S adm hfb hfix
              hq2pos hq2PredPos hlifecycle1.runBlock hB1pred hB1entry hB1ParentNamed
              hsourceToParent hformsB1Prev hwindowB1 hpacket2 hmature2 hpostQ2Pred with
            hB2exact | hrise2
          · exact hcontinue hB2exact
          · exact hlift hproposalEnd2 hrise2
        · exact hcontinue hB2exact
    · -- the first opening already sits at the fixed frontier
      have hreadAction2 : read ≤ S.a q1 :=
        hreadAction.trans (Assembly.a_mono S hrQ1)
      obtain ⟨q2, hq2lo, hq2hi, hcarrier2⟩ := hrec (q1 + 2 + delayExtra)
      obtain ⟨hq2End, hrThreeQ2⟩ :=
        fixedExactEnd_nat hbound hq1lo hq1hi hq2lo hq2hi
      have hfixedWindow2 : ∀ r', q1 + 1 ≤ r' → r' ≤ q2 →
          ∀ v ∈ rho.honest,
            Protocol.get_fg_root
                (rho.storeBeforeTime S v (S.a r')).toHealing.toFG =
              (rho.storeBeforeTime S u read).J ∧
            (rho.storeBeforeTime S v (S.a r')).h_max = M := by
        intro r' hq1r' hr'q2
        exact hfixedAt (fixedRootWindowLower_nat hrOneQ1 hq1r')
          (hr'q2.trans hq2End)
      have hpostB1 : S.E.t_GST ≤ S.a (q1 + 1) :=
        hpost.trans (hreadAction.trans (Assembly.a_mono S hrQ1Succ))
      have hproposalEnd2 : Protocol.proposal_time S.E
          (S.hc.opening_slot q2) ≤ S.a endpointRound := by
        refine le_trans ?_ (Assembly.a_mono S hq2End)
        rw [Setup.a, Protocol.a_eq_confirmation_time]
        exact Protocol.proposal_time_le_confirmation_time S.E _
      have hdelayProposal2 : read + S.E.Δ ≤
          Protocol.proposal_time S.E (S.hc.opening_slot q2) := by
        calc
          read + S.E.Δ ≤ S.a q1 + S.E.Δ :=
            Int.add_le_add_right hreadAction2 S.E.Δ
          _ ≤ Protocol.proposal_time S.E (S.hc.opening_slot q2) :=
            action_add_delta_le_openingProposal_of_round_lt S
              (r := q1) (q := q2) (fixedRootCarrierSpacing_nat hq2lo).1
      have hcapProposal2 : honestHMaxAt S rho
          (Protocol.proposal_time S.E (S.hc.opening_slot q2)) ≤ M :=
        (honestHMaxAt_mono S adm.toNamedScheduleWellFormed
          hproposalEnd2).trans hcapEnd
      have hfixedProposal2 :=
        fixedHeightJustificationRoot_laterFGRoot_eq_target_and_hMax_eq_of_oneDelay_of_noRise
          S adm hsb hfix hcarrier2.1 hpost hdelayProposal2
            (hproposalEnd2.trans hendHor) hcapProposal2
      have hrootDuty2 : Protocol.get_fg_root
          (Protocol.proposerDutyStore S rho
            (S.hc.opening_slot q2)).toHealing.toFG =
            (rho.storeBeforeTime S u read).J := by
        simpa only [Protocol.proposerDutyStore,
          Proofs.Optimistic.tickStore] using hfixedProposal2.1
      have hmaxDuty2 : (Protocol.proposerDutyStore S rho
          (S.hc.opening_slot q2)).h_max = M := by
        simpa only [Protocol.proposerDutyStore,
          Proofs.Optimistic.tickStore] using hfixedProposal2.2
      have hmature2 := htimeoutAt hlifecycle1 hrQ1 hreadAction2 hpostB1
        hq2lo hrThreeQ2 hq2End hcarrier2 hJB1 hB1exact
      exact exactHeightAttempt_rise_of_rebased_of_fixedRoot_noRise
        S adm hfb hfix hlifecycle1.gradeNext hlifecycle1.runBlock hpost
          hreadAction2 (fixedRootCarrierSpacing_nat hq2lo).2 hcarrier2
          hmature2 hB1exact hJB1
          hfixedWindow2 (Assembly.a_mono S hq2End) hendHor hcapEnd

/-- The same numeric height progress with the bounded proposal lifecycle
instantiated by `fixedHeightJustificationRoot_boundedProposalLifecycle_closed`.
That theorem is hypothesis-free; the scoped source-height callback is the
remaining proof-layer input. -/
theorem fixedRootProgress_of_rows
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {gap : Round}
    (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra)
    (_of_sourceToParent : ∀ {H : Height} {w : V} {read0 : Time}
      {r endpointRound q1 q' : Round} {B1 B2 : NamedBlock V},
      FixedHeightJustificationRootAtRead S rho H w read0 →
      S.E.t_GST ≤ read0 →
      read0 ≤ S.a r →
      r + 3 ≤ q1 →
      read0 ≤ S.a q1 →
      0 < q1 → q1 < q' →
      q' ≤ endpointRound →
      ProposerCarrierAt S rho q1 →
      S.E.t_GST ≤ S.a q1 →
      S.a endpointRound ≤ rho.horizon →
      honestHMaxAt S rho (S.a endpointRound) ≤ H →
      (∃ Bplus : NamedBlock V,
        proposedBlockAt S rho (S.hc.opening_slot q1 + 2) = some Bplus ∧
        RunBlock S rho Bplus ∧
        S.E.proposer (S.hc.opening_slot q1 + 2) ∈ rho.honest ∧
        Protocol.proposal_time S.E (S.hc.opening_slot q1 + 2) ≤ rho.horizon ∧
        Protocol.get_fg_root
            (rho.storeBeforeTime S
              (S.E.proposer (S.hc.opening_slot q1 + 2))
              (Protocol.proposal_time S.E
                (S.hc.opening_slot q1 + 2))).toHealing.toFG =
          (rho.storeBeforeTime S w read0).J ∧
        (rho.storeBeforeTime S
          (S.E.proposer (S.hc.opening_slot q1 + 2))
          (Protocol.proposal_time S.E
            (S.hc.opening_slot q1 + 2))).h_max = H) →
      NamedSGProposalLifecyclePacket S rho (q1 - 1)
        (S.hc.opening_slot q1 - 1) B1 →
      NamedSGProposalLifecyclePacket S rho (q' - 1)
        (S.hc.opening_slot q' - 1) B2 →
      (Protocol.derive_named S.E S.cfg B1).h = H - 1 →
      SGTargetOpeningConeRootLock S rho H (q1 - 1)
        (S.hc.opening_slot q1 - 1) →
      SGTargetOpeningConeRootLock S rho H (q' - 1)
        (S.hc.opening_slot q' - 1) →
      (∀ {k : Round}, r + 1 ≤ k → k ≤ endpointRound →
        ∀ v ∈ rho.honest,
          Protocol.get_fg_root
              (rho.storeBeforeTime S v (S.a k)).toHealing.toFG =
            (rho.storeBeforeTime S w read0).J ∧
          (rho.storeBeforeTime S v (S.a k)).h_max = H) →
      Protocol.get_fg_root
          (Protocol.proposerDutyStore S rho
            (S.hc.opening_slot q')).toHealing.toFG =
        (rho.storeBeforeTime S w read0).J →
      (Protocol.proposerDutyStore S rho
          (S.hc.opening_slot q')).h_max = H →
      NamedGradeFormsAt S rho (q' - 1) B1.erase →
      (∀ v ∈ rho.honest,
        B1.erase ∈ PhaseGrades.filteredTree
          (actionReadAt S rho v (q' - 1))) →
      Block.Preceq B1.erase B2.parent.erase →
      ProposalTimeoutMatureAt S rho (S.hc.opening_slot q') →
      q1 + 2 + delayExtra ≤ q' →
      ∀ v ∈ rho.honest, ∀ Q : Block V,
        nodeFGSource S (actionReadAt S rho v (q' - 1)) (q' - 1) = some Q →
        ((actionReadAt S rho v (q' - 1)).st.core.toHealing.σ Q).h ≤
          (Protocol.derive_named S.E S.cfg B2.parent).h)
    :
    ∀ {M : Height} {u : V} {read : Time}
      {r endpointRound : Round},
      FixedHeightJustificationRootAtRead S rho M u read →
      S.E.t_GST ≤ read → read ≤ S.a r →
      r + 3 * gap + 8 + 2 * delayExtra ≤ endpointRound →
      S.a endpointRound ≤ rho.horizon →
      honestHMaxAt S rho (S.a endpointRound) ≤ M →
      M < honestHMaxAt S rho (S.a endpointRound) :=
  fixedRootProgress_of_lifecycle S adm hcom hfb hrec hdelay
    (fun hfix hpost hreadAction hendHor =>
      fixedHeightJustificationRoot_boundedProposalLifecycle_closed
        S adm hcom hfb hfix hpost hreadAction hrec hendHor)
    _of_sourceToParent

#print axioms fixedRootProgress_of_lifecycle
#print axioms fixedRootProgress_of_rows

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
