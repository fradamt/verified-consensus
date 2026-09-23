module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.HandoverHeight
public import DecoupledConsensusProofs.Protocol.Grades.HonestProposalRawLifecycleNamed
public import DecoupledConsensusProofs.Protocol.Grades.PreparedFrameAfterDeadline

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-! # High opening stable writes after the recovery height gain -/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Internal.NamedRecoveryRead
open Internal.PhaseGrades Protocol Proofs.Optimistic Proofs.HealingLemmas DecoupledConsensusModel.Protocol
open Handover

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}

private theorem postGain_openingSlot_succ_lt_next (S : Setup V) (r : Round) :
    S.hc.opening_slot r + 1 < S.hc.opening_slot (r + 1) := by
  simpa only [Protocol.HealConfig.opening_slot, Nat.add_mul, Nat.one_mul] using
    Nat.add_lt_add_left (Nat.lt_of_succ_le S.hc.R_ge_two) (r * S.hc.R)

private theorem postGain_openingSlot_succ_le_of_lt
    (S : Setup V) {p q : Round} (h : p < q) :
    S.hc.opening_slot p + 1 ≤ S.hc.opening_slot q :=
  (Nat.le_of_lt (postGain_openingSlot_succ_lt_next S p)).trans
    (Nat.mul_le_mul_right S.hc.R h)

private theorem postGain_namedPreceq_of_runBlocks
    {S : Setup V} {rho : Run V} (roots : NamedRootCollisionFree S rho)
    {A B : NamedBlock V} (hArun : RunBlock S rho A)
    (hBrun : RunBlock S rho B) (hAB : Block.Preceq A.erase B.erase) :
    NamedBlock.Preceq A B := by
  obtain ⟨A', hA'B, hA'erase⟩ := Proofs.NamedAncestry.erased_ancestor_lift B hAB
  have hA'run : RunBlock S rho A' :=
    Proofs.NamedRuntime.blockInRun_of_ancestor S rho hBrun hA'B
  have hroot : A.root = A'.root := by
    calc
      A.root = A.erase.root := (Proofs.NamedWire.erase_root A).symm
      _ = A'.erase.root := congrArg Block.root hA'erase.symm
      _ = A'.root := Proofs.NamedWire.erase_root A'
  have hEq : A = A' :=
    roots.root_injective A A' hArun hA'run A A'
      (Or.inl (Proofs.NamedAncestry.named_self A))
      (Or.inr (Proofs.NamedAncestry.named_self A')) hroot
  rw [hEq]
  exact hA'B

set_option maxHeartbeats 400000 in
private theorem postGain_storeGrade_g2_of_relativeCarrierWindow_and_cover
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q : Round} (hq : 0 < q)
    (hpost : S.E.t_GST ≤ S.a (q - 1))
    (hhor : domain S.E S.hc q .g2 ≤ rho.horizon)
    (hforming : Internal.NamedOutageEntry.GradeFormingMajority S rho q)
    (hwindow : RelativeCarrierWindowAt S rho (q - 1) .g2)
    {P : Block V}
    (hcover : ∀ u ∈ rho.honest,
      Block.Preceq P (actionSGBlockAt S rho u (q - 1)))
    {w : V} (hw : w ∈ rho.honest) :
    storeGrade S.E S.hc
      (readAt S rho (domain S.E S.hc q .g2) w).st q .g2 P = true := by
  have hpred : q - 1 + 1 = q := Nat.sub_add_cancel (Nat.succ_le_iff.mpr hq)
  let n := NamedRun.stateBeforeTime S rho (domain S.E S.hc q .g2) w
  let gv := n.st.core.toHealing.gradeView
  let F := n.st.core.F
  let ea := early S.E S.hc q .g2
  let la := late S.E S.hc q .g2
  have hwindowAt : ∀ u ∈ Internal.NamedOutageEntry.honestRoundVoters S rho (q - 1),
      ∃ y ∈ DecoupledConsensusModel.Protocol.interpretedInputs gv F S.hc.η_SG q ea u,
        y.round = q - 1 ∧
        y.confirmed = some (actionSGBlockAt S rho u (q - 1)).root ∧
        Block.find? n.st.core.T (actionSGBlockAt S rho u (q - 1)).root =
          some (actionSGBlockAt S rho u (q - 1)) := by
    intro u hu
    have h := hwindow w hw u hu
    change ∃ y ∈ DecoupledConsensusModel.Protocol.interpretedInputs
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc (q - 1 + 1) .g2) w).st.core.toHealing.gradeView
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc (q - 1 + 1) .g2) w).st.core.F
        S.hc.η_SG (q - 1 + 1) (early S.E S.hc (q - 1 + 1) .g2) u,
      y.round = q - 1 ∧
        y.confirmed = some (actionSGBlockAt S rho u (q - 1)).root ∧
        Block.find? (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc (q - 1 + 1) .g2) w).st.core.T
          (actionSGBlockAt S rho u (q - 1)).root =
            some (actionSGBlockAt S rho u (q - 1)) at h
    simpa only [n, gv, F, ea, hpred] using h
  have hpositive : Internal.NamedOutageEntry.honestRoundVoters S rho (q - 1) ⊆
      Finset.univ.filter fun u =>
        DecoupledConsensusModel.Protocol.positive gv F S.hc.η_SG q ea la u P = true := by
    intro u hu
    have huHon := ((Proofs.NamedOutageInputs.honestRoundVoters_iff
      S rho u (q - 1)).mp hu).1
    obtain ⟨y, hy, hyround, hyconfirmed, hyfind⟩ := hwindowAt u hu
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ u, ?_⟩
    simp only [DecoupledConsensusModel.Protocol.positive, decide_eq_true_eq]
    refine ⟨DecoupledConsensusModel.Protocol.token y, ?_, ?_, ?_, ?_, ?_⟩
    · exact Finset.mem_image_of_mem DecoupledConsensusModel.Protocol.token hy
    · intro x hx
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      have hzraw := (Finset.mem_filter.mp hz).1
      change z ∈ DecoupledConsensusModel.Protocol.rawInputs
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc q .g2) w).st.core.toHealing.gradeView
        S.hc.η_SG q (early S.E S.hc q .g2) u at hzraw
      have hzraw' : z ∈ DecoupledConsensusModel.Protocol.rawInputs
          (NamedRun.stateBeforeTime S rho
            (domain S.E S.hc q .g2) w).st.core.toHealing.gradeView
          S.hc.η_SG (q - 1 + 1) (early S.E S.hc q .g2) u := by
        simpa only [hpred] using hzraw
      obtain ⟨_, _, _, _, _, _, _, _, hzupper⟩ :=
        NamedOutageClosure.honest_rawInput_is_own_round_vote S rho
          adm.toNamedAdmissibleCore (domain S.E S.hc q .g2)
          (early S.E S.hc q .g2) w hw huHon (r := q - 1) hzraw'
      simpa only [DecoupledConsensusModel.Protocol.token, hyround] using hzupper
    · change Protocol.head_covers n.st.core.T P y.confirmed = true
      rw [hyconfirmed]
      simp only [Protocol.head_covers]
      rw [show Block.find? n.st.core.T
          (actionSGBlockAt S rho u (q - 1)).root =
            some (actionSGBlockAt S rho u (q - 1)) by
        simpa only [n, hpred] using hyfind]
      exact hcover u huHon
    · have hclean := NamedOutageClosure.honest_rawView_clean S rho
        adm.toNamedAdmissibleCore (domain S.E S.hc q .g2) la
        w hw huHon (q - 1) (DecoupledConsensusModel.Protocol.token y).round
      rw [hpred] at hclean
      exact hclean
    · intro x hx hlt
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      have hzraw := (Finset.mem_filter.mp hz).1
      change z ∈ DecoupledConsensusModel.Protocol.rawInputs
        (NamedRun.stateBeforeTime S rho
          (domain S.E S.hc q .g2) w).st.core.toHealing.gradeView
        S.hc.η_SG q (late S.E S.hc q .g2) u at hzraw
      have hzraw' : z ∈ DecoupledConsensusModel.Protocol.rawInputs
          (NamedRun.stateBeforeTime S rho
            (domain S.E S.hc q .g2) w).st.core.toHealing.gradeView
          S.hc.η_SG (q - 1 + 1) (late S.E S.hc q .g2) u := by
        simpa only [hpred] using hzraw
      obtain ⟨_, _, _, _, _, _, _, _, hzupper⟩ :=
        NamedOutageClosure.honest_rawInput_is_own_round_vote S rho
          adm.toNamedAdmissibleCore (domain S.E S.hc q .g2)
          (late S.E S.hc q .g2) w hw huHon (r := q - 1) hzraw'
      exfalso
      exact (Nat.not_lt_of_ge hzupper) (by
        simpa only [DecoupledConsensusModel.Protocol.token, hyround] using hlt)
  have hopposing : (Finset.univ.filter fun u =>
      DecoupledConsensusModel.Protocol.opposing gv F S.hc.η_SG q ea la u P = true) ⊆
      (Finset.univ \ rho.honest) ∪
        Internal.NamedOutageEntry.staleHistoricalVoters S rho q := by
    intro u hu
    by_cases huHon : u ∈ rho.honest
    · have huVoter : u ∈ Internal.NamedOutageEntry.honestRoundVoters S rho (q - 1) := by
        apply (Proofs.NamedOutageInputs.honestRoundVoters_iff S rho u (q - 1)).mpr
        have hprevHor : S.a (q - 1) ≤ rho.horizon :=
          (NamedOutageClosure.action_le_domain S S.hc.R_ge_three
            (Nat.sub_lt hq (by decide))).trans hhor
        exact ⟨huHon, actionAttestationAt S rho u (q - 1),
          (actionAttestationAt_shape S rho u (q - 1)).1,
          (actionAttestationAt_shape S rho u (q - 1)).2.1,
          honest_emits_exact_actionAttestationAt S adm huHon (q - 1) hprevHor hpost⟩
      have hopp := (Finset.mem_filter.mp hu).2
      simp only [DecoupledConsensusModel.Protocol.opposing, decide_eq_true_eq] at hopp
      rcases hopp with ⟨x, hx, hdom, hnotcover⟩ |
        ⟨x, hx, y, hy, _, hround, hkey⟩
      · simp only [DecoupledConsensusModel.Protocol.readyView, Finset.mem_image] at hx
        obtain ⟨z, hz, rfl⟩ := hx
        have hzraw := (Finset.mem_filter.mp hz).1
        change z ∈ DecoupledConsensusModel.Protocol.rawInputs
          (NamedRun.stateBeforeTime S rho
            (domain S.E S.hc q .g2) w).st.core.toHealing.gradeView
          S.hc.η_SG q (late S.E S.hc q .g2) u at hzraw
        have hzraw' : z ∈ DecoupledConsensusModel.Protocol.rawInputs
            (NamedRun.stateBeforeTime S rho
              (domain S.E S.hc q .g2) w).st.core.toHealing.gradeView
            S.hc.η_SG (q - 1 + 1) (late S.E S.hc q .g2) u := by
          simpa only [hpred] using hzraw
        obtain ⟨a, haround, _, hemit, _, hconfirmed, _, _, hzupper⟩ :=
          NamedOutageClosure.honest_rawInput_is_own_round_vote S rho
            adm.toNamedAdmissibleCore (domain S.E S.hc q .g2)
            (late S.E S.hc q .g2) w hw huHon (r := q - 1) hzraw'
        obtain ⟨earlyVote, hearly, hearlyRound, _, hfind⟩ :=
          hwindowAt u huVoter
        have hsourceLe : q - 1 ≤ z.round := by
          simpa only [DecoupledConsensusModel.Protocol.token, hearlyRound] using
            hdom (DecoupledConsensusModel.Protocol.token earlyVote)
              (Finset.mem_image_of_mem DecoupledConsensusModel.Protocol.token hearly)
        have hzround : z.round = q - 1 :=
          Nat.le_antisymm hzupper hsourceLe
        have har : a.round = q - 1 := haround.trans hzround
        have hem : NamedRun.emits S rho u (.attest a) (S.a (q - 1)) := by
          simpa only [hzround] using hemit
        have hconfirmedAction := NamedOutageClosure.honest_emitted_round_confirmed
          S rho adm.toNamedAdmissibleCore u huHon (q - 1)
          ((NamedOutageClosure.action_le_domain S S.hc.R_ge_three
            (Nat.sub_lt hq (by decide))).trans hhor) har hem
        exact False.elim (hnotcover (by
          change Protocol.head_covers n.st.core.T P z.confirmed = true
          rw [hconfirmed, hconfirmedAction]
          simp only [Protocol.head_covers]
          rw [show Block.find? n.st.core.T
              (actionSGBlockAt S rho u (q - 1)).root =
                some (actionSGBlockAt S rho u (q - 1)) by
            simpa only [n, hpred] using hfind]
          exact hcover u huHon))
      · have hclean0 := NamedOutageClosure.honest_rawView_clean S rho
          adm.toNamedAdmissibleCore (domain S.E S.hc q .g2) la
          w hw huHon (q - 1) 0
        rw [hpred] at hclean0
        exact False.elim (hkey
          (hclean0 x hx y hy (Nat.zero_le _) hround))
    · exact Finset.mem_union_left _
        (Finset.mem_sdiff.mpr ⟨Finset.mem_univ u, huHon⟩)
  change DecoupledConsensusModel.Protocol.gradeBool S.E gv F S.hc.η_SG q ea la P = true
  exact phaseGrade_of_gradeFormingMajority S rho q gv F P ea la
    hforming hpositive hopposing

private theorem postGain_frameStableRoot_of_high_viable_prefix
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {v : V} (hv : v ∈ rho.honest) {t : Time} {r : Round} {cap : Height}
    {Q R2 : Block V} {Qn : NamedBlock V}
    (hraw : (DecoupledConsensusModel.Protocol.readFrame
      (NamedActionReads.confirmationReadAt S rho v t).cache
      (NamedActionReads.confirmationReadAt S rho v t).st.core.toHealing r).g2.bind id =
        some R2)
    (hQR : Block.Preceq Q R2)
    (hQerase : Qn.erase = Q) (hQrun : RunBlock S rho Qn)
    (hQmem : Q ∈ (rho.stateBeforeTime S t v).st.core.T)
    (hQviable : Protocol.viable
      (rho.stateBeforeTime S t v).st.core.σ
      (rho.stateBeforeTime S t v).st.core.h_max
      (rho.stateBeforeTime S t v).st.core.T Q = true)
    (hQrootCompat : Block.compatible Q
      (Protocol.get_fg_root
        (rho.stateBeforeTime S t v).st.core.toHealing.toFG) = true)
    (hcap : cap < (Protocol.derive_named S.E S.cfg Qn).h) :
    ∃ (G : Block V) (Gn : NamedBlock V),
      DecoupledConsensusModel.Protocol.frameStableRoot
          (NamedActionReads.confirmationReadAt S rho v t).cache S.E S.hc
          (NamedActionReads.confirmationReadAt S rho v t).st.core.toHealing r = some G ∧
        Gn.erase = G ∧ RunBlock S rho Gn ∧
        cap < (Protocol.derive_named S.E S.cfg Gn).h := by
  classical
  let n := NamedActionReads.confirmationReadAt S rho v t
  let st := n.st.core
  let root := Protocol.get_fg_root st.toHealing.toFG
  have hQmem' : Q ∈ st.T := by
    simpa only [st, n, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using hQmem
  have hQviable' : Protocol.viable st.σ st.h_max st.T Q = true := by
    simpa only [st, n, NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using hQviable
  have hFJ := Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
    S rho t v
  have hFroot : Block.Preceq st.F root :=
    StoreFinality.finalized_preceq_fgRoot (by
      simpa only [st, n, NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using hFJ)
  have hQfiltered_of_root (hrootQ : Block.Preceq root Q) :
      Q ∈ Protocol.get_filtered_block_tree st.toHealing.toFG := by
    simp only [Protocol.get_filtered_block_tree,
      Protocol.get_filtered_block_tree_from, Protocol.viable_tree,
      Protocol.finalized_descendants, Finset.mem_filter,
      decide_eq_true_eq, Protocol.Store.toHealing]
    exact ⟨⟨⟨hQmem', Block.preceq_trans hFroot hrootQ⟩, hQviable'⟩, hrootQ⟩
  have hQroot : Block.Preceq Q root ∨ Block.Preceq root Q := by
    simpa only [Block.compatible, Bool.or_eq_true] using hQrootCompat
  simp only [DecoupledConsensusModel.Protocol.frameStableRoot]
  rw [show (DecoupledConsensusModel.Protocol.readFrame n.cache n.st.core.toHealing r).g2.bind id =
      some R2 by simpa only [n] using hraw]
  simp only [Option.bind_some]
  cases hactive : DecoupledConsensusModel.Protocol.activePrefix
      (Protocol.get_filtered_block_tree n.st.core.toHealing.toFG) R2 with
  | none =>
      have hQroot' : Block.Preceq Q root := by
        rcases hQroot with hQr | hrQ
        · exact hQr
        · have hQfiltered := hQfiltered_of_root hrQ
          obtain ⟨X, hX, -⟩ := NamedOutageClosure.q10_activePrefix_dominates
            (by simpa only [n, st] using hQfiltered) hQR
          rw [hactive] at hX
          contradiction
      have hinvPre := (Proofs.NamedRuntime.stateBeforeTime_invariants S rho t v).1
      have hinv : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg n.st := by
        simpa only [n, NamedActionReads.confirmationReadAt] using
          Proofs.NamedConfirmationMembership.invariant_clock S.E S.cfg _ _ hinvPre
      have hrootMem : root ∈ st.T := by
        simpa only [n, st, root] using
          Proofs.NamedStoreRoots.fg_root_mem n.st hinv.1.2
      obtain ⟨Gn, hGerase, hGrun⟩ :=
        Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
          adm.toNamedScheduleWellFormed hv t hrootMem
      have hQGn : NamedBlock.Preceq Qn Gn :=
        postGain_namedPreceq_of_runBlocks adm.toNamedRootCollisionFree
          hQrun hGrun (by simpa only [hQerase, hGerase] using hQroot')
      refine ⟨root, Gn, ?_, hGerase, hGrun, hcap.trans_le ?_⟩
      · simpa only [n, st, root, hactive]
      · exact Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hQGn
  | some G =>
      have hGfiltered : G ∈
          Protocol.get_filtered_block_tree n.st.core.toHealing.toFG :=
        NamedProposalParent.activePrefix_mem _ R2 G hactive
      have hQG : Block.Preceq Q G := by
        rcases hQroot with hQr | hrQ
        · exact Block.preceq_trans hQr
            (Proofs.Records.preceq_get_fg_root_of_mem_filtered hGfiltered)
        · have hQfiltered := hQfiltered_of_root hrQ
          obtain ⟨X, hX, hQX⟩ := NamedOutageClosure.q10_activePrefix_dominates
            (by simpa only [n, st] using hQfiltered) hQR
          have hXG : X = G := Option.some.inj (hX.symm.trans hactive)
          simpa only [hXG] using hQX
      have hGcore : G ∈ st.T := by
        have := Proofs.Records.get_filtered_block_tree_subset _ hGfiltered
        simpa only [n, st] using this
      obtain ⟨Gn, hGerase, hGrun⟩ :=
        Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
          adm.toNamedScheduleWellFormed hv t hGcore
      have hQGn : NamedBlock.Preceq Qn Gn :=
        postGain_namedPreceq_of_runBlocks adm.toNamedRootCollisionFree
          hQrun hGrun (by simpa only [hQerase, hGerase] using hQG)
      refine ⟨G, Gn, ?_, hGerase, hGrun, hcap.trans_le ?_⟩
      · simpa only [n, hactive]
      · exact Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hQGn

/-- The first recurrent carrier strictly after the two-progress point has a
named proposal strictly above the pre-progress honest frontier. -/
private theorem postGain_window_le_nat {d l gap eta m : Nat}
    (hm : d + 2 * l + max (1 + eta) (gap + 3) ≤ m) :
    d + 2 * l + 1 + gap ≤ m := by
  omega

theorem exists_postGain_carrier_height_r270
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {m : Round}
    (hm : fgSafetyProgressDeadline S rho rGST gap delayExtra +
        2 * progressLag' gap delayExtra +
        max (1 + S.hc.η_SG) (gap + 3) ≤ m)
    (hhor : Protocol.confirmation_time S.E
      (S.hc.opening_slot m) ≤ rho.horizon) :
    ∃ q : Round, ∃ P : NamedBlock V,
      fgSafetyProgressDeadline S rho rGST gap delayExtra +
          2 * progressLag' gap delayExtra + 1 ≤ q ∧
      q ≤ fgSafetyProgressDeadline S rho rGST gap delayExtra +
          2 * progressLag' gap delayExtra + 1 + gap ∧
      q + 1 < m ∧
      ProposerCarrierAt S rho q ∧
      proposedBlockAt S rho (S.hc.opening_slot q) = some P ∧
      honestHMaxAt S rho
          (S.a (fgSafetyProgressDeadline S rho rGST gap delayExtra)) <
        (Protocol.derive_named S.E S.cfg P).h := by
  classical
  let D := fgSafetyProgressDeadline S rho rGST gap delayExtra
  let L := progressLag' gap delayExtra
  let r0 : Round := D + 2 * L
  have hGSTdead : rGST ≤ D := by
    dsimp only [D]
    unfold fgSafetyProgressDeadline
    exact (Nat.le_succ rGST).trans (Nat.le_add_right _ _)
  have hGSTwindow : S.E.t_GST ≤
      Protocol.proposal_time S.E (S.hc.opening_slot (r0 + 1)) :=
    hpost.trans ((Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans
      (action_add_delta_le_openingProposal_of_round_lt S
        (Nat.lt_of_le_of_lt hGSTdead (by
          dsimp only [r0]
          exact Nat.lt_succ_of_le (Nat.le_add_right D (2 * L))))))
  have hwindowRound : r0 + 1 + gap ≤ m := by
    simpa only [r0, D, L] using postGain_window_le_nat hm
  have hhorAction : S.a m ≤ rho.horizon := by
    simpa only [opening_confirmation_time_eq_action] using hhor
  have hhorWindow := (openingProposal_window_le_action S (r0 + 1) gap).trans
    ((Assembly.a_mono S hwindowRound).trans hhorAction)
  obtain ⟨q, hqlo, hqhi, hcarrier⟩ := hrec (r0 + 1) hGSTwindow hhorWindow
  have hqStrict : r0 < q := Nat.lt_of_lt_of_le (Nat.lt_succ_self r0) hqlo
  have hqm : q + 1 < m := by
    have hgap : D + 2 * L + (gap + 3) ≤ m := by
      exact (Nat.add_le_add_left (le_max_right _ _) (D + 2 * L)).trans (by
        simpa only [Nat.add_assoc] using hm)
    have hq2 : q + 2 ≤ r0 + 1 + gap + 2 := Nat.add_le_add_right hqhi 2
    have heq : r0 + 1 + gap + 2 = D + 2 * L + (gap + 3) := by
      calc
        r0 + 1 + gap + 2 = r0 + (1 + gap + 2) := by
          simp only [Nat.add_assoc]
        _ = r0 + (gap + 3) := by
          congr 1
          rw [Nat.add_comm 1 gap, Nat.add_assoc]
        _ = D + 2 * L + (gap + 3) := rfl
    have hq2m : q + 2 ≤ m := by rw [heq] at hq2; exact hq2.trans hgap
    exact Nat.lt_of_succ_le (by simpa only [Nat.add_assoc] using hq2m)
  have hqLeM : q ≤ m := Nat.le_of_lt (lt_of_le_of_lt (Nat.le_succ q) hqm)
  have hqHor : S.a q ≤ rho.horizon := by
    have hmAction : S.a m ≤ rho.horizon := by
      simpa only [opening_confirmation_time_eq_action] using hhor
    exact (Assembly.a_mono S hqLeM).trans hmAction
  have hconfHor : Protocol.confirmation_time S.E
      (S.hc.opening_slot q) ≤ rho.horizon := by
    simpa only [opening_confirmation_time_eq_action] using hqHor
  obtain ⟨P, hP⟩ := proposedBlockAt_isSome S rho (S.hc.opening_slot q)
  obtain ⟨u, hu⟩ := honest_nonempty_of_honestCommittees hcom
  have hDq : D ≤ q := by
    exact (Nat.le_add_right D (2 * L)).trans hqStrict.le
  have hDtwoQ : D + 2 ≤ q := by
    have hLpos : 1 ≤ L := by simpa only [L] using progressLag'_pos gap
    have h2L : 2 ≤ 2 * L := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left 2 hLpos
    exact (Nat.add_le_add_left h2L D).trans hqStrict.le
  have hreadLo : S.a D ≤ S.a q := Assembly.a_mono S hDq
  have hDr0 : D ≤ r0 := by
    simpa only [r0] using (Nat.le_add_right D (2 * L))
  have hopenLo : S.hc.opening_slot D + 1 ≤ S.hc.opening_slot q := by
    exact postGain_openingSlot_succ_le_of_lt S
      (lt_of_le_of_lt hDr0 hqStrict)
  have hvoteHor : Protocol.vote_time S.E (S.hc.opening_slot q) ≤ rho.horizon :=
    (vote_time_le_confirmation_time S.E _).trans hconfHor
  have hvoteDelta : Protocol.vote_time S.E (S.hc.opening_slot q) + S.E.Δ ≤
      rho.horizon := by
    rw [vote_time_add_delta]
    exact (support_cutoff_le_confirmation_time S.E _).trans hconfHor
  obtain ⟨T, hTrun, hTband, hTheads⟩ :=
    exists_namedCommonPreviousHeadAncestor_in_frontierBand_through_confirmation_after_GST
      S adm hcom hbelow hrec hdelay hpost hreadLo hqHor hopenLo
        (by simpa only [opening_confirmation_time_eq_action] using
          (le_refl (S.a q))) hvoteDelta hu
  have hheads : ∀ w ∈ rho.honest,
      voterHeadAt S rho w (S.hc.opening_slot q) = P.erase :=
    honestProposal_voterHeadAt_eq_after_SG_healing_named
      S adm hcom hbelow hrec hdelay hpost
        (by simpa only [D] using hDtwoQ) hvoteHor hcarrier hP
  have hTP : Block.Preceq T.erase P.erase := by
    have h := hTheads u hu
    rwa [hheads u hu] at h
  have hqPos : 0 < q := lt_of_lt_of_le Nat.zero_lt_two
    ((Nat.le_add_left 2 D).trans hDtwoQ)
  have hopenPos : 0 < S.hc.opening_slot q := by
    unfold Protocol.HealConfig.opening_slot
    exact Nat.mul_pos hqPos (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two)
  have hproposalHor : Protocol.proposal_time S.E (S.hc.opening_slot q) ≤
      rho.horizon :=
    (proposal_time_lt_vote_time S.E _).le.trans hvoteHor
  have hPrun : RunBlock S rho P :=
    proposedBlockAt_blockInRun_of_admissible S adm.toNamedAdmissibleCore
      (S.hc.opening_slot q) hopenPos hcarrier.1 hproposalHor hP
  have hTPn : NamedBlock.Preceq T P :=
    postGain_namedPreceq_of_runBlocks adm.toNamedRootCollisionFree hTrun hPrun hTP
  have hTheight : (Protocol.derive_named S.E S.cfg T).h ≤
      (Protocol.derive_named S.E S.cfg P).h :=
    Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hTPn
  have hr0Hor : S.a r0 ≤ rho.horizon :=
    (Assembly.a_mono S hqStrict.le).trans hqHor
  have hgain : honestHMaxAt S rho (S.a D) + 2 ≤
      honestHMaxAt S rho (S.a r0) := by
    have h := honestHMaxAt_gt_after_twoProgress S adm hcom hbelow hrec
      hdelay hpost (r := r0) (show D + 2 * L ≤ r0 by rfl) hr0Hor
    simpa only [Nat.add_assoc] using h
  have hr0Post : S.E.t_GST ≤ S.a r0 := by
    have hrGSTr0 : rGST ≤ r0 :=
      (Nat.le_succ rGST).trans
        ((gstRound_succ_le_deadline S rho rGST gap).trans
          (by simpa only [D, L, r0] using Nat.le_add_right D (2 * L)))
    exact hpost.trans (Assembly.a_mono S hrGSTr0)
  have hrelay : S.a r0 + 1 + S.E.Δ ≤ S.a q :=
    action_succ_delta_le_action_of_lt S hqStrict
  have hlocal := honestHMaxAt_le_localFrontier_after_oneDelay S adm hcom
    (slashableBound_of_admissible_belowOneThird S adm hbelow)
      hr0Post hrelay hqHor u hu
  have hheight : honestHMaxAt S rho (S.a D) <
      (Protocol.derive_named S.E S.cfg P).h :=
    heightOld_assemble hgain hlocal hTband hTheight
  exact ⟨q, P, by simpa only [D, L, r0, Nat.add_assoc] using hqlo,
    by simpa only [D, L, r0, Nat.add_assoc] using hqhi, hqm,
    hcarrier, hP, by simpa only [D] using hheight⟩

#print axioms exists_postGain_carrier_height_r270

set_option maxHeartbeats 400000 in
private theorem postGain_localFrameRoot_above_proposal
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    {q : Round} {P : NamedBlock V} {v : V} (hv : v ∈ rho.honest)
    (hpost : S.E.t_GST ≤ S.a q)
    (hdomainHor : domain S.E S.hc (q + 1) .g2 ≤ rho.horizon)
    (hwindow : RelativeCarrierWindowAt S rho q .g2)
    (hforming : Internal.NamedOutageEntry.GradeFormingMajority S rho (q + 1))
    (hcover : ActionCarriersCover S rho q P.erase) :
    let o := S.hc.opening_slot (q + 1)
    let t := Protocol.confirmation_time S.E o
    ∃ raw R2 : Block V,
      DecoupledConsensusModel.Protocol.freezeRoot S.E
          (NamedRun.stateBeforeTime S rho
            (domain S.E S.hc (q + 1) .g2) v).st.core.toHealing.gradeView
          (NamedRun.stateBeforeTime S rho
            (domain S.E S.hc (q + 1) .g2) v).st.core.F
          S.hc.η_SG (q + 1) (early S.E S.hc (q + 1) .g2)
          (late S.E S.hc (q + 1) .g2) = some raw ∧
      (DecoupledConsensusModel.Protocol.readFrame
          (confirmationInputRead S rho v o).cache
          (confirmationInputRead S rho v o).st.core.toHealing (q + 1)).g2 =
        some (some R2) ∧
      R2 = DecoupledConsensusModel.Protocol.clipGrade raw
        (NamedRun.stateBeforeTime S rho t v).st.core.F ∧
      Block.Preceq P.erase raw := by
  classical
  let r : Round := q + 1
  let o : Slot := S.hc.opening_slot r
  let t : Time := Protocol.confirmation_time S.E o
  have hrPos : 0 < r := by dsimp only [r]; exact Nat.succ_pos q
  have hprev : r - 1 = q := by simp only [r, Nat.add_sub_cancel]
  have hgrade : storeGrade S.E S.hc
      (readAt S rho (domain S.E S.hc r .g2) v).st r .g2 P.erase = true := by
    apply postGain_storeGrade_g2_of_relativeCarrierWindow_and_cover
      S adm hrPos (by simpa only [hprev] using hpost)
      (by simpa only [r] using hdomainHor)
      (by simpa only [r] using hforming)
    · simpa only [hprev] using hwindow
    · intro u hu
      simpa only [hprev] using hcover u hu
    · exact hv
  have hqActionHor : S.a q ≤ rho.horizon :=
    (NamedOutageClosure.action_le_domain S S.hc.R_ge_three
      (Nat.lt_succ_self q)).trans hdomainHor
  obtain ⟨u, hu⟩ := honest_nonempty_of_honestCommittees hcom
  have huVoter : u ∈ Internal.NamedOutageEntry.honestRoundVoters S rho q := by
    apply (Proofs.NamedOutageInputs.honestRoundVoters_iff S rho u q).mpr
    exact ⟨hu, actionAttestationAt S rho u q,
      (actionAttestationAt_shape S rho u q).1,
      (actionAttestationAt_shape S rho u q).2.1,
      honest_emits_exact_actionAttestationAt S adm hu q hqActionHor hpost⟩
  obtain ⟨y, hy, hyround, hyconfirmed, hyfind⟩ := hwindow v hv u huVoter
  have hcarrierMem : actionSGBlockAt S rho u q ∈
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) v).st.core.T := by
    have := Proofs.HealingLemmas.find?_mem hyfind
    simpa only [hprev] using this
  have hPdomain : P.erase ∈
      (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) v).st.core.T :=
    Proofs.Records.mem_of_preceq
      ((parentClosed_iff _).mp (Proofs.NamedStoreBridge.parentClosed_stateBeforeTime
        S rho (domain S.E S.hc r .g2) v)).2
      P.erase (actionSGBlockAt S rho u q) hcarrierMem (hcover u hu)
  obtain ⟨raw, hfreeze, hPraw⟩ := NamedOutageClosure.q10_freeze_of_graded S.E
    (NamedRun.stateBeforeTime S rho
      (domain S.E S.hc r .g2) v).st.core.toHealing.gradeView
    (NamedRun.stateBeforeTime S rho
      (domain S.E S.hc r .g2) v).st.core.F
    S.hc.η_SG r (NamedOutageClosure.q10_early_le_late S r .g2)
    hPdomain (by simpa only [storeGrade, phaseGrade] using hgrade)
  have htAction : t = S.a r := by
    simpa only [t, o, r] using opening_confirmation_time_eq_action S r
  have hround : S.hc.round_of (S.E.slotOf t) = r := by
    rw [htAction]
    exact Proofs.HealingLemmas.round_of_slotOf_a S r
  have hg2Base := FrameCompleted.frame_phase_completed
    S rho adm.toNamedAdmissibleCore v hv r hrPos .g2 t
      (by simpa only [htAction] using NamedOutageClosure.q10_domain_lt_a S r .g2)
      (le_of_eq htAction) (by simpa only [r] using hdomainHor)
  have hg2Prepared := NamedOutageClosure.frame_phase_prepared_eq
    S rho v r .g2 t hround _ hg2Base
  let R2 := DecoupledConsensusModel.Protocol.clipGrade raw
    (NamedRun.stateBeforeTime S rho t v).st.core.F
  refine ⟨raw, R2, ?_, ?_, rfl, hPraw⟩
  · simpa only [r] using hfreeze
  · simpa only [confirmationInputRead, o, t, r, hfreeze, Option.map_some, R2]
      using hg2Prepared







set_option maxHeartbeats 400000 in
private theorem postGain_actionCarrier_below_consuming_head
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {q : Round} (hq :
      fgSafetyProgressDeadline S rho rGST gap delayExtra + 2 ≤ q)
    (hrHor : S.a (q + 1) ≤ rho.horizon)
    {u v : V} (hu : u ∈ rho.honest) (hv : v ∈ rho.honest) :
    Block.Preceq (actionSGBlockAt S rho u q)
      (voterHeadAt S rho v (S.hc.opening_slot (q + 1) + 1)) := by
  let D := fgSafetyProgressDeadline S rho rGST gap delayExtra
  have hDpred : D ≤ q - 1 := Nat.le_sub_of_add_le
    ((Nat.add_le_add_left (by decide : 1 ≤ 2) D).trans
      (by simpa only [D] using hq))
  have hqPos : 0 < q := lt_of_lt_of_le Nat.zero_lt_two
    ((Nat.le_add_left 2 D).trans (by simpa only [D] using hq))
  have hpred : q - 1 + 1 = q :=
    Nat.sub_add_cancel (Nat.succ_le_iff.mpr hqPos)
  have hdHor : Protocol.vote_time S.E
      (S.hc.opening_slot (q + 1) + 1) + S.E.Δ ≤ rho.horizon := by
    rw [vote_time_succ_add_delta_eq_confirmation_time,
      opening_confirmation_time_eq_action]
    exact hrHor
  have hopenQD : S.hc.opening_slot q + 1 ≤
      S.hc.opening_slot (q + 1) + 1 :=
    (postGain_openingSlot_succ_lt_next S q).le.trans (Nat.le_succ _)
  simpa only [hpred] using
    (actionSGBlock_preceq_voterHeadAt_after_GST
      S adm hcom hbelow hrec hdelay hpost
        (c := q - 1) (by simpa only [D] using hDpred)
        (by simpa only [hpred] using hopenQD) hdHor hu hv)

set_option maxHeartbeats 400000 in
private theorem postGain_proposal_below_consuming_head
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {q : Round} {P : NamedBlock V} (hq :
      fgSafetyProgressDeadline S rho rGST gap delayExtra + 2 ≤ q)
    (hrHor : S.a (q + 1) ≤ rho.horizon)
    (hcover : ActionCarriersCover S rho q P.erase)
    {v : V} (hv : v ∈ rho.honest) :
    Block.Preceq P.erase
      (voterHeadAt S rho v (S.hc.opening_slot (q + 1) + 1)) := by
  exact Block.preceq_trans (hcover v hv)
    (postGain_actionCarrier_below_consuming_head
      S adm hcom hbelow hrec hdelay hpost hq hrHor hv hv)
/-
  let D:= fgSafetyProgressDeadline S rho rGST gap delayExtra
  have hDpred: D ≤ q - 1:= Nat.le_sub_of_add_le
    ((Nat.add_le_add_left (by decide: 1 ≤ 2) D).trans
      (by simpa only [D] using hq))
  have hqPos: 0 < q:= lt_of_lt_of_le Nat.zero_lt_two
    ((Nat.le_add_left 2 D).trans (by simpa only [D] using hq))
  have hpred: q - 1 + 1 = q:=
    Nat.sub_add_cancel (Nat.succ_le_iff.mpr hqPos)
  have hdHor: Protocol.vote_time S.E
      (S.hc.opening_slot (q + 1) + 1) + S.E.Δ ≤ rho.horizon:= by
    rw [vote_time_succ_add_delta_eq_confirmation_time,
      opening_confirmation_time_eq_action]
    exact hrHor
  have hopenQD: S.hc.opening_slot q + 1 ≤
      S.hc.opening_slot (q + 1) + 1:=
    (postGain_openingSlot_succ_lt_next S q).le.trans (Nat.le_succ _)
  exact Block.preceq_trans (hcover v hv)
    (actionSGBlock_preceq_voterHeadAt_after_GST
      S adm hcom hbelow hrec hdelay hpost
        (c:= q - 1) (by simpa only [D] using hDpred)
        (by simpa only [hpred] using hopenQD) hdHor hv hv)
-/

set_option maxHeartbeats 400000 in
private theorem postGain_root_below_consuming_head
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {q : Round} (hq :
      fgSafetyProgressDeadline S rho rGST gap delayExtra + 2 ≤ q)
    (hrHor : S.a (q + 1) ≤ rho.horizon)
    {v : V} (hv : v ∈ rho.honest) :
    let o := S.hc.opening_slot (q + 1)
    let d := o + 1
    let t := Protocol.confirmation_time S.E o
    Block.Preceq
      (Protocol.get_fg_root
        (rho.stateBeforeTime S t v).st.core.toHealing.toFG)
      (voterHeadAt S rho v d) := by
  let D := fgSafetyProgressDeadline S rho rGST gap delayExtra
  let o : Slot := S.hc.opening_slot (q + 1)
  let d : Slot := o + 1
  let t : Time := Protocol.confirmation_time S.E o
  have htAction : t = S.a (q + 1) := by
    simpa only [t, o] using opening_confirmation_time_eq_action S (q + 1)
  have htHor : t ≤ rho.horizon := by simpa only [htAction] using hrHor
  have hDq : D ≤ q := (Nat.le_add_right D 2).trans (by simpa only [D] using hq)
  have hreadLo : S.a D ≤ t := by
    rw [htAction]
    exact Assembly.a_mono S (hDq.trans (Nat.le_succ q))
  have hslotLo : S.hc.opening_slot D + 1 ≤ d :=
    (postGain_openingSlot_succ_le_of_lt S
      (lt_of_le_of_lt hDq (Nat.lt_succ_self q))).trans (by
        simp only [d, o]
        exact Nat.le_succ _)
  have htNextVote : t ≤ Protocol.vote_time S.E (d + 1) :=
    (by
      dsimp only [t, d]
      rw [Protocol.confirmation_time_eq_support_cutoff_succ]
      exact support_cutoff_le_vote_time_succ S.E (o + 1))
  have hdHor : Protocol.vote_time S.E d + S.E.Δ ≤ rho.horizon := by
    dsimp only [d, o, t]
    rw [vote_time_succ_add_delta_eq_confirmation_time]
    exact htHor
  exact fgRoot_preceq_previousHead_after_GST
    S adm hcom hbelow hrec hdelay hpost hreadLo htHor hslotLo
      htNextVote hdHor hv hv

set_option maxHeartbeats 400000 in
private theorem postGain_consuming_head_body
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {q : Round} (hrHor : S.a (q + 1) ≤ rho.horizon)
    {v : V} (hv : v ∈ rho.honest) :
    let o := S.hc.opening_slot (q + 1)
    let d := o + 1
    let t := Protocol.confirmation_time S.E o
    ∃ Hn : NamedBlock V,
      Hn ∈ (rho.stateBeforeTime S t v).st.bodies ∧
      RunBlock S rho Hn ∧ Hn.erase = voterHeadAt S rho v d := by
  let o : Slot := S.hc.opening_slot (q + 1)
  let d : Slot := o + 1
  let t : Time := Protocol.confirmation_time S.E o
  have htHor : t ≤ rho.horizon := by
    simpa only [t, o, opening_confirmation_time_eq_action] using hrHor
  have hvoteLe : Protocol.vote_time S.E d ≤ t := by
    dsimp only [t, d, o]
    rw [← vote_time_succ_add_delta_eq_confirmation_time S.E o]
    show Protocol.vote_time S.E (o + 1) ≤
      Protocol.vote_time S.E (o + 1) + S.E.Δ
    exact Int.le_add_of_nonneg_right S.E.Δ_pos.le
  have hHvote : voterHeadAt S rho v d ∈
      (rho.storeBeforeTime S v (Protocol.vote_time S.E d)).T := by
    simpa only [voteDutyHead, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
      Proofs.Optimistic.tickStore] using voteDutyHead_mem_voteDutyStore S adm v d
  have hHmem : voterHeadAt S rho v d ∈
      (rho.stateBeforeTime S t v).st.core.T := by
    change voterHeadAt S rho v d ∈ (rho.storeBeforeTime S v t).T
    rw [storeBeforeTime_eq_stateBefore_strictEventIndex
      S adm.toNamedScheduleWellFormed] at hHvote
    rw [storeBeforeTime_eq_stateBefore_strictEventIndex
      S adm.toNamedScheduleWellFormed]
    exact stateBefore_T_subset S rho v _
      (strictEventIndex_mono rho hvoteLe) hHvote
  obtain ⟨Hn, hHbody, hHerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho t v hHmem
  have hHrun : RunBlock S rho Hn := by
    obtain ⟨i, hi, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix
      S rho adm.toNamedScheduleWellFormed.sorted t
    apply Proofs.Bridges.runBlock_of_stateBefore_mem S hv (i := i)
    exact (congrArg (fun w => Hn ∈ (w v).st.bodies) hi).mp hHbody
  exact ⟨Hn, hHbody, hHrun, hHerase⟩

set_option maxHeartbeats 400000 in
private theorem postGain_proposal_viable_at_consuming_read
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {q : Round} {P : NamedBlock V} (hq :
      fgSafetyProgressDeadline S rho rGST gap delayExtra + 2 ≤ q)
    (hrHor : S.a (q + 1) ≤ rho.horizon)
    (hcover : ActionCarriersCover S rho q P.erase)
    {v : V} (hv : v ∈ rho.honest) :
    let o := S.hc.opening_slot (q + 1)
    let t := Protocol.confirmation_time S.E o
    P.erase ∈ (rho.stateBeforeTime S t v).st.core.T ∧
      Protocol.viable
        (rho.stateBeforeTime S t v).st.core.σ
        (rho.stateBeforeTime S t v).st.core.h_max
        (rho.stateBeforeTime S t v).st.core.T P.erase = true ∧
      Block.compatible P.erase
        (rho.stateBeforeTime S t v).st.core.F = true ∧
      Block.compatible P.erase
        (Protocol.get_fg_root
          (rho.stateBeforeTime S t v).st.core.toHealing.toFG) = true := by
  classical
  let D := fgSafetyProgressDeadline S rho rGST gap delayExtra
  let r : Round := q + 1
  let o : Slot := S.hc.opening_slot r
  let d : Slot := o + 1
  let t : Time := Protocol.confirmation_time S.E o
  have htAction : t = S.a r := by
    simpa only [t, o, r] using opening_confirmation_time_eq_action S r
  have htHor : t ≤ rho.horizon := by simpa only [htAction, r] using hrHor
  have hDq : D ≤ q := (Nat.le_add_right D 2).trans (by simpa only [D] using hq)
  have hPhead := postGain_proposal_below_consuming_head
    S adm hcom hbelow hrec hdelay hpost hq hrHor hcover hv
  have hrootHead := postGain_root_below_consuming_head
    S adm hcom hbelow hrec hdelay hpost hq hrHor hv
  dsimp only at hrootHead
  obtain ⟨Hn, hHbody, hHrun, hHerase⟩ :=
    postGain_consuming_head_body S adm hrHor hv
  rw [← hHerase] at hPhead hrootHead
  have hreadLo : S.a D ≤ t := by
    rw [htAction]
    exact Assembly.a_mono S (hDq.trans (Nat.le_succ q))
  have hslotLo : S.hc.opening_slot D + 1 ≤ d :=
    (postGain_openingSlot_succ_le_of_lt S
      (lt_of_le_of_lt hDq (Nat.lt_succ_self q))).trans (by
        simp only [d, o, r]
        exact Nat.le_succ _)
  have hdHor : Protocol.vote_time S.E d + S.E.Δ ≤ rho.horizon := by
    dsimp only [d, o, t]
    rw [vote_time_succ_add_delta_eq_confirmation_time]
    exact htHor
  have hconfD : t ≤ Protocol.confirmation_time S.E d := by
    dsimp only [t]
    rw [Protocol.confirmation_time_eq_support_cutoff_succ,
      Protocol.confirmation_time_eq_support_cutoff_succ]
    exact support_cutoff_mono S.E (Nat.add_le_add_right (Nat.le_succ o) 1)
  obtain ⟨T, hTrun, hTband, hTheads⟩ :=
    exists_namedCommonPreviousHeadAncestor_in_frontierBand_through_confirmation_after_GST
      S adm hcom hbelow hrec hdelay hpost hreadLo htHor hslotLo
        hconfD hdHor hv
  have hTH : Block.Preceq T.erase Hn.erase := by
    rw [hHerase]
    exact hTheads v hv
  have hTHn : NamedBlock.Preceq T Hn :=
    postGain_namedPreceq_of_runBlocks adm.toNamedRootCollisionFree
      hTrun hHrun hTH
  have hHband : (rho.stateBeforeTime S t v).st.core.h_max - 1 ≤
      (Protocol.derive_named S.E S.cfg Hn).h :=
    hTband.trans (Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hTHn)
  have hSigmaH : (rho.stateBeforeTime S t v).st.core.σ Hn.erase =
      Protocol.derive_named S.E S.cfg Hn :=
    Proofs.NamedStoreBridge.derivedView_stateBeforeTime S rho t v Hn hHbody
  have hHmem : Hn.erase ∈ (rho.stateBeforeTime S t v).st.core.T := by
    have hcoh := (Proofs.NamedRuntime.stateBeforeTime_invariants S rho t v).1.1.1
    rw [hcoh.1]
    exact Finset.mem_image_of_mem NamedBlock.erase hHbody
  have hPmem : P.erase ∈ (rho.stateBeforeTime S t v).st.core.T :=
    Proofs.Records.mem_of_preceq
      ((parentClosed_iff _).mp
        (Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho t v)).2
      P.erase Hn.erase hHmem hPhead
  have hPviable : Protocol.viable
      (rho.stateBeforeTime S t v).st.core.σ
      (rho.stateBeforeTime S t v).st.core.h_max
      (rho.stateBeforeTime S t v).st.core.T P.erase = true := by
    simp only [Protocol.viable, decide_eq_true_eq]
    refine ⟨Hn.erase, hHmem, hPhead, ?_⟩
    rw [hSigmaH]
    exact hHband
  have hFroot := StoreFinality.finalized_preceq_fgRoot
    (Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime S rho t v)
  exact ⟨hPmem, hPviable,
    Block.compatible_of_preceq_common hPhead
      (Block.preceq_trans hFroot hrootHead),
    Block.compatible_of_preceq_common hPhead hrootHead⟩

set_option maxHeartbeats 400000 in
/-- At a fixed strict post-gain carrier, every honest opening-confirmation
stable write in the successor round is strictly above the previous frontier. -/
theorem postGainOpeningWrite_high_at_node
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {m q : Round} {P : NamedBlock V}
    (hq : fgSafetyProgressDeadline S rho rGST gap delayExtra + 2 ≤ q)
    (hqm : q + 1 < m) (hcarrier : ProposerCarrierAt S rho q)
    (hP : proposedBlockAt S rho (S.hc.opening_slot q) = some P)
    (hcap : honestHMaxAt S rho
        (S.a (fgSafetyProgressDeadline S rho rGST gap delayExtra)) <
      (Protocol.derive_named S.E S.cfg P).h)
    (hhor : Protocol.confirmation_time S.E
      (S.hc.opening_slot m) ≤ rho.horizon) :
    ∀ v ∈ rho.honest, ∃ (G : Block V) (Gn : NamedBlock V),
      DecoupledConsensusModel.Protocol.frameStableRoot
          (confirmationInputRead S rho v (S.hc.opening_slot (q + 1))).cache
          S.E S.hc
          (confirmationInputRead S rho v
            (S.hc.opening_slot (q + 1))).st.core.toHealing
          (S.hc.round_of (S.E.slotOf (Protocol.confirmation_time S.E
            (S.hc.opening_slot (q + 1))))) = some G ∧
        Gn.erase = G ∧ RunBlock S rho Gn ∧
        honestHMaxAt S rho
            (S.a (fgSafetyProgressDeadline S rho rGST gap delayExtra)) <
          (Protocol.derive_named S.E S.cfg Gn).h := by
  classical
  let D := fgSafetyProgressDeadline S rho rGST gap delayExtra
  let r : Round := q + 1
  let o : Slot := S.hc.opening_slot r
  let t : Time := Protocol.confirmation_time S.E o
  have hmAction : S.a m ≤ rho.horizon := by
    simpa only [opening_confirmation_time_eq_action] using hhor
  have hrHor : S.a r ≤ rho.horizon :=
    (Assembly.a_mono S (by dsimp only [r]; exact Nat.le_of_lt hqm)).trans hmAction
  have hdomainHor : domain S.E S.hc r .g2 ≤ rho.horizon :=
    (FrameForward.domain_le_a S r .g2).trans hrHor
  have hDq : D ≤ q := (Nat.le_add_right D 2).trans (by simpa only [D] using hq)
  have hpostQ : S.E.t_GST ≤ S.a q :=
    hpost.trans (Assembly.a_mono S (by
      have hGSTdead : rGST ≤ D := by
        dsimp only [D]
        unfold fgSafetyProgressDeadline
        exact (Nat.le_add_right rGST 1).trans
          (Nat.le_add_right (rGST + 1) _)
      exact hGSTdead.trans hDq))
  have hwindow : RelativeCarrierWindowAt S rho q .g2 :=
    relativeCarrierWindowAt_after_recovery_deadline
      S adm hcom hbelow hrec hdelay hpost (by simpa only [D] using hDq)
        (by simpa only [r] using hdomainHor)
  have hforming : Internal.NamedOutageEntry.GradeFormingMajority S rho r :=
    gradeFormingMajority_of_admissible_belowOneThird
      S adm hbelow (by dsimp only [r]; exact Nat.succ_pos q) hdomainHor
      (by simpa only [r, Nat.add_sub_cancel] using hpostQ)
  have hcover : ActionCarriersCover S rho q P.erase :=
    honestProposal_actionCover_after_SG_healing_named
      S adm hcom hbelow hrec hdelay hpost hq hcarrier hP
        (by
          simpa only [opening_confirmation_time_eq_action] using
            ((Assembly.a_mono S (Nat.le_succ q)).trans hrHor))
  have hqPos : 0 < q := lt_of_lt_of_le Nat.zero_lt_two
    ((Nat.le_add_left 2 D).trans (by simpa only [D] using hq))
  have hqActionHor : S.a q ≤ rho.horizon :=
    (Assembly.a_mono S (Nat.le_succ q)).trans hrHor
  have hPrun : RunBlock S rho P :=
    proposedBlockAt_blockInRun_of_admissible S adm.toNamedAdmissibleCore
      (S.hc.opening_slot q)
      (by
        unfold Protocol.HealConfig.opening_slot
        exact Nat.mul_pos hqPos
          (lt_of_lt_of_le Nat.zero_lt_two S.hc.R_ge_two))
      hcarrier.1
      ((proposal_time_lt_vote_time S.E _).le.trans (by
        apply (vote_time_le_confirmation_time S.E _).trans
        simpa only [opening_confirmation_time_eq_action] using hqActionHor)) hP
  intro v hv
  obtain ⟨raw, R2, hfreeze, hg2, hR2eq, hPraw⟩ :=
    postGain_localFrameRoot_above_proposal S adm hcom hv hpostQ
      (by simpa only [r] using hdomainHor) hwindow
      (by simpa only [r] using hforming) hcover
  obtain ⟨hPmem, hPviable, hPFCompat, hProotCompat⟩ :=
    postGain_proposal_viable_at_consuming_read
      S adm hcom hbelow hrec hdelay hpost hq hrHor hcover hv
  have hPR2 : Block.Preceq P.erase R2 := by
    rw [hR2eq]
    exact (NamedOutageClosure.q10_retained_prefix raw
      (NamedRun.stateBeforeTime S rho t v).st.core.F P.erase
        (by simpa only [t, o, r] using hPFCompat)).mpr hPraw
  have hrawBind :
      (DecoupledConsensusModel.Protocol.readFrame
        (confirmationInputRead S rho v o).cache
        (confirmationInputRead S rho v o).st.core.toHealing r).g2.bind id =
          some R2 := by rw [hg2]; rfl
  have hstable := postGain_frameStableRoot_of_high_viable_prefix
    S adm hv (t := t) (r := r)
      (cap := honestHMaxAt S rho (S.a D))
      (Q := P.erase) (R2 := R2) (Qn := P)
      (by simpa only [confirmationInputRead, o, t] using hrawBind)
      hPR2 rfl hPrun
      (by simpa only [t, o, r] using hPmem)
      (by simpa only [t, o, r] using hPviable)
      (by simpa only [t, o, r] using hProotCompat)
      (by simpa only [D] using hcap)
  have hround : S.hc.round_of
      (S.E.slotOf (Protocol.confirmation_time S.E o)) = r := by
    rw [show Protocol.confirmation_time S.E o = S.a r by
      simpa only [o] using opening_confirmation_time_eq_action S r]
    exact Proofs.HealingLemmas.round_of_slotOf_a S r
  simpa only [t, o, r, hround] using hstable



#print axioms postGainOpeningWrite_high_at_node

/-- A high stable write occurs at every honest node before the later carrier
round used by the post-recovery consumer. -/
theorem exists_highOpeningStableWrite_before_postRecoveryCarrier
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest) (hbelow : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra) (hpost : S.E.t_GST ≤ S.a rGST)
    {m : Round}
    (hm : fgSafetyProgressDeadline S rho rGST gap delayExtra +
        2 * progressLag' gap delayExtra +
        max (1 + S.hc.η_SG) (gap + 3) ≤ m)
    (hhor : Protocol.confirmation_time S.E
      (S.hc.opening_slot m) ≤ rho.horizon) :
    ∃ q : Round,
      fgSafetyProgressDeadline S rho rGST gap delayExtra +
          2 * progressLag' gap delayExtra + 1 ≤ q ∧
      q ≤ fgSafetyProgressDeadline S rho rGST gap delayExtra +
          2 * progressLag' gap delayExtra + 1 + gap ∧
      q + 1 < m ∧
      ∀ v ∈ rho.honest, ∃ (G : Block V) (Gn : NamedBlock V),
        DecoupledConsensusModel.Protocol.frameStableRoot
          (confirmationInputRead S rho v (S.hc.opening_slot (q + 1))).cache
          S.E S.hc
          (confirmationInputRead S rho v
            (S.hc.opening_slot (q + 1))).st.core.toHealing
          (S.hc.round_of (S.E.slotOf (Protocol.confirmation_time S.E
            (S.hc.opening_slot (q + 1))))) = some G ∧
        Gn.erase = G ∧ RunBlock S rho Gn ∧
        honestHMaxAt S rho
            (S.a (fgSafetyProgressDeadline S rho rGST gap delayExtra)) <
          (Protocol.derive_named S.E S.cfg Gn).h := by
  obtain ⟨q, P, hqlo, hqhi, hqm, hcarrier, hP, hcap⟩ :=
    exists_postGain_carrier_height_r270
      S adm hcom hbelow hrec hdelay hpost hm hhor
  have hLpos : 1 ≤ progressLag' gap delayExtra := progressLag'_pos gap
  have hq : fgSafetyProgressDeadline S rho rGST gap delayExtra + 2 ≤ q := by
    have htwo : 2 ≤ 2 * progressLag' gap delayExtra + 1 := by
      have hmul : 2 ≤ 2 * progressLag' gap delayExtra := by
        simpa only [Nat.mul_one] using Nat.mul_le_mul_left 2 hLpos
      exact hmul.trans (Nat.le_succ _)
    exact (Nat.add_le_add_left htwo _).trans hqlo
  refine ⟨q, hqlo, hqhi, hqm, ?_⟩
  exact postGainOpeningWrite_high_at_node
    S adm hcom hbelow hrec hdelay hpost hq hqm hcarrier hP hcap hhor

#print axioms exists_highOpeningStableWrite_before_postRecoveryCarrier





end HealingSurface
end Proofs
end DecoupledConsensusModel

end
