module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SGProposalLifecycle
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SGTargetCanonicality
public import DecoupledConsensusProofs.Protocol.Grades.RecoveryG1AfterCutoffReflection
public import DecoupledConsensusProofs.Protocol.Store.RecoveryG1AfterCutoffPersistence
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge

@[expose] public section

/-!
# Vote-duty grade transport

This module transports a common action-read grade to any vote duty in the
same round. It also bounds the two branches of the integrated SG anchor during
a proposal lifecycle. The fresh branch uses the fixed grade-one cutoff. The
relative-majority branch uses the exact previous honest action votes.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol
open Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]


/-
/-- A common grade at the action read gives grade one at every honest vote
duty in the same round. The proof covers vote reads on both sides of the
action read because grade one is fixed after `Gamma[0]`. -/
theorem g1_at_voteDuty_of_gradeFormsAt
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    {r: Round} {B: Block V} (hforms: GradeFormsAt S rho r B)
    {s: Slot} (hround: S.hc.round_of s = r)
    {v: V} (hv: v ∈ rho.honest):
    Protocol.G1 S.E
      (Proofs.Optimistic.voteDutyStore S rho v s).toHealing.gradeView S.hc r B = true:= by
  let read:= Protocol.vote_time S.E s
  have hG1Action: Protocol.G1 S.E (gradeViewAt S rho v r)
      S.hc r B = true:=
    G2_imp_G1 S.E (gradeViewAt S rho v r) S.hc r B (hforms v hv).2
  have hcut: S.hc.Γ_0 S.E.Δ r ≤ read:= by
    simpa only [read] using Γ_0_le_vote_time_of_round_eq S hround
  have hG1Read: Protocol.G1 S.E
      (rho.storeBeforeTime S v read).toHealing.gradeView S.hc r B = true:= by
    rcases le_total read (S.a r) with hbefore | hafter
    · have hG1AtAction: Protocol.G1 S.E
          (rho.storeBeforeTime S v (S.a r)).toHealing.gradeView
          S.hc r B = true:= by
        simpa only [gradeViewAt, healStoreAt] using hG1Action
      exact G1_reflects_after_cutoff S adm hv hcut hbefore hG1AtAction
    · exact G1_persists_from_opening S adm hv hafter hG1Action
  simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
    Proofs.Optimistic.tickStore, read] using hG1Read
 -/

/-
/-- If the common graded block is still in the duty filtered tree, the actual
integrated anchor extends it. The grade-one candidate makes the fallback
branch impossible. -/
theorem gradeFormsAt_preceq_voteDutyAnchor_of_active
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    {r: Round} {B: Block V} (hforms: GradeFormsAt S rho r B)
    {s: Slot} (hround: S.hc.round_of s = r)
    {v: V} (hv: v ∈ rho.honest)
    (hactive: B ∈ Protocol.get_filtered_block_tree
      (Proofs.Optimistic.voteDutyStore S rho v s).toHealing.toFG):
    Block.Preceq B
      (Proofs.Optimistic.healAnchor S.E S.hc
        (Proofs.Optimistic.voteDutyStore S rho v s).toHealing):= by
  let duty:= Proofs.Optimistic.voteDutyStore S rho v s
  have hG1: Protocol.G1 S.E duty.toHealing.gradeView S.hc r B = true:= by
    simpa only [duty] using
      g1_at_voteDuty_of_gradeFormsAt S adm hforms hround hv
  have hsome:= fresh_anchor_isSome_of_G1 S.E
    (by simpa only [duty] using hactive) hG1
  obtain ⟨A, hA⟩:= Option.isSome_iff_exists.mp hsome
  have hBA: Block.Preceq B A:= by
    refine deepest?_dominates hA (Finset.mem_filter.mpr ⟨?_, hG1⟩) ?_
    · simpa only [duty] using hactive
    · exact G1_compatible S.E hG1
        (Finset.mem_filter.mp (Proofs.Engine.deepest?_mem hA)).2
  change Block.Preceq B (Proofs.Optimistic.healAnchor S.E S.hc duty.toHealing)
  rw [Proofs.Optimistic.healAnchor_eq_get_sg_root]
  have hroundDuty: S.hc.round_of duty.toHealing.s = r:= by
    rw [show duty.toHealing.s = s by
      simpa only [duty, Proofs.Optimistic.toHealing_slot] using
        Proofs.Optimistic.voteDutyStore_slot S rho v s]
    exact hround
  rw [hroundDuty]
  simp only [Protocol.get_sg_root, hA]
  exact hBA
 -/

/-- At a next-round vote duty, the exact previous honest action votes give
directed relative-SG support once a common upper block is in every honest
reader's tree. -/
theorem voteDutySupportAligned_of_previousActionCeiling
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {r : Round} {s : Slot} {Can : Block V}
    (hround : S.hc.round_of s = r + 1)
    (hpost : S.E.t_GST ≤ S.a r)
    (hcut : S.hc.Γ_neg1 S.E.Δ (r + 1) ≤ rho.horizon)
    (hcanMem : ∀ w ∈ rho.honest,
      Can ∈ (Proofs.Optimistic.voteDutyStore S rho w s).T)
    (hupper : ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u r) Can) :
    ∀ w ∈ rho.honest,
      Proofs.Optimistic.SupportAligned
        (Proofs.Optimistic.voteDutyStore S rho w s).toHealing.sg_votes S.hc.η_SG
        (Proofs.Optimistic.voteDutyStore S rho w s).T rho.honest (r + 1) Can := by
  intro w hw
  let B := Can
  let duty := Proofs.Optimistic.voteDutyStore S rho w s
  let pre := (rho.storeBeforeTime S w (Protocol.vote_time S.E s)).core
  have hsg : duty.toHealing.sg_votes = pre.toHealing.sg_votes := by
    rfl
  have hT : duty.T = pre.T := by
    rfl
  have hread : S.hc.Γ_0 S.E.Δ (r + 1) ≤ Protocol.vote_time S.E s :=
    Γ_0_le_vote_time_of_round_eq S hround
  have hrelay : ∀ v ∈ rho.honest,
      actionSGVoteAt S rho v r ∈ duty.toHealing.sg_votes r := by
    intro v hv
    exact (actionSGVote_mem_stamp_voteDuty S adm hpost hcut hread hw hv).1
  refine ⟨?_, ?_⟩
  · intro v hv
    have hwindow : r ∈ Protocol.latest_window S.hc.η_SG (r + 1) := by
      simpa only [Nat.add_sub_cancel] using
        (Protocol.pred_mem_latest_window S.hc.η_SG (r + 1)
          S.hc.η_SG_ge_one (Nat.succ_pos r))
    exact Protocol.represented_of_vote_mem hwindow (hrelay v hv) rfl
  · intro v hv u hlatest
    let C := actionSGBlockAt S rho v r
    have hpcPre : ParentClosed pre := by
      simpa only [pre, Run.storeBeforeTime] using
        Proofs.NamedStoreBridge.parentClosed_stateBeforeTime S rho
          (Protocol.vote_time S.E s) w
    have hpc : ParentClosed duty := by
      rw [parentClosed_iff] at hpcPre ⊢
      simpa only [duty, Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
        Proofs.Optimistic.tickStore] using hpcPre
    have hBmem : B ∈ duty.T := by
      simpa only [B, duty] using hcanMem w hw
    have hCsource : C ∈ (rho.storeBeforeTime S v (S.a r)).T := by
      simpa only [C] using actionSGBlockAt_mem_storeBeforeTime S rho v r
    obtain ⟨C', hCerase, hCrun⟩ :=
      Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
        adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hv (S.a r)
        hCsource
    have hCB : Block.Preceq C B := by
      simpa only [C, B] using hupper v hv
    have hCmem : C ∈ duty.T :=
      Proofs.Records.mem_of_preceq ((parentClosed_iff duty).mp hpc).2 C B hBmem hCB
    have hfind : Block.find? duty.T C.root = some C := by
      apply Proofs.Optimistic.find?_eq_some_of_unique hCmem
      intro X hX hroot
      have hXpre : X ∈ pre.T := by
        rw [← hT]
        exact hX
      obtain ⟨X', hXerase, hXrun⟩ :=
        Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
          adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hw
          (Protocol.vote_time S.E s) hXpre
      have hroot' : X'.root = C'.root := by
        rw [← Proofs.NamedWire.erase_root X', ← Proofs.NamedWire.erase_root C',
          hXerase, hCerase]
        exact hroot
      have hnamedEq :=
        adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective
          X' C' hXrun hCrun X' C'
          (Or.inl (Proofs.NamedAncestry.named_self X'))
          (Or.inr (Proofs.NamedAncestry.named_self C')) hroot'
      calc
        X = X'.erase := hXerase.symm
        _ = C'.erase := congrArg NamedBlock.erase hnamedEq
        _ = C := hCerase
    have hresolved : Protocol.holds_resolved_vote_by
        duty.T (duty.toHealing.sg_votes r) v = true := by
      unfold Protocol.holds_resolved_vote_by
      rw [decide_eq_true_eq]
      apply Finset.card_pos.mpr
      refine ⟨actionSGVoteAt S rho v r, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
      · exact Finset.mem_filter.mpr ⟨hrelay v hv, by rfl⟩
      · change (Block.find? duty.T C.root).isSome = true
        rw [hfind]
        rfl
    have hetaPos : 0 < S.hc.η_SG :=
      Nat.succ_le_iff.mp S.hc.η_SG_ge_one
    have hlenPos : 0 < min (r + 1) S.hc.η_SG :=
      Nat.lt_min.mpr ⟨Nat.succ_pos r, hetaPos⟩
    have hlen : min (r + 1) S.hc.η_SG =
        min (r + 1) S.hc.η_SG - 1 + 1 := by
      exact (Nat.sub_add_cancel
        (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hlenPos))).symm
    have hlast : (r + 1 - S.hc.η_SG) +
        (min (r + 1) S.hc.η_SG - 1) = r := by
      by_cases hle : S.hc.η_SG ≤ r + 1
      · rw [Nat.min_eq_right hle]
        have hsucc : ((r + 1 - S.hc.η_SG) +
            (S.hc.η_SG - 1)) + 1 = r + 1 := by
          calc
            ((r + 1 - S.hc.η_SG) + (S.hc.η_SG - 1)) + 1 =
                (r + 1 - S.hc.η_SG) +
                  ((S.hc.η_SG - 1) + 1) := Nat.add_assoc _ _ _
            _ = (r + 1 - S.hc.η_SG) + S.hc.η_SG := by
              rw [Nat.sub_add_cancel S.hc.η_SG_ge_one]
            _ = r + 1 := Nat.sub_add_cancel hle
        exact Nat.succ.inj (by
          simpa only [Nat.succ_eq_add_one] using hsucc)
      · have hle' : r + 1 ≤ S.hc.η_SG := Nat.le_of_not_ge hle
        rw [Nat.min_eq_left hle', Nat.sub_eq_zero_of_le hle',
          Nat.zero_add, Nat.add_sub_cancel]
    have hwindow : Protocol.latest_window S.hc.η_SG (r + 1) =
        List.range' (r + 1 - S.hc.η_SG)
          (min (r + 1) S.hc.η_SG - 1) ++ [r] := by
      unfold Protocol.latest_window
      calc
        List.range' (r + 1 - S.hc.η_SG) (min (r + 1) S.hc.η_SG) =
            List.range' (r + 1 - S.hc.η_SG)
              (min (r + 1) S.hc.η_SG - 1 + 1) :=
          congrArg (List.range' (r + 1 - S.hc.η_SG)) hlen
        _ = List.range' (r + 1 - S.hc.η_SG)
              (min (r + 1) S.hc.η_SG - 1) ++
            [r + 1 - S.hc.η_SG +
              (min (r + 1) S.hc.η_SG - 1)] := by
          simpa only [Nat.one_mul] using
            (List.range'_concat (s := r + 1 - S.hc.η_SG)
              (n := min (r + 1) S.hc.η_SG - 1) (step := 1))
        _ = List.range' (r + 1 - S.hc.η_SG)
              (min (r + 1) S.hc.η_SG - 1) ++ [r] := by
          rw [hlast]
    have hlatestRound : Protocol.latest_support_round
        duty.toHealing.sg_votes S.hc.η_SG duty.T v (r + 1) = some r := by
      unfold Protocol.latest_support_round
      rw [hwindow, List.filter_append]
      simp [hresolved]
    have hsole : Protocol.sole_vote? (duty.toHealing.sg_votes r) v = some u := by
      unfold Protocol.latest_support_vote at hlatest
      rw [hlatestRound] at hlatest
      exact hlatest
    obtain ⟨hu, huv⟩ := Protocol.sole_vote_mem_and_author hsole
    have huPre : u ∈ pre.toHealing.sg_votes r := by
      rw [← hsg]
      exact hu
    have hactionPre : actionSGVoteAt S rho v r ∈ pre.toHealing.sg_votes r := by
      rw [← hsg]
      exact hrelay v hv
    have huState : u ∈
        (rho.stateBeforeTime S (Protocol.vote_time S.E s) w).st.toHealing.sg_votes r := by
      simpa only [pre, Run.storeBeforeTime] using huPre
    have hactionState : actionSGVoteAt S rho v r ∈
        (rho.stateBeforeTime S (Protocol.vote_time S.E s) w).st.toHealing.sg_votes r := by
      simpa only [pre, Run.storeBeforeTime] using hactionPre
    have huEq : u = actionSGVoteAt S rho v r :=
      Protocol.honest_sgVote_unique_stateBeforeTime S adm hv
        huState hactionState huv (by rfl)
    rw [huEq]
    change Proofs.Optimistic.rootOnCan duty.T B (some C.root) = true
    simp only [Proofs.Optimistic.rootOnCan, hfind]
    exact hCB




#print axioms voteDutySupportAligned_of_previousActionCeiling

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
