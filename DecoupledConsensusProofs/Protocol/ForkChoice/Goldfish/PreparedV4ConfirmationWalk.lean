module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.PreparedV4ActionSourcesCore
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.WeakConfirmationWalkFactsNamed

@[expose] public section

/-! # Prepared V4 named confirmation walk -/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Protocol Proofs.Optimistic Proofs.HealingLemmas Statements

variable {V : Type} [DecidableEq V] [Fintype V]

namespace PreparedV4Confirmation

private theorem confirmationWalkWith_of_twoCones
    (contract : Protocol.GradeContract V)
    (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.Store V)
    (s : Slot) (Hon : Finset V) {B : Block V}
    (hB : ConeSupport E st.T (confVotes E st s) (confVotes E st s)
      (confLate E st s) s Hon (fun X => Block.Preceq B X))
    (hA : ConeSupport E st.T (confVotes E st s) (confVotes E st s)
      (confLate E st s) s Hon
        (fun X => Block.Preceq (confAnchorWith contract E hc st) X))
    (hvalid : Protocol.VoteSetValid E s (confLate E st s))
    (hcompat : Block.compatible (confAnchorWith contract E hc st) B = true)
    (hpath : Block.Preceq (confAnchorWith contract E hc st) B →
      ∀ C, Block.Preceq (confAnchorWith contract E hc st) C →
        C ≠ confAnchorWith contract E hc st →
        Block.Preceq C B → C ∈ confTree st) :
    Block.Preceq B (confWalkWith contract E hc st s) ∧
      confEligible E st s (confWalkWith contract E hc st s) = true := by
  have hanchorEligible :
      confEligible E st s (confAnchorWith contract E hc st) = true := by
    simp only [confEligible, decide_eq_true_eq, confCount, confScore]
    exact hA.eligible hvalid (fun _ h => h)
  have helig : confEligible E st s
      (confWalkWith contract E hc st s) = true := by
    rcases ghost_eligible (confAnchorWith contract E hc st)
        (confTree st) (confScore E st s) (confEligible E st s) with
      hwalk | helig
    · have hwalk' : confWalkWith contract E hc st s =
          confAnchorWith contract E hc st := by
        simpa only [confWalkWith] using hwalk
      rw [hwalk']
      exact hanchorEligible
    · exact helig
  refine ⟨?_, helig⟩
  have hor : Block.Preceq (confAnchorWith contract E hc st) B ∨
      Block.Preceq B (confAnchorWith contract E hc st) := by
    simpa only [Block.compatible, Bool.or_eq_true] using hcompat
  rcases hor with hAB | hBA
  · exact ghost_passes_cone E st.T (confTree st)
      (confVotes E st s) (confVotes E st s) (confLate E st s)
      s Hon hB hvalid hAB (hpath hAB)
  · exact Block.preceq_trans hBA (ghost_preceq _ _ _ _)

private theorem coneSupport_confVotes_afterGST
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {s : Slot} (hs : 0 < s)
    (hpost : S.E.t_GST ≤ Protocol.vote_time S.E s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    {tgt : Block V → Prop} (hnames : NamedHonestVotesCone S rho s tgt)
    {v : V} (hv : v ∈ rho.honest)
    (hres : HeadsResolveIn S rho s (confStore S rho v s).T
      (confStore S rho v s).timestamp_block) :
    ConeSupport S.E (confStore S rho v s).T
      (confVotes S.E (confStore S rho v s) s)
      (confVotes S.E (confStore S rho v s) s)
      (confLate S.E (confStore S rho v s) s) s rho.honest tgt := by
  apply Proofs.Optimistic.coneSupport_confVotes S rho hcom hnames v
  · intro u hus hval hemit harr
    exact WeakGoldfish.canonicalSuffixHonestVoteCounted_core
      S adm hs hpost hhor v hv u hus hval hemit harr
  · exact hres

end PreparedV4Confirmation

namespace Handover

/-- Common honest-head ancestors pass the named prepared confirmation walk. -/
theorem SettledBootstrapPreparedV4.confirmationWalk_core_of_pins
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    {fresh base : Round} {start : Slot} {P : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start P cap)
    (hawake : ∀ r, base + S.hc.η_SG ≤ r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hfinality : FinalizedRootsBelowAtRead S rho cap P.erase)
    (_of_anchor : ∀ {s : Slot}, start ≤ s →
      Protocol.confirmation_time S.E s ≤ rho.horizon →
      ∀ {w x : V}, w ∈ rho.honest → x ∈ rho.honest →
        Block.Preceq
          (namedConfirmationAnchor S
            (Internal.NamedRecoveryRead.confirmationInputRead S rho w s))
          (voterHeadAt S rho x s))
    (_of_band : ∀ {s : Slot}, start ≤ s →
      Protocol.confirmation_time S.E s ≤ rho.horizon →
      ∀ {v x : V}, x ∈ rho.honest →
      ∀ {X : NamedBlock V}, X.erase = voterHeadAt S rho x s →
        NamedRun.blockInRun S rho X →
        (Internal.NamedRecoveryRead.confirmationInputRead S rho v s).st.core.h_max - 1 ≤
          (Protocol.derive_named S.E S.cfg X).h)
    {s : Slot} (hs0 : start ≤ s)
    (hhor : Protocol.confirmation_time S.E s ≤ rho.horizon)
    {v : V} (hv : v ∈ rho.honest) {B : Block V}
    (hheads : ∀ x ∈ rho.honest,
      Block.Preceq B (voterHeadAt S rho x s)) :
    Block.Preceq B
        (namedConfirmationWalk S
          (Internal.NamedRecoveryRead.confirmationInputRead S rho v s) s) ∧
      confirmationEligible S.E
        (Internal.NamedRecoveryRead.confirmationInputRead S rho v s).st.core s
        (namedConfirmationWalk S
          (Internal.NamedRecoveryRead.confirmationInputRead S rho v s) s) = true := by
  let read := Internal.NamedRecoveryRead.confirmationInputRead S rho v s
  let contract := NamedProfile.gradeContract read.cache
  let duty := Proofs.Optimistic.confStore S rho v s
  let A := confAnchorWith contract S.E S.hc duty
  have hcutpos : 0 < base + S.hc.η_SG :=
    (Nat.zero_lt_of_lt S.hc.η_SG_ge_one).trans_le (Nat.le_add_left _ _)
  have hs : 0 < s :=
    (Nat.mul_pos hcutpos
      (lt_of_lt_of_le (by decide : 0 < 2) S.hc.R_ge_two)).trans_le
        (hboot.settled.trans hs0)
  have hvoteHor : Protocol.vote_time S.E s ≤ rho.horizon :=
    (vote_time_le_confirmation_time S.E s).trans hhor
  have hbaseCut : base < base + S.hc.η_SG :=
    Nat.lt_of_succ_le (Nat.add_le_add_left S.hc.η_SG_ge_one base)
  have hpost : S.E.t_GST ≤ Protocol.vote_time S.E s := by
    have ht := action_add_delta_le_openingProposal_of_round_lt S hbaseCut
    exact hboot.basePost.trans
      ((Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans
        ((ht.trans (proposal_time_mono S.E (hboot.settled.trans hs0))).trans
          (proposal_time_lt_vote_time S.E s).le))
  have hanchor : ∀ x ∈ rho.honest,
      Block.Preceq A (voterHeadAt S rho x s) := by
    intro x hx
    have hA := _of_anchor hs0 hhor hv hx
    simpa only [A, contract, duty, read, confAnchorWith,
      namedConfirmationAnchor,
      Proofs.Optimistic.confStore_eq_confirmationInputRead] using hA
  have namedCone (C : Block V)
      (hC : ∀ x ∈ rho.honest,
        Block.Preceq C (voterHeadAt S rho x s)) :
      NamedHonestVotesCone S rho s (fun X => Block.Preceq C X) := by
    intro x hx hxc
    obtain ⟨X, hX, hXrun, hXemit⟩ :=
      WeakGoldfish.voterHead_runBlock_and_emits
        S adm hx hs hxc hvoteHor
    exact ⟨X, by simpa only [hX] using hC x hx, hXrun, hXemit⟩
  have hconeBNames := namedCone B hheads
  have hconeANames := namedCone A hanchor
  have hrootA : Block.Preceq (confRoot duty) A := by
    have hroot := fg_root_preceq_get_sg_root_with_frame
      read.cache S.E S.hc duty.toHealing (S.hc.round_of duty.s)
    simpa only [confRoot, A, contract, duty, read,
      Proofs.Optimistic.confStore_eq_confirmationInputRead] using hroot
  have hresolve : HeadsResolveIn S rho s duty.T duty.timestamp_block := by
    have hr := WeakGoldfish.headsResolveIn_confStore_of_postHealingCone
      S adm hv hpost
        ((support_cutoff_le_confirmation_time S.E s).trans hhor)
        hrootA hconeANames
    simpa only [duty] using hr
  have hconeB := PreparedV4Confirmation.coneSupport_confVotes_afterGST
    S adm hcom hs hpost hhor hconeBNames hv hresolve
  have hconeA := PreparedV4Confirmation.coneSupport_confVotes_afterGST
    S adm hcom hs hpost hhor hconeANames hv hresolve
  obtain ⟨x, hxc, hx, -⟩ := coneSupport_exists_honest_vote hconeB
  obtain ⟨X, hX, hXrun, hXemit⟩ :=
    WeakGoldfish.voterHead_runBlock_and_emits
      S adm hx hs hxc hvoteHor
  have hXhead : X.erase = voterHeadAt S rho x s := hX
  obtain ⟨hfind, -⟩ := hresolve X.erase
    ⟨x, hx, hxc, ⟨X, rfl, hXrun⟩, hXemit⟩
  have hXmem : X.erase ∈ duty.T := find?_mem hfind
  obtain ⟨X', hX'body, hX'erase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho
      (Protocol.confirmation_time S.E s) v (by
        simpa only [duty, Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore] using hXmem)
  obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore
    S adm.toNamedScheduleWellFormed (Protocol.confirmation_time S.E s)
  have hX'prefix : X' ∈ (rho.stateBefore S n v).st.bodies := by
    rw [← congrArg (fun world => (world v).st.bodies) hn]
    exact hX'body
  have hX'run : NamedRun.blockInRun S rho X' :=
    Proofs.Bridges.runBlock_of_stateBefore_mem S hv hX'prefix
  have hX'eq : X' = X := by
    apply adm.toNamedRootCollisionFree.root_injective
      X' X hX'run hXrun X' X
      (Or.inl (Proofs.NamedAncestry.named_self X'))
      (Or.inr (Proofs.NamedAncestry.named_self X))
    rw [← Proofs.NamedWire.erase_root X', ← Proofs.NamedWire.erase_root X, hX'erase]
  have hXbody : X ∈ (rho.stateBeforeTime S
      (Protocol.confirmation_time S.E s) v).st.bodies := by
    rw [← hX'eq]
    exact hX'body
  have hXview : duty.σ X.erase =
      Protocol.derive_named S.E S.cfg X := by
    simpa only [duty, Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore] using
      Proofs.NamedStoreBridge.derivedView_stateBeforeTime S rho
        (Protocol.confirmation_time S.E s) v X hXbody
  have hFJ : Block.Preceq duty.F duty.J := by
    simpa only [duty, Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore] using
      Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime
        S rho (Protocol.confirmation_time S.E s) v
  have hrootX : Block.Preceq (confRoot duty) X.erase :=
    Block.preceq_trans hrootA (by rw [hX]; exact hanchor x hx)
  have hFX : Block.Preceq duty.F X.erase :=
    Block.preceq_trans
      (Proofs.Records.preceq_get_fg_root_of_F (st := duty.toHealing.toFG) hFJ)
      (by simpa only [confRoot] using hrootX)
  have hheight : duty.h_max - 1 ≤ (duty.σ X.erase).h := by
    rw [hXview]
    have hband := _of_band hs0 hhor
      (v := v) (x := x) hx (X := X) hXhead hXrun
    simpa only [duty, Proofs.Optimistic.confStore_eq_confirmationInputRead] using hband
  have hcandidate : X.erase ∈ confTree duty := by
    simp only [confTree, Protocol.get_filtered_block_tree,
      Protocol.get_filtered_block_tree_from, Protocol.viable_tree,
      Protocol.finalized_descendants, Protocol.viable,
      Finset.mem_filter, decide_eq_true_eq]
    exact ⟨⟨⟨hXmem, hFX⟩, X.erase, hXmem, Block.preceq_self _, hheight⟩,
      by simpa only [confRoot] using hrootX⟩
  have hvalid : Protocol.VoteSetValid S.E s (confLate S.E duty s) := by
    simpa only [duty, Proofs.Optimistic.confStore, Proofs.Optimistic.tickStore] using
      voteSetValid_confLate_stateBeforeTime
        S adm.toNamedScheduleWellFormed v
          (Protocol.confirmation_time S.E s) s
  have hresult := PreparedV4Confirmation.confirmationWalkWith_of_twoCones
    contract S.E S.hc duty s rho.honest hconeB hconeA hvalid
      (Block.compatible_of_preceq_common (hanchor x hx) (hheads x hx)) (by
        intro _ C hAC hCne hCB
        exact Protocol.confPath_of_candidate S hcandidate C hAC hCne
          (Block.preceq_trans hCB (by rw [hX]; exact hheads x hx)))
  simpa only [namedConfirmationWalk, read, contract, duty,
    Proofs.Optimistic.confStore_eq_confirmationInputRead] using hresult

#print axioms SettledBootstrapPreparedV4.confirmationWalk_core_of_pins

end Handover
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
