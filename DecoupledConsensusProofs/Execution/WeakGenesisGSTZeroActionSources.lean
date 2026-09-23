module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.WeakBootstrapSlot
public import DecoupledConsensusProofs.Protocol.Grades.WeakFiniteWindow

@[expose] public section

/-!
# GST-zero action-source bounds

This leaf instantiates the named prepared-duty history fold at the genesis
boundary. It restores the weak-genesis action-source bound without importing
the recovery closure.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace WeakGenesis

open Internal Execution Protocol Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]

theorem protectedVoteSlots_of_gstZero_v2
    (S : Setup V) {rho : Run V}
    (adm : AdmissibleCore S rho) (hcom : HonestCommittees S rho.honest)
    (hgst : S.E.t_GST = 0)
    (hawake : ∀ r, 0 < r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    {last : Slot} (hhor : Protocol.confirmation_time S.E last ≤ rho.horizon) :
    ∀ d, 1 ≤ d → d ≤ last + 1 →
      ProtectedVoteSlot S rho d Block.genesis ∧
      (∀ q, q < d → ∀ w ∈ rho.honest, ∀ B,
        GenuineConfirmationWith
          (NamedProfile.gradeContract
            (Internal.NamedRecoveryRead.confirmationInputRead S rho w q).cache)
          S.E S.hc (confStore S rho w q) q B →
          ProtectedVoteSlot S rho d B) := by
  have hmajority := honestWeightMajority_of_finiteWindows S hawake hhor
  have hvoteHor : Protocol.vote_time S.E (last + 1) ≤ rho.horizon := by
    apply le_trans ?_ hhor
    rw [← vote_time_succ_add_delta_eq_confirmation_time S.E last]
    exact Int.le_add_of_nonneg_right S.E.Δ_pos.le
  have hseed : ProtectedVoteSlot S rho 1 Block.genesis :=
    protectedVoteSlot_genesis S adm (by decide)
      ((vote_time_mono_slots S.E (Nat.succ_le_succ (Nat.zero_le last))).trans
        hvoteHor)
  have hresult := WeakJoint.protectedVoteSlots_of_historyCut_v2_after_gst
    S adm hcom hmajority (base := 0) (cut := 0) (start := 1)
      (last := last) (P := Block.genesis)
      (Nat.zero_le _) (by rw [hgst]; exact Proofs.HealingLemmas.a_nonneg S 0)
      (by decide) (by simp [Protocol.HealConfig.opening_slot])
      (by rw [hgst]; exact proposal_time_nonneg S.E 1) hhor hseed
      (by
        intro e he hlast C hPC w hw hhigh a ta K ha hemit ht hrow hold hT
        exact False.elim (Nat.not_lt_zero _ hold))
      (by
        intro r hr hold
        exact False.elim (Nat.not_lt_zero _ hold))
      (by
        intro q hq hqone w hw B hB
        have hqzero : q = 0 := Nat.lt_one_iff.mp hqone
        subst q
        have hzero := actionLiveConfirmed_eq_genesis_zero
          S adm hmajority hw
        change (actionStoreAt S rho w 0).st.core.live_confirmed =
          Block.genesis at hzero
        rw [actionStoreAt_eq_update_confirmation_openingConfStore] at hzero
        simp only [Protocol.HealConfig.opening_slot, Nat.zero_mul,
          ← Protocol.confirmation_time_zero_eq_action_zero] at hzero
        rw [hB.selected.symm.trans hzero]
        exact Block.preceq_self _)
      (by
        intro r hr ht w hw C a
        dsimp only
        intro hC hJ ha hemit hold hpair hT
        exact False.elim (Nat.not_lt_zero _ hold))
      (by
        intro d hd hu w hw C a ta
        dsimp only
        intro hC hJ ha hemit ht hold hpair hT
        exact False.elim (Nat.not_lt_zero _ hold))
      (by
        intro r hr hrpos ht
        apply hawake r hrpos
        exact (Assembly.a_mono S (Nat.sub_le r 1)).trans
          (ht.le.trans hvoteHor))
      (by
        intro d hd hu hrpos
        apply hawake (S.hc.round_of d) hrpos
        exact (windowSourceTime_le_vote S hrpos).trans
          ((vote_time_mono_slots S.E hu).trans hvoteHor))
      (by
        intro r hr hrpos ht p
        exact (FrameForward.domain_le_a S r p).trans
          (ht.le.trans hvoteHor))
  intro d hd hu
  obtain ⟨hgen, hconfs⟩ := hresult d hd hu
  exact ⟨hgen, fun q hq w hw B hB =>
    hconfs q (by simp [Protocol.HealConfig.opening_slot]) hq w hw B hB⟩

/-- Every honest SG action source, FG root, and FG witness is below a later
honest vote-duty head when GST is zero. -/
theorem actionSources_preceq_voteDutyHead_of_gstZero
    (S : Setup V) {rho : Run V}
    (adm : AdmissibleCore S rho) (hcom : HonestCommittees S rho.honest)
    (hgst : S.E.t_GST = 0)
    (hawake : ∀ r, 0 < r → S.a (r - 1) ≤ rho.horizon →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    {last d : Slot} (hhor : Protocol.confirmation_time S.E last ≤ rho.horizon)
    (hd : 1 ≤ d) (hupper : d ≤ last + 1)
    {x : V} (hx : x ∈ rho.honest) :
    ∀ r, S.a r < Protocol.vote_time S.E (d + 1) →
      (∀ w ∈ rho.honest,
        NamedRun.emits S rho w
          (Object.attest (actionAttestationAt S rho w r)) (S.a r) →
          Block.Preceq (actionSGBlockAt S rho w r)
            (voteDutyHead S rho x d)) ∧
      (∀ w ∈ rho.honest,
        Block.Preceq
          (Protocol.get_fg_root
            (actionStoreAt S rho w r).st.core.toHealing.toFG)
          (voteDutyHead S rho x d) ∧
        ∀ T, fgConfirmationWitness S (actionStoreAt S rho w r) = some T →
          Block.Preceq T (voteDutyHead S rho x d)) := by
  have hmajority := honestWeightMajority_of_finiteWindows S hawake hhor
  have hslots := protectedVoteSlots_of_gstZero_v2
    S adm hcom hgst hawake hhor
  have hprior := (hslots d hd hupper).2
  have hsources := WeakJoint.actionSources_preceq_of_priorConfirmations_and_historyCut
    S adm hmajority (base := 0) (cut := 0) (s := d)
      (D := voteDutyHead S rho x d) (Nat.zero_le _) ?_ ?_ ?_ ?_
  · intro r ht
    have hr := hsources r (Nat.zero_le _) ht
    exact ⟨hr.1, hr.2 (Nat.zero_le _)⟩
  · intro r hr hold
    exact False.elim (Nat.not_lt_zero _ hold)
  · intro q hq hqd w hw B hB
    exact (hprior q hqd w hw B hB).heads x hx
  · intro r hr ht w hw C a
    dsimp only
    intro hC hJ ha hemit hold hpair hT
    exact False.elim (Nat.not_lt_zero _ hold)
  · intro r hr hrpos ht hsg hroots
    have hactionHor : S.a r ≤ rho.horizon := by
      apply le_trans (action_le_supportCutoff_of_lt_nextVote S ht)
      apply le_trans (support_cutoff_mono S.E hupper)
      simpa only [Protocol.confirmation_time_eq_support_cutoff_succ] using hhor
    have hawakeR := hawake r hrpos
      ((Assembly.a_mono S (Nat.sub_le r 1)).trans hactionHor)
    exact WeakJoint.actionGradeFormationAt_of_awakeWindowMajority
      S adm hrpos hawakeR (by
        intro p hp
        exact WeakJoint.relativeGradeCarrierAt_of_awakeWindowHistory_gstZero
          S adm hgst (base := 0) hrpos (Nat.zero_le _) hawakeR
            hsg hroots p hp)

#print axioms actionSources_preceq_voteDutyHead_of_gstZero
#print axioms protectedVoteSlots_of_gstZero_v2

end WeakGenesis
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
