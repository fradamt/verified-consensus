module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Handlers.MutualInduction
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.LayerAHistoryIndices
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.WeakBootstrapSlot

@[expose] public section

/-!
# Bounded healthy-prefix confirmation fold

The read-transport producer and the delivery-parametric prepared successor are
available. The fold declarations remain parked here until their producer
packages are complete.

## Open — G2 `WeakJoint.protectedVoteSlots_of_historyCut`

The pre-rewrite theorem is the live induction in the read-only earlier tree:
`DecoupledConsensusProofs/HealingSurface/WeakBootstrapSlotRun.lean:40-194`.
Its recent-row route is the prepared successor in
`WeakBootstrapJoinRun.lean:808`, not the all-row `hwitnesses` route.

The real prepared-fold attempt reached this exact recent-row goal:

```text
⊢ ∀ (a: NamedAttestation V) (ta: Time) (K: NamedBlock V),
    a.val_index ∈ rho.honest →
    NamedRun.emits S rho a.val_index (Object.attest a) ta →
    ta < Protocol.vote_time S.E (d + 1) →
    a.height_pair.erase.height? =
      some ((Proofs.Optimistic.voteDutyStore S rho w (d + 1)).h_max - 1) →
    fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) =
      some (Protocol.derive_named S.E S.cfg K).T_h →
    NamedBlock.compatible C K = true
```

First compiler error:

```text
Application type mismatch: hnoOldFrontier requires
a.round < cut, but the live FGFrontierWitnessesCompatibleAt goal has no
a.round < cut premise.
```

the prior proof handles recent rows inside the successor through action-source
induction. No theorem in the current named cone supplies that recent-row
frontier package at this fold site. No public premise was added.

## Open — W3 T1 `protectedVoteSlots_before`

The requested declaration is:

```lean
theorem protectedVoteSlots_before
    (S: Setup V) (rho: NamedRun V) (b0 b1: Time)
    (hexec: OutageExecution S rho b0 b1)
    (hcom: HonestCommittees S rho.honest)
    (hsleep: OutageSleepyThroughout S rho):
    ∀ d: Slot, 1 ≤ d → Protocol.vote_time S.E d + S.E.Δ ≤ b0 →
      Proofs.HealingSurface.ProtectedVoteSlot S rho d Block.genesis ∧
      (∀ q: Slot, q < d → ∀ w ∈ rho.honest, ∀ B,
        GenuineConfirmationWith
          (NamedProfile.gradeContract
            (Internal.NamedRecoveryRead.confirmationInputRead S rho w q).cache)
          S.E S.hc (Proofs.Optimistic.confStore S rho w q) q B →
          Proofs.HealingSurface.ProtectedVoteSlot S rho d B)
```

The stale first attempt used
`protectedVoteSlot_succ_of_preparedWindow` and blocked at
`⊢ S.E.t_GST ≤ Protocol.vote_time S.E s`. That route is superseded. A real
follow-up probe used
`protectedVoteSlot_succ_of_preparedWindow_persistent_of_delivery` with
`hexec.core` and `hexec.healthy`; that application typechecks when the
prepared package, frontier witnesses, and roots are supplied.

The first unresolved goal in the full successor probe is now the all-row
frontier package:

```text
⊢ ∀ w ∈ rho.honest,
    ∀ {C: NamedBlock V},
      C.erase = B →
      (Protocol.derive_named S.E S.cfg C).h <
          (Internal.NamedRecoveryRead.voteDutyRead S rho w (s + 1)).st.core.h_max - 1 →
      ∀ (a: NamedAttestation V) (ta: Time) (K: NamedBlock V),
        a.val_index ∈ rho.honest →
        NamedRun.emits S rho a.val_index (Object.attest a) ta →
        ta < Protocol.vote_time S.E (s + 1) →
        a.height_pair.erase.height? =
          some ((Proofs.Optimistic.voteDutyStore S rho w (s + 1)).h_max - 1) →
        fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) =
          some (Protocol.derive_named S.E S.cfg K).T_h →
        NamedBlock.compatible C K = true
```

First compiler error from that probe:

```text
BoundedSelectionChainRun.lean:31:10: error: don't know how to synthesize placeholder for argument `hwitnesses`
```

The bounded delivery instance is therefore wired, but T1 is not available.

## Delivery-fold interface Open

A focused application of the available delivery-parametric fold, with the
unrelated majority, seed, horizon, and callback inputs pinned locally, leaves
this exact goal for the first fold-only premise:

```text
⊢ S.E.t_GST ≤ Protocol.proposal_time S.E 1
```

First compiler error, verbatim:

```text
/private/tmp/W3T1InterfaceProbe.lean:23:8: error: omega could not prove the goal:
No usable constraints found. You may need to unfold definitions so `omega` can see linear arithmetic facts about `Nat` and `Int`, which may also involve multiplication, division, and modular remainder by constants.
```

Selected difference to the pre-rewrite
`WeakGenesis.protectedVoteSlots_of_gstZero_finiteWindows`: its `hgst:
S.E.t_GST = 0` proves this premise by rewriting to
`proposal_time_nonneg`. The outage T1 statement has no GST-zero premise;
`hexec.healthy` proves delivery only when a send satisfies `t + Δ ≤ b0`, and
`hexec.gst` gives only `S.E.t_GST ≤ b1`. The current available fold still
requires the numeric post-GST inequality, so the bounded horizon does not
close this goal. No public premise was added.

## T2–T5

The bounded twins are not declared in the current source cone. T2 and T3
need the pinned T1 fold; T4 needs T3; and T5 has the same two live-body
compatibility branches recorded in `proof branch.md`, each with
goal `⊢ C.compatible L = true`. No extra premise or standing assumption was
introduced.
-/



namespace DecoupledConsensusModel.Proofs.NamedOutageClosure

open Internal Execution Internal.NamedOutageEntry
open DecoupledConsensusModel.Protocol
open Proofs.HealingSurface Protocol Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]

/- The healthy-prefix form of the genesis protected-slot fold.

The extra fixed G2-domain bound is the weakest schedule range that exposes a
positive covered round and hence the weighted majority used by the fold. The
per-slot vote bound covers every phase domain of each round that the prepared
successor reads. -/
set_option maxHeartbeats 400000 in
theorem protectedVoteSlots_before
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time)
    (hexec : OutageExecution S rho b0 b1)
    (hcom : HonestCommittees S rho.honest)
    (hsleep : OutageSleepyThroughout S rho)
    (hroundOne : domain S.E S.hc 1 .g2 ≤ b0) :
    ∀ d : Slot, 1 ≤ d → Protocol.vote_time S.E d + S.E.Δ ≤ b0 →
      Proofs.HealingSurface.ProtectedVoteSlot S rho d Block.genesis ∧
      (∀ q : Slot, q < d → ∀ w ∈ rho.honest, ∀ B,
        GenuineConfirmationWith
          (NamedProfile.gradeContract
            (Internal.NamedRecoveryRead.confirmationInputRead S rho w q).cache)
          S.E S.hc (Proofs.Optimistic.confStore S rho w q) q B →
          Proofs.HealingSurface.ProtectedVoteSlot S rho d B) := by
  have hcapHor : b0 ≤ rho.horizon :=
    hexec.interval.2.1.trans hexec.interval.2.2
  have hroundOneNonneg : 0 ≤ domain S.E S.hc 1 .g2 := by
    exact (Proofs.HealingLemmas.a_nonneg S 0).trans
      (action_le_domain S S.hc.R_ge_three (by decide))
  have hmajority : HonestWeightMajority S rho.honest := by
    apply Proofs.HealingSurface.WeakSG.honestWeightMajority_of_awakeWindowMajority S
    exact hsleep 1 (by decide)
      (Or.inr ⟨.g2, hroundOneNonneg, hroundOne.trans hcapHor⟩)
  intro d hd hcap
  have hvoteCap : Protocol.vote_time S.E d ≤ b0 :=
    (Int.le_add_of_nonneg_right S.E.Δ_pos.le).trans hcap
  have hvoteHor : Protocol.vote_time S.E d ≤ rho.horizon :=
    hvoteCap.trans hcapHor
  have hseed : Proofs.HealingSurface.ProtectedVoteSlot S rho 1 Block.genesis :=
    Proofs.HealingSurface.WeakGenesis.protectedVoteSlot_genesis S hexec.core
      (by decide) ((vote_time_mono_slots S.E hd).trans hvoteHor)
  have hnoOldFrontier : Proofs.HealingSurface.WeakJoint.NoOldFrontierAtCut
      S rho 0 1 (d - 1) Block.genesis := by
    intro e he hlast C hPC w hw hhigh a ta K ha hemit ht hrow hold hT
    exact False.elim (Nat.not_lt_zero _ hold)
  have hsgBoot : ∀ r, 0 ≤ r → r < 0 → ∀ w ∈ rho.honest,
      NamedRun.emits S rho w
        (Object.attest (actionAttestationAt S rho w r)) (S.a r) →
      Block.Preceq (actionSGBlockAt S rho w r) Block.genesis := by
    intro r hr hold w hw hemit
    exact False.elim (Nat.not_lt_zero _ hold)
  have hconfBoot : ∀ q, S.hc.opening_slot 0 ≤ q → q < 1 →
      ∀ w ∈ rho.honest, ∀ B,
      GenuineConfirmationWith
        (NamedProfile.gradeContract
          (Internal.NamedRecoveryRead.confirmationInputRead S rho w q).cache)
        S.E S.hc (confStore S rho w q) q B →
      Block.Preceq B Block.genesis := by
    intro q hq hqone w hw B hB
    have hqzero : q = 0 := Nat.lt_one_iff.mp hqone
    subst q
    have hzero := Proofs.HealingSurface.WeakGenesis.actionLiveConfirmed_eq_genesis_zero
      S hexec.core hmajority hw
    change (actionStoreAt S rho w 0).st.core.live_confirmed = Block.genesis at hzero
    rw [Proofs.HealingSurface.actionStoreAt_eq_update_confirmation_openingConfStore] at hzero
    have hBzero : B = Block.genesis := hB.selected.symm.trans (by
      simpa only [Protocol.HealConfig.opening_slot, Nat.zero_mul,
        Internal.NamedRecoveryRead.confirmationInputRead,
        Protocol.confirmation_time_zero_eq_action_zero S] using hzero)
    rw [hBzero]
    exact Block.preceq_self _
  have hlegacyActionRoots : ∀ r, 0 ≤ r →
      S.a r < Protocol.vote_time S.E d → ∀ w ∈ rho.honest,
      ∀ (C : NamedBlock V) (a : NamedAttestation V),
      let R := Protocol.get_fg_root
        (actionStoreAt S rho w r).st.core.toHealing.toFG
      C ∈ (actionStoreAt S rho w r).st.bodies →
      (Protocol.derive_named S.E S.cfg C).J = R →
      a.val_index ∈ rho.honest →
      NamedRun.emits S rho a.val_index (Object.attest a) (S.a a.round) →
      a.round < 0 →
      a.height_pair.erase = HeightPair.target
        (Protocol.derive_named S.E S.cfg C).h_j
        (Protocol.derive_named S.E S.cfg C).J.root →
      fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) = some R →
      Block.Preceq R Block.genesis := by
    intro r hr ht w hw C a
    dsimp only
    intro hC hJ ha hemit hold hpair hT
    exact False.elim (Nat.not_lt_zero _ hold)
  have hlegacyReadRoots : ∀ e, 1 < e → e ≤ d → ∀ w ∈ rho.honest,
      ∀ (C : NamedBlock V) (a : NamedAttestation V) (ta : Time),
      let R := Protocol.get_fg_root (voteDutyStore S rho w e).toHealing.toFG
      C ∈ (NamedRun.stateBeforeTime S rho
        (Protocol.vote_time S.E e) w).st.bodies →
      (Protocol.derive_named S.E S.cfg C).J = R →
      a.val_index ∈ rho.honest →
      NamedRun.emits S rho a.val_index (Object.attest a) ta →
      ta < Protocol.vote_time S.E e →
      a.round < 0 →
      a.height_pair.erase = HeightPair.target
        (Protocol.derive_named S.E S.cfg C).h_j
        (Protocol.derive_named S.E S.cfg C).J.root →
      fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) = some R →
      Block.Preceq R Block.genesis := by
    intro e he hed w hw C a ta
    dsimp only
    intro hC hJ ha hemit ht hold hpair hT
    exact False.elim (Nat.not_lt_zero _ hold)
  have hwindow : ∀ r, 0 ≤ r → 0 < r → S.a r < Protocol.vote_time S.E d →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r := by
    intro r hr hrpos ht
    apply hsleep r hrpos
    exact Or.inl ⟨Proofs.HealingLemmas.a_nonneg S r,
      ht.le.trans hvoteHor⟩
  have hreadWindow : ∀ e, 1 < e → e ≤ d →
      0 < S.hc.round_of e →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG (S.hc.round_of e) := by
    intro e he hed hrpos
    apply hsleep (S.hc.round_of e) hrpos
    apply Or.inr
    refine ⟨.g1, ?_, ?_⟩
    · rw [NamedOutageClosure.domain_g1_eq_opening]
      exact Proofs.Optimistic.proposal_time_nonneg S.E _
    · rw [NamedOutageClosure.domain_g1_eq_opening]
      exact ((Protocol.proposal_time_mono S.E
        (Nat.div_mul_le_self e S.hc.R)).trans
          (proposal_time_lt_vote_time S.E e).le).trans
        ((vote_time_mono_slots S.E hed).trans hvoteHor)
  have hcapDomain : ∀ r, 0 ≤ r → 0 < r →
      S.a r < Protocol.vote_time S.E d → ∀ p,
      domain S.E S.hc r p ≤ b0 := by
    intro r hr hrpos ht p
    have hdomainAction : domain S.E S.hc r p ≤ S.a r := by
      have hDelta := S.E.Δ_pos
      have hp : domain S.E S.hc r p ≤ domain S.E S.hc r .g0 := by
        cases p <;> unfold domain Phase.domainOffset <;> linarith
      exact hp.trans (by
        rw [Proofs.HealingSurface.domain_g0_eq_Γ_1]
        exact (Proofs.HealingLemmas.Γ_1_lt_Γ_2 S.hc S.E.Δ_pos r).le.trans
          (Proofs.HealingSurface.Γ_2_le_a S.hc S.E.Δ_pos r))
    exact hdomainAction.trans (ht.le.trans hvoteCap)
  have hconfCap : Protocol.confirmation_time S.E (d - 1) ≤ b0 := by
    rw [← vote_time_succ_add_delta_eq_confirmation_time S.E (d - 1)]
    simpa only [Nat.sub_add_cancel hd] using hcap
  have hconfHor : Protocol.confirmation_time S.E (d - 1) ≤ rho.horizon :=
    hconfCap.trans hcapHor
  have hresult := Proofs.HealingSurface.WeakJoint.protectedVoteSlots_of_historyCut_of_delivery_v2
    S hexec.core hexec.healthy hcapHor hcom hmajority
    (base := 0) (cut := 0) (start := 1) (last := d - 1) (P := Block.genesis)
    (Nat.zero_le _) (by decide) (by simp [Protocol.HealConfig.opening_slot])
    hconfCap hconfHor hseed hnoOldFrontier hsgBoot hconfBoot
    (by simpa only [Nat.sub_add_cancel hd] using hlegacyActionRoots)
    (by simpa only [Nat.sub_add_cancel hd] using hlegacyReadRoots)
    (by simpa only [Nat.sub_add_cancel hd] using hwindow)
    (by simpa only [Nat.sub_add_cancel hd] using hreadWindow)
    (by simpa only [Nat.sub_add_cancel hd] using hcapDomain)
  have hupper : d ≤ (d - 1) + 1 := (Nat.sub_add_cancel hd).ge
  obtain ⟨hgen, hprior⟩ := hresult d hd hupper
  refine ⟨hgen, ?_⟩
  intro q hqd w hw B hB
  exact hprior q (by simp [Protocol.HealConfig.opening_slot]) hqd w hw B hB

#print axioms protectedVoteSlots_before

end DecoupledConsensusModel.Proofs.NamedOutageClosure

end
