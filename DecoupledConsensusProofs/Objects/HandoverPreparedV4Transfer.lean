module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.HandoverPreparedV4
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.HandoverReadTransfer

@[expose] public section

/-! # Prefix transfer for the prepared V4 handover
Every field of the finite V4 bootstrap reads the run strictly before the
seed confirmation cutoff. The exact named seed body is transferred through
a retained honest committee member's vote-duty state.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace Handover

open Internal Execution Protocol Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]

private theorem preparedV4_vote_lt_confirmation (S : Setup V) (s : Slot) :
    Protocol.vote_time S.E s < Protocol.confirmation_time S.E s := by
  change Protocol.proposal_time S.E s + S.E.Δ <
    Protocol.proposal_time S.E s + 6 * S.E.Δ
  have harith : ∀ p d : Int, 0 < d → p + d < p + 6 * d := by
    intro p d hd
    omega
  exact harith _ _ S.E.Δ_pos

private theorem preparedV4_confirmation_mono
    (S : Setup V) {s t : Slot} (hst : s ≤ t) :
    Protocol.confirmation_time S.E s ≤ Protocol.confirmation_time S.E t := by
  rw [Protocol.confirmation_time_eq_support_cutoff_succ,
    Protocol.confirmation_time_eq_support_cutoff_succ]
  exact support_cutoff_mono S.E (Nat.add_le_add_right hst 1)

private theorem preparedV4_action_lt_handover
    (S : Setup V) {r cut : Round} {start : Slot}
    (hr : r < cut) (hs : S.hc.opening_slot cut ≤ start) :
    S.a r < Protocol.confirmation_time S.E start := by
  have hgap := action_succ_delta_le_action_of_lt S hr
  have hlt : S.a r < S.a cut := by
    have harith : ∀ x y d : Int, 0 < d → x + 1 + d ≤ y → x < y := by
      intro x y d hd hxy
      omega
    exact harith _ _ _ S.E.Δ_pos hgap
  exact hlt.trans_le (preparedV4_confirmation_mono S hs)

private theorem preparedV4_confirmationInputRead_eq
    (S : Setup V) {rho rho' : Run V} {cutoff : Time}
    (h : AgreesUntil rho rho' cutoff) {s : Slot}
    (ht : Protocol.confirmation_time S.E s ≤ cutoff)
    {v : V} (hv : v ∈ rho'.honest) :
    Internal.NamedRecoveryRead.confirmationInputRead S rho' v s =
      Internal.NamedRecoveryRead.confirmationInputRead S rho v s := by
  unfold Internal.NamedRecoveryRead.confirmationInputRead
    NamedActionReads.confirmationReadAt
  exact congrArg
    (fun n => NamedActionReads.confirmationReadFrom S n
      (Protocol.confirmation_time S.E s))
    (AgreesUntil.stateBeforeTime_eq S h ht hv)

omit [Fintype V] in
private theorem preparedV4_ancestorBodyMem
    {st : Protocol.NamedStore V} (hpc : NamedStore.NamedParentClosed st)
    {A B : NamedBlock V} (hB : B ∈ st.bodies)
    (hAB : NamedBlock.Preceq A B) : A ∈ st.bodies := by
  revert hB hAB
  induction B with
  | genesis =>
      intro hB hAB
      simp only [NamedBlock.Preceq, NamedBlock.preceq, decide_eq_true_eq] at hAB
      exact hAB ▸ hB
  | node parent s root votes support rows proposer ih =>
      intro hB hAB
      simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hAB
      rcases hAB with rfl | hparent
      · exact hB
      · exact ih (hpc.2 _ hB) hparent

private theorem preparedV4_runBlock_transfer
    (S : Setup V) {rho rho' : Run V}
    (adm : AdmissibleCore S rho) (adm' : AdmissibleCore S rho')
    (hcom' : HonestCommittees S rho'.honest)
    {fresh base : Round} {start : Slot} {P : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start P cap)
    (hagree : AgreesUntil rho rho'
      (Protocol.confirmation_time S.E start)) :
    RunBlock S rho' P := by
  have hnonempty : 0 < ((S.E.committee start) ∩ rho'.honest).card := by
    have hm := hcom' start
    rcases Nat.eq_zero_or_pos ((S.E.committee start) ∩ rho'.honest).card with hz | hp
    · rw [hz, Nat.mul_zero] at hm
      exact absurd hm (Nat.not_lt_zero _)
    · exact hp
  obtain ⟨v, hvmem⟩ := Finset.card_pos.mp hnonempty
  have hv' : v ∈ rho'.honest := (Finset.mem_inter.mp hvmem).2
  have hv : v ∈ rho.honest := hagree.honest_subset hv'
  have hvc : v ∈ S.E.committee start := (Finset.mem_inter.mp hvmem).1
  obtain ⟨X, hPX, hXrun, hXemit⟩ := hboot.seed.cone v hv hvc
  have hXtree := emittedHead_mem_voteDutyRead_of_core S adm hv hXrun hXemit
  have hXpre : X.erase ∈
      (rho.stateBeforeTime S (Protocol.vote_time S.E start) v).st.core.T := by
    simpa only [Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom, Protocol.NamedStore.setClock] using hXtree
  obtain ⟨D, hDbody, hDerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho
      (Protocol.vote_time S.E start) v hXpre
  have hDrun : RunBlock S rho D := by
    obtain ⟨i, hi, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho
      adm.toNamedScheduleWellFormed.sorted (Protocol.vote_time S.E start)
    apply Proofs.Bridges.runBlock_of_stateBefore_mem S hv (i := i)
    simpa only [hi] using hDbody
  have hDX : D = X := by
    apply adm.toNamedRootCollisionFree.root_injective D X hDrun hXrun D X
      (Or.inl (Proofs.NamedAncestry.named_self D))
      (Or.inr (Proofs.NamedAncestry.named_self X))
    rw [← Proofs.NamedWire.erase_root D, ← Proofs.NamedWire.erase_root X, hDerase]
  have hPXnamed : NamedBlock.Preceq P X :=
    (namedPreceq_iff_erase_preceq S rho adm.toNamedRootCollisionFree
      hboot.runBlock hXrun).2 hPX
  have hPbody : P ∈
      (rho.stateBeforeTime S (Protocol.vote_time S.E start) v).st.bodies := by
    apply preparedV4_ancestorBodyMem
      (Proofs.NamedRuntime.stateBeforeTime_invariants S rho
        (Protocol.vote_time S.E start) v).1.1.1.2.2.1
      (B := D) hDbody
    simpa only [hDX] using hPXnamed
  have hvoteCut : Protocol.vote_time S.E start ≤
      Protocol.confirmation_time S.E start :=
    vote_time_le_confirmation_time S.E start
  have hPbody' : P ∈
      (rho'.stateBeforeTime S (Protocol.vote_time S.E start) v).st.bodies := by
    rw [AgreesUntil.stateBeforeTime_eq S hagree hvoteCut hv']
    exact hPbody
  obtain ⟨i, hi, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho'
    adm'.toNamedScheduleWellFormed.sorted (Protocol.vote_time S.E start)
  apply Proofs.Bridges.runBlock_of_stateBefore_mem S hv' (i := i)
  simpa only [hi] using hPbody'

/-- The prepared V4 finite bootstrap is invariant under retained-validator
prefix agreement through the seed confirmation cutoff. -/
theorem SettledBootstrapPreparedV4.transfer
    (S : Setup V) {rho rho' : Run V}
    (adm : AdmissibleCore S rho) (adm' : AdmissibleCore S rho')
    (hcom' : HonestCommittees S rho'.honest)
    {fresh base : Round} {start : Slot} {P : NamedBlock V} {cap : Height}
    (hboot : SettledBootstrapPreparedV4 S rho fresh base start P cap)
    (hfresh : fresh ≤ base + S.hc.η_SG)
    (hagree : AgreesUntil rho rho'
      (Protocol.confirmation_time S.E start)) :
    SettledBootstrapPreparedV4 S rho' fresh base start P cap := by
  have hvote := preparedV4_vote_lt_confirmation S start
  have hprotected : ProtectedVoteSlot S rho start P.erase :=
    ⟨hboot.seedAll, hboot.seed.cone⟩
  have hseedFull := AgreesUntil.protectedVoteSlot_of_core S adm
    adm'.toNamedScheduleWellFormed hagree hvote hprotected
  have hseed : ProtectedVoteSlotCommittee S rho' start P.erase :=
    ⟨fun w hw _ => hseedFull.heads w hw, hseedFull.cone⟩
  have haction : ∀ r, r < base + S.hc.η_SG →
      S.a r < Protocol.confirmation_time S.E start :=
    fun r hr => preparedV4_action_lt_handover S hr hboot.settled
  refine
    { settled := hboot.settled
      basePost := hboot.basePost
      seed := hseed
      seedAll := hseedFull.heads
      confirmationSeedPrepared := ?_
      runBlock := preparedV4_runBlock_transfer S adm adm' hcom' hboot hagree
      oldRows := ?_
      heightCap := hboot.heightCap
      frontierSeed := ?_
      sgBoot := ?_
      confBoot := ?_
      fgAll := ?_ }
  · intro v hv
    rw [preparedV4_confirmationInputRead_eq S hagree (le_refl _) hv,
      AgreesUntil.confStore_eq S hagree (le_refl _) hv]
    exact hboot.confirmationSeedPrepared v (hagree.honest_subset hv)
  · intro a ta ht ha hemit hold hrow
    have hat : ta = S.a a.round := (emits_attest_shape S hemit).2
    have htime : ta < Protocol.confirmation_time S.E start := by
      rw [hat]
      exact haction _ (hold.trans_le hfresh)
    exact hboot.oldRows a ta ht (hagree.honest_subset ha)
      ((AgreesUntil.emits_iff S adm.toNamedScheduleWellFormed
        adm'.toNamedScheduleWellFormed hagree htime ha _).mp hemit) hold hrow
  · rcases hboot.frontierSeed with hz | hgap
    · exact Or.inl hz
    · right
      intro v hv
      rw [AgreesUntil.storeBeforeTime_eq S hagree
        ((min_le_right _ _).trans hvote.le) hv]
      exact hgap v (hagree.honest_subset hv)
  · intro r hrlo hrhi v hv hemit
    have ht := haction r hrhi
    have heq := AgreesUntil.actionAttestationAt_eq S hagree ht.le hv
    rw [heq] at hemit
    rw [AgreesUntil.actionSGBlockAt_eq S hagree ht.le hv]
    exact hboot.sgBoot r hrlo hrhi v (hagree.honest_subset hv)
      ((AgreesUntil.emits_iff S adm.toNamedScheduleWellFormed
        adm'.toNamedScheduleWellFormed hagree ht hv _).mp hemit)
  · intro q hqlo hqhi v hv B hB
    rw [preparedV4_confirmationInputRead_eq S hagree
        (preparedV4_confirmation_mono S hqhi.le) hv,
      AgreesUntil.confStore_eq S hagree
        (preparedV4_confirmation_mono S hqhi.le) hv] at hB
    exact hboot.confBoot q hqlo hqhi v (hagree.honest_subset hv) B hB
  · intro a ta ht T ha hemit hrow hrlo hrhi hT
    have htime : ta < Protocol.confirmation_time S.E start := by
      rw [(emits_attest_shape S hemit).2]
      exact haction _ hrhi
    rw [AgreesUntil.actionStoreAt_eq S hagree (haction _ hrhi).le ha] at hT
    exact hboot.fgAll a ta ht T (hagree.honest_subset ha)
      ((AgreesUntil.emits_iff S adm.toNamedScheduleWellFormed
        adm'.toNamedScheduleWellFormed hagree htime ha _).mp hemit)
      hrow hrlo hrhi hT


/-- The separate latest seed transfers through the same confirmation-read
prefix as the live-only V4 bootstrap. -/
theorem SettledBootstrapPreparedV4.LatestSeed.transfer
    (S : Setup V) {rho rho' : Run V} {start : Slot} {P : NamedBlock V}
    (hlatest : SettledBootstrapPreparedV4.LatestSeed S rho start P)
    (hagree : AgreesUntil rho rho'
      (Protocol.confirmation_time S.E start)) :
    SettledBootstrapPreparedV4.LatestSeed S rho' start P := by
  intro v hv
  rw [preparedV4_confirmationInputRead_eq S hagree (le_refl _) hv,
    AgreesUntil.confStore_eq S hagree (le_refl _) hv]
  exact hlatest v (hagree.honest_subset hv)


end Handover
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
