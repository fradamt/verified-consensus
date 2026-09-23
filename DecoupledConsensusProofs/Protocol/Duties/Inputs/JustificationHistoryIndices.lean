module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.LayerAHistoryIndices
public import DecoupledConsensusProofs.Execution.EventIndexBridge
public import DecoupledConsensusProofs.Execution.IdxGaps
public import DecoupledConsensusProofs.Execution.ViabilityHistoryIndices
public import DecoupledConsensusProofs.Protocol.Handlers.PrefixCarrier
public import DecoupledConsensusProofs.Protocol.ChainState.JustificationCertificates
public import DecoupledConsensusProofs.Execution.OutageProvenance
public import DecoupledConsensusProofs.Protocol.Handlers.ReceiptCallsGF
public import DecoupledConsensusProofs.Protocol.Handlers.FinalizationBridge
public import DecoupledConsensusProofs.Protocol.ChainState.FinalityCertificates
public import DecoupledConsensusProofs.Protocol.Handlers.TickBridges

@[expose] public section

/-!
# Index-bounded justification/prefix history (task 4)

`justification_on_history_chain` and `receipt_prefix_history_lift`, copied
from `HistoryProofsDraft.lean` with the index hypotheses in place of the
time cut and its strict/prefix bounds. `justification_on_history_chain`
reuses `ViabilityHistory.row_emission_index_le_block_acceptance`
(task 3) for the same provenance step, so it inherits the same recorded gap
(`IdxGaps.emission_index_le_self_proposed_carrier`) on the self-proposal
branch. `receipt_prefix_history_lift` never used the time cut for anything
but `LayerAHistoryOn`'s finalized-prefix clause, whose index form already
takes `i ≤ n` directly (`PrefixThrough` is not needed at all), so its proof
is a bound-free substitution.
-/


namespace DecoupledConsensusModel.Proofs.NamedOutageHistory.HistoryProofs
open Execution Execution.NamedReceiptCalls Protocol
open Internal.NamedOutageEntry.History
open DecoupledConsensusModel.Proofs.NamedOutageHistory.ViabilityHistory
variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
private theorem genesis_preceq (B : NamedBlock V) : NamedBlock.Preceq .genesis B := by
  induction B with
  | genesis => simp [NamedBlock.Preceq, NamedBlock.preceq]
  | node parent s root votes support rows proposer ih =>
    simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true]
    exact Or.inr ih

omit [Fintype V] in
private theorem ancestor_body_mem {st : Protocol.NamedStore V}
    (hpc : NamedStore.NamedParentClosed st) {A B : NamedBlock V}
    (hB : B ∈ st.bodies) (hAB : NamedBlock.Preceq A B) : A ∈ st.bodies := by
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

private theorem quorum_honest_member (S : Setup V) (rho : NamedRun V)
    (Q : Finset V) (hQ : S.E.electorate.IsQuorum Q)
    (hbad : S.E.electorate.weightOf (Finset.univ \ rho.honest) < S.E.q) :
    ∃ signer ∈ Q, signer ∈ rho.honest := by
  by_contra hn
  have hsub : Q ⊆ Finset.univ \ rho.honest := by
    intro signer hs
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun hh => hn ⟨signer, hs, hh⟩⟩
  have hm := S.E.electorate.weightOf_mono hsub
  have hq : S.E.q ≤ S.E.electorate.weightOf Q := hQ
  omega



theorem justification_on_history_chain
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    (n : Nat) (C : NamedBlock V)
    (hhistory : LayerAHistoryIdx S rho n C)
    (i : Nat) (v : V) (hv : v ∈ rho.honest) (hi : i ≤ n)
    (hbad : S.E.electorate.weightOf (Finset.univ \ rho.honest) < S.E.q) :
    ∃ J : NamedBlock V,
      NamedRun.blockInRun S rho J ∧
      J ∈ (NamedRun.stateBefore S rho i v).st.bodies ∧
      J.erase = (NamedRun.stateBefore S rho i v).st.core.J ∧
      NamedBlock.Preceq J C := by
  obtain ⟨D, hD, hDJ, hDh⟩ :=
    PrefixCarrier.justification_carrier_stateBefore S rho i v
  have hDscope := Proofs.NamedRuntime.blockInRun_of_direct S rho
    (Proofs.NamedRuntime.directBlock_of_prefix S rho hv i hD)
  have hpc := (Proofs.NamedRuntime.stateBefore_invariants S rho i v).1.1.1.2.2.1
  by_cases hz : (derive_named S.E S.cfg D).h_j = 0
  · have hgen := NamedJustificationCertificates.justified_zero_is_genesis S.E S.cfg D hz
    refine ⟨.genesis, ?_, hpc.1, hgen.symm.trans hDJ, genesis_preceq C⟩
    exact Proofs.NamedRuntime.blockInRun_of_ancestor S rho hDscope (genesis_preceq D)
  · obtain ⟨J, hJD, hJE, Q, hQ, hrows⟩ :=
      NamedJustificationCertificates.justification_certificate S.E S.cfg D hz
    obtain ⟨signer, hsignerQ, hsignerHon⟩ := quorum_honest_member S rho Q hQ hbad
    obtain ⟨carrier, a, hcarrier, hrow, hsigner, hp⟩ := hrows signer hsignerQ
    have ha : a.val_index ∈ rho.honest := by simpa only [hsigner] using hsignerHon
    obtain ⟨j, hj, received, hacc, hsend, hem⟩ :=
      NamedOutageProvenance.honest_held_ancestor_row_emission S rho
        core.toNamedUnforgeable i v hD hcarrier hrow ha
    obtain ⟨k, hk, hemit⟩ := hem
    have hjn : j < n := lt_of_lt_of_le hj hi
    have hkj : k ≤ j :=
      row_emission_index_le_block_acceptance S rho core v carrier j received hacc
        a hrow ha k hk hemit hsend
    have hkn : k < n := lt_of_le_of_lt hkj hjn
    obtain ⟨source, entry, hsourceScope, hsourceHeld, hentryScope, hentryHeld,
      hval, htime, hcreate, hselector, hfields, hheight, htarget, herase,
      hancestor, hsameHeight, hroot, hentryC⟩ :=
      hhistory.2.2.1 k a.val_index (S.a a.round) a ha hk hemit hkn
        (derive_named S.E S.cfg D).h_j J.root false hp
    have heq : entry = J := core.root_injective C D hhistory.1 hDscope
      entry J (Or.inl hentryC) (Or.inr hJD) hroot
    subst entry
    exact ⟨J, Proofs.NamedRuntime.blockInRun_of_ancestor S rho hDscope hJD,
      ancestor_body_mem hpc hD hJD, hJE.trans hDJ, hentryC⟩


/-- The justified block of an honest indexed read is genesis or the height-pair
target of an honest attestation emitted at an earlier tick; the row data
(emitting node, tick index, round, FG source of that action read) is kept.
Variant of `justification_on_history_chain` for the outage output theorem. -/
theorem justification_honest_fgRow
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    (n : Nat) (C : NamedBlock V)
    (hhistory : LayerAHistoryIdx S rho n C)
    (i : Nat) (v : V) (hv : v ∈ rho.honest) (hi : i ≤ n)
    (hbad : S.E.electorate.weightOf (Finset.univ \ rho.honest) < S.E.q) :
    (NamedRun.stateBefore S rho i v).st.core.J = Block.genesis ∨
    ∃ (k : Nat) (a : NamedAttestation V) (J source : NamedBlock V),
      a.val_index ∈ rho.honest ∧ k < i ∧
      rho.events[k]? = some (.tick a.val_index (S.a a.round)) ∧
      NamedObject.attest a ∈ NamedRun.emittedAt S rho k a.val_index (S.a a.round) ∧
      NamedRun.blockInRun S rho J ∧
      J.erase = (NamedRun.stateBefore S rho i v).st.core.J ∧
      NamedBlock.Preceq J C ∧
      Protocol.fg_source_with
        (NamedProfile.gradeContract
          (Internal.NamedOutageEntry.actionReadFrom S (NamedRun.stateBefore S rho k a.val_index) a.round).cache)
        S.E S.hc
        (Internal.NamedOutageEntry.actionReadFrom S (NamedRun.stateBefore S rho k a.val_index) a.round).st.core.toHealing
        a.round
        (Protocol.grade2_block_with
          (NamedProfile.gradeContract
            (Internal.NamedOutageEntry.actionReadFrom S (NamedRun.stateBefore S rho k a.val_index) a.round).cache)
          S.E S.hc
          (Internal.NamedOutageEntry.actionReadFrom S (NamedRun.stateBefore S rho k a.val_index) a.round).st.core.toHealing
          a.round) = some source.erase ∧
      J.erase = ((Internal.NamedOutageEntry.actionReadFrom S (NamedRun.stateBefore S rho k a.val_index) a.round).st.core.σ
        source.erase).T_h := by
  obtain ⟨D, hD, hDJ, hDh⟩ :=
    PrefixCarrier.justification_carrier_stateBefore S rho i v
  have hDscope := Proofs.NamedRuntime.blockInRun_of_direct S rho
    (Proofs.NamedRuntime.directBlock_of_prefix S rho hv i hD)
  by_cases hz : (derive_named S.E S.cfg D).h_j = 0
  · have hgen := NamedJustificationCertificates.justified_zero_is_genesis S.E S.cfg D hz
    exact Or.inl (hDJ.symm.trans hgen)
  · obtain ⟨J, hJD, hJE, Q, hQ, hrows⟩ :=
      NamedJustificationCertificates.justification_certificate S.E S.cfg D hz
    obtain ⟨signer, hsignerQ, hsignerHon⟩ := quorum_honest_member S rho Q hQ hbad
    obtain ⟨carrier, a, hcarrier, hrow, hsigner, hp⟩ := hrows signer hsignerQ
    have ha : a.val_index ∈ rho.honest := by simpa only [hsigner] using hsignerHon
    obtain ⟨j, hj, received, hacc, hsend, hem⟩ :=
      NamedOutageProvenance.honest_held_ancestor_row_emission S rho
        core.toNamedUnforgeable i v hD hcarrier hrow ha
    obtain ⟨k, hk, hemit⟩ := hem
    have hjn : j < n := lt_of_lt_of_le hj hi
    have hkj : k ≤ j :=
      row_emission_index_le_block_acceptance S rho core v carrier j received hacc
        a hrow ha k hk hemit hsend
    have hki : k < i := lt_of_le_of_lt hkj hj
    have hkn : k < n := lt_of_le_of_lt hkj hjn
    obtain ⟨source, entry, hsourceScope, hsourceHeld, hentryScope, hentryHeld,
      hval, htime, hcreate, hselector, hfields, hheight, htarget, herase,
      hancestor, hsameHeight, hroot, hentryC⟩ :=
      hhistory.2.2.1 k a.val_index (S.a a.round) a ha hk hemit hkn
        (derive_named S.E S.cfg D).h_j J.root false hp
    have heq : entry = J := core.root_injective C D hhistory.1 hDscope
      entry J (Or.inl hentryC) (Or.inr hJD) hroot
    subst entry
    refine Or.inr ⟨k, a, J, source, ha, hki, hk, hemit,
      Proofs.NamedRuntime.blockInRun_of_ancestor S rho hDscope hJD,
      hJE.trans hDJ, hentryC, hselector, herase⟩


/-- An honest attestation row carried by a block held at an honest strict read
at time `t` was emitted strictly before `t`. General-time form of
`NamedOutageProvenance.honest_held_ancestor_row_before_action`. -/
theorem honest_held_ancestor_row_before_time
    (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (auth : NamedUnforgeable S rho)
    (reader : V) (t : Time) {B A : NamedBlock V} {a : NamedAttestation V}
    (hB : B ∈ (NamedRun.stateBeforeTime S rho t reader).st.bodies)
    (hAB : NamedBlock.Preceq A B) (ha : a ∈ A.attestations)
    (hHon : a.val_index ∈ rho.honest) :
    S.a a.round < t ∧ NamedRun.emits S rho a.val_index (.attest a) (S.a a.round) := by
  obtain ⟨i, hread, hbefore⟩ :=
    Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho sch.sorted t
  rw [hread] at hB
  obtain ⟨j, hj, t', hacc, hsend, hem⟩ :=
    NamedOutageProvenance.honest_held_ancestor_row_emission S rho auth i reader hB hAB ha hHon
  obtain ⟨e, he, _, het⟩ := hacc.1.2
  have ht : t' < t := by simpa only [het] using hbefore j e hj he
  exact ⟨lt_of_le_of_lt hsend ht, hem⟩

/-- The finalized block of an honest indexed read is genesis or the height-pair
target of an honest FG row emitted at an earlier tick: the finality certificate
names an honest finality voter whose head's justified block is the finalized
block, and that block's own justification certificate names an honest FG row
carried below that head. Same output shape as `justification_honest_fgRow`. -/
theorem finalized_honest_fgRow
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    (n : Nat) (C : NamedBlock V)
    (hhistory : LayerAHistoryIdx S rho n C)
    (i : Nat) (v : V) (hv : v ∈ rho.honest) (hi : i ≤ n)
    (hbad : S.E.electorate.weightOf (Finset.univ \ rho.honest) < S.E.q) :
    (NamedRun.stateBefore S rho i v).st.core.F = Block.genesis ∨
    ∃ (k : Nat) (a : NamedAttestation V) (J source : NamedBlock V),
      a.val_index ∈ rho.honest ∧ k < i ∧
      rho.events[k]? = some (.tick a.val_index (S.a a.round)) ∧
      NamedObject.attest a ∈ NamedRun.emittedAt S rho k a.val_index (S.a a.round) ∧
      NamedRun.blockInRun S rho J ∧
      J.erase = (NamedRun.stateBefore S rho i v).st.core.F ∧
      NamedBlock.Preceq J C ∧
      Protocol.fg_source_with
        (NamedProfile.gradeContract
          (Internal.NamedOutageEntry.actionReadFrom S
            (NamedRun.stateBefore S rho k a.val_index) a.round).cache)
        S.E S.hc
        (Internal.NamedOutageEntry.actionReadFrom S
          (NamedRun.stateBefore S rho k a.val_index) a.round).st.core.toHealing
        a.round
        (Protocol.grade2_block_with
          (NamedProfile.gradeContract
            (Internal.NamedOutageEntry.actionReadFrom S
              (NamedRun.stateBefore S rho k a.val_index) a.round).cache)
          S.E S.hc
          (Internal.NamedOutageEntry.actionReadFrom S
            (NamedRun.stateBefore S rho k a.val_index) a.round).st.core.toHealing
          a.round) = some source.erase ∧
      J.erase = ((Internal.NamedOutageEntry.actionReadFrom S
        (NamedRun.stateBefore S rho k a.val_index) a.round).st.core.σ
        source.erase).T_h ∧
      ∃ (ka : Nat) (xa : V) (ra : Round), ka < i ∧
        rho.events[ka]? = some (.tick xa (S.a ra)) ∧ S.a a.round < S.a ra := by
  obtain ⟨D, hD, hDF, -⟩ :=
    NamedFinalizationBridge.finalization_carrier_stateBefore S rho i v
  have hDscope := Proofs.NamedRuntime.blockInRun_of_direct S rho
    (Proofs.NamedRuntime.directBlock_of_prefix S rho hv i hD)
  by_cases hzF : (derive_named S.E S.cfg D).h_F = 0
  · exact Or.inl (hDF.symm.trans
      (NamedFinalityCertificates.finalized_zero_is_genesis S.E S.cfg D hzF))
  obtain ⟨Fn, hFD, hFE, Q, hQ, hrows⟩ :=
    NamedFinalityCertificates.finality_certificate S.E S.cfg D hzF
  obtain ⟨signer, hsQ, hsHon⟩ := quorum_honest_member S rho Q hQ hbad
  obtain ⟨carrier, a, hcarrier, hrow, hsigner, hp⟩ := hrows signer hsQ
  have ha : a.val_index ∈ rho.honest := by simpa only [hsigner] using hsHon
  obtain ⟨j, hj, received, hacc, hsend, hem⟩ :=
    NamedOutageProvenance.honest_held_ancestor_row_emission S rho
      core.toNamedUnforgeable i v hD hcarrier hrow ha
  obtain ⟨k, hk, hemit⟩ := hem
  have hkj : k ≤ j :=
    row_emission_index_le_block_acceptance S rho core v carrier j received hacc
      a hrow ha k hk hemit hsend
  have hki : k < i := lt_of_le_of_lt hkj hj
  have hkn : k < n := lt_of_lt_of_le hki hi
  obtain ⟨H, K, hHrun, hHbody, -, hKrun, hKbody, hKerase, -, -, -, -, -, -, -, -,
      hKroot, hKC⟩ :=
    hhistory.2.1 k a.val_index (S.a a.round) a ha hk hemit hkn
      ⟨(derive_named S.E S.cfg D).h_F, Fn.root⟩ hp
  have hKF : K = Fn := core.root_injective C D hhistory.1 hDscope
    K Fn (Or.inl hKC) (Or.inr hFD) hKroot.symm
  subst hKF
  -- the finality voter's head is held at its pre-tick state, and its derived
  -- justified block is the finalized block
  have hHk : H ∈ (NamedRun.stateBefore S rho k a.val_index).st.bodies := hHbody
  have hcoh := (Proofs.NamedRuntime.stateBefore_invariants S rho k a.val_index).1.1.1
  have hσ : (Internal.NamedOutageEntry.actionReadFrom S
      (NamedRun.stateBefore S rho k a.val_index) a.round).st.core.σ H.erase =
        derive_named S.E S.cfg H := hcoh.2.2.2.2 H hHk
  have hJH : (derive_named S.E S.cfg H).J = (NamedRun.stateBefore S rho i v).st.core.F := by
    rw [← hσ, ← hKerase, hFE, hDF]
  by_cases hzJ : (derive_named S.E S.cfg H).h_j = 0
  · exact Or.inl (hJH.symm.trans
      (NamedJustificationCertificates.justified_zero_is_genesis S.E S.cfg H hzJ))
  obtain ⟨J, hJH', hJE, Q', hQ', hrows'⟩ :=
    NamedJustificationCertificates.justification_certificate S.E S.cfg H hzJ
  obtain ⟨signer', hsQ', hsHon'⟩ := quorum_honest_member S rho Q' hQ' hbad
  obtain ⟨carrier', a', hcarrier', hrow', hsigner', hp'⟩ := hrows' signer' hsQ'
  have ha' : a'.val_index ∈ rho.honest := by simpa only [hsigner'] using hsHon'
  obtain ⟨j', hj', received', hacc', hsend', hem'⟩ :=
    NamedOutageProvenance.honest_held_ancestor_row_emission S rho
      core.toNamedUnforgeable k a.val_index hHk hcarrier' hrow' ha'
  obtain ⟨k', hk', hemit'⟩ := hem'
  have hk'j' : k' ≤ j' :=
    row_emission_index_le_block_acceptance S rho core a.val_index carrier' j' received'
      hacc' a' hrow' ha' k' hk' hemit' hsend'
  have hk'i : k' < i := lt_of_le_of_lt hk'j' (hj'.trans hki)
  have hk'n : k' < n := lt_of_lt_of_le hk'i hi
  obtain ⟨source, entry, hsourceScope, hsourceHeld, hentryScope, hentryHeld,
      hval, htime, hcreate, hselector, hfields, hheight, htarget, herase,
      hancestor, hsameHeight, hroot, hentryC⟩ :=
    hhistory.2.2.1 k' a'.val_index (S.a a'.round) a' ha' hk' hemit' hk'n
      (derive_named S.E S.cfg H).h_j J.root false hp'
  have heq : entry = J := core.root_injective C H hhistory.1 hHrun
    entry J (Or.inl hentryC) (Or.inr hJH') hroot
  subst heq
  -- the FG row was emitted strictly before the finality voter's tick
  have hHtime : H ∈ (NamedRun.stateBeforeTime S rho (S.a a.round) a.val_index).st.bodies := by
    have hst : NamedRun.stateBefore S rho k a.val_index =
        NamedRun.stateBeforeTime S rho (S.a a.round) a.val_index :=
      Proofs.Optimistic.stateBefore_tick_eq_stateBeforeTime S core.toNamedScheduleWellFormed hk
    rw [← hst]
    exact hHk
  have hlt : S.a a'.round < S.a a.round :=
    (honest_held_ancestor_row_before_time S rho core.toNamedScheduleWellFormed
      core.toNamedUnforgeable a.val_index (S.a a.round) hHtime hcarrier' hrow' ha').1
  exact Or.inr ⟨k', a', entry, source, ha', hk'i, hk', hemit',
    Proofs.NamedRuntime.blockInRun_of_ancestor S rho hHrun hJH',
    hJE.trans hJH, hentryC, hselector, herase, k, a.val_index, a.round, hki, hk, hlt⟩


end DecoupledConsensusModel.Proofs.NamedOutageHistory.HistoryProofs

end
