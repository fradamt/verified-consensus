module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.LayerAHistoryIndices
public import DecoupledConsensusProofs.Execution.EventIndexBridge
public import DecoupledConsensusProofs.Execution.IdxGaps
public import DecoupledConsensusProofs.Execution.ViabilityHistory
public import DecoupledConsensusProofs.Protocol.ChainState.FinalityCertificates
public import DecoupledConsensusProofs.Execution.OutageProvenance

@[expose] public section

/-!
# Index-bounded viability history (task 3)

`held_finalized_on_history` and `held_crossing_on_history`, copied from
`ViabilityHistory.lean` with the index hypotheses `(n: Nat)
(hhistory: LayerAHistoryIdx S rho n C) (hi: i ≤ n)` in place of `(t: Time)
(hhistory: LayerAHistoryOn S rho t C) (hstrict:...)`. `named_common_chain`,
`named_extend`, `genesis_preceq`, `quorum_honest_member`, `ancestor_body_mem`
are unchanged and reused from `ViabilityHistory.lean`.

The provenance step gives an acceptance index `j < i` for the carrying block
at the holder. When that acceptance is a delivery, the carried row's
emission index is `< j` by task 1's `tick_lt_of_deliver_index`. When the
holder instead self-proposed the carrying block (a self-tick acceptance),
the same bound is recorded as a gap (`emission_index_le_self_proposed_carrier`
in `IdxGaps.lean`): it is not closable from the tick-vs-deliver phase trick
alone, since both ticks share phase 0. Either way `k ≤ j < i ≤ n` closes the
index bound the history clause needs.
-/


namespace DecoupledConsensusModel.Proofs.NamedOutageHistory.ViabilityHistory
open Execution Protocol
open Internal.NamedOutageEntry.History
open DecoupledConsensusModel.Proofs.NamedOutageHistory.ViabilityHistoryTime
variable {V : Type} [DecidableEq V] [Fintype V]


/-- The carried row's emission index sits at or before the carrying block's
own acceptance index, whichever branch (self-tick or delivery) that
acceptance took. Public: reused by the justification-history index migration
(task 4, `JustificationHistoryIndices.lean`), which needs the same provenance step. -/
theorem row_emission_index_le_block_acceptance
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    (v : V) (carrier : NamedBlock V) (j : Nat) (received : Time)
    (hacc : NamedRun.acceptsAt S rho j v (.block carrier) received)
    (a : NamedAttestation V) (hrow : a ∈ carrier.attestations) (ha : a.val_index ∈ rho.honest)
    (k : Nat) (hk : rho.events[k]? = some (.tick a.val_index (S.a a.round)))
    (hemit : NamedObject.attest a ∈ NamedRun.emittedAt S rho k a.val_index (S.a a.round))
    (hsend : S.a a.round ≤ received) : k ≤ j := by
  obtain ⟨hcallIdx, e, he, _, het⟩ := hacc.1
  change NamedRun.processesAtIndex S rho j v (.block carrier) at hcallIdx
  rcases hcallIdx with ⟨time, hji, hemC⟩ | ⟨time, hji⟩
  · have heq : NamedEvent.tick v time = e := Option.some.inj (hji.symm.trans he)
    have htime : time = received := by
      simpa only [NamedEvent.time] using (congrArg NamedEvent.time heq).trans het
    subst htime
    exact emission_index_le_self_proposed_carrier S rho core j v time carrier
      hji hemC a hrow ha k _ hk hemit hsend
  · have heq : NamedEvent.deliver v (.block carrier) time = e :=
      Option.some.inj (hji.symm.trans he)
    have htime : time = received := by
      simpa only [NamedEvent.time] using (congrArg NamedEvent.time heq).trans het
    subst htime
    exact (tick_lt_of_deliver_index rho core.sorted hji hk hsend).le


/-- The exact progress crossing, with either timeout flag, is on the history
chain, index-bounded version. -/
theorem held_crossing_on_history
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    (n : Nat) (C : NamedBlock V) (hhistory : LayerAHistoryIdx S rho n C)
    (i : Nat) (v : V) (hv : v ∈ rho.honest) (hi : i ≤ n)
    (hbad : S.E.electorate.weightOf (Finset.univ \ rho.honest) < S.E.q)
    (D : NamedBlock V) (hD : D ∈ (NamedRun.stateBefore S rho i v).st.bodies)
    (h : Height) (hpos : 1 ≤ h) (hlt : h < (derive_named S.E S.cfg D).h) :
    ∃ X : NamedBlock V, NamedBlock.Preceq X D ∧
      (derive_named S.E S.cfg X).h = h ∧ NamedBlock.Preceq X C := by
  have hDscope := Proofs.NamedRuntime.blockInRun_of_direct S rho
    (Proofs.NamedRuntime.directBlock_of_prefix S rho hv i hD)
  obtain ⟨X, hXD, hXheight, Q, hQ, hrows⟩ :=
    NamedFinalityCertificates.height_crossing S.E S.cfg D h hpos hlt
  obtain ⟨signer, hsignerQ, hsignerHon⟩ := quorum_honest_member S rho Q hQ hbad
  obtain ⟨carrier, a, hcarrier, hrow, hsigner, hp⟩ := hrows signer hsignerQ
  have ha : a.val_index ∈ rho.honest := by simpa only [hsigner] using hsignerHon
  have hvote : ∃ timeout : Bool, a.height_pair = .vote h X.root timeout := by
    cases heq : a.height_pair with
    | empty => simp only [heq, NamedHeightPair.matchesEntry, Bool.false_eq_true] at hp
    | vote height target timeout =>
      have he : height = h ∧ target = X.root := by
        simpa only [heq, NamedHeightPair.matchesEntry, decide_eq_true_eq] using hp
      exact ⟨timeout, by rw [he.1, he.2]⟩
  obtain ⟨timeout, hvote⟩ := hvote
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
      h X.root timeout hvote
  have heq : entry = X := core.root_injective C D hhistory.1 hDscope
    entry X (Or.inl hentryC) (Or.inr hXD) hroot
  subst entry
  exact ⟨X, hXD, hXheight, hentryC⟩

end DecoupledConsensusModel.Proofs.NamedOutageHistory.ViabilityHistory

end
