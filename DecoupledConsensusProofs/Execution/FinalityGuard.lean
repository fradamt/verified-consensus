module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Handlers.FinalizationBridge
public import DecoupledConsensusProofs.Protocol.ChainState.FinalityCertificates
public import DecoupledConsensusProofs.Execution.OutageProvenance
public import DecoupledConsensusProofs.Objects.AwakeWindowQuorum

@[expose] public section

namespace DecoupledConsensusModel.Proofs.NamedFinalityGuard
open Execution Internal.NamedOutageEntry Internal.NamedStableChainOutage
variable {V : Type} [DecidableEq V] [Fintype V]

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

omit [Fintype V] in
private theorem genesis_preceq (B : NamedBlock V) : NamedBlock.Preceq .genesis B := by
  induction B with
  | genesis => simp [NamedBlock.Preceq, NamedBlock.preceq]
  | node parent s root votes support rows proposer ih =>
    simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true]
    exact Or.inr ih

private theorem indexed_finalizer_compatible
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (s : Round)
    (hexec : OutageExecution S rho b0 b1) (hmargin : FormationMargin S s b0)
    (hsleep : OutageSleepyThroughout S rho)
    (Pn : NamedBlock V) (hPn : NamedRun.blockInRun S rho Pn)
    (hno : NoHonestConflictAbove S rho b0 Pn.erase)
    (reader : V) (hreader : reader ∈ rho.honest) (i : Nat)
    (hbefore : ∀ j e, j < i → rho.events[j]? = some e → e.time < b0) :
    ∃ F : NamedBlock V,
      F ∈ (NamedRun.stateBefore S rho i reader).st.bodies ∧
      F.erase = (NamedRun.stateBefore S rho i reader).st.core.F ∧
      NamedBlock.compatible Pn F = true := by
  have hcoh : Proofs.NamedStore.Coherent S.E S.cfg
      (NamedRun.stateBefore S rho i reader).st :=
    (Proofs.NamedRuntime.stateBefore_invariants S rho i reader).1.1.1
  obtain ⟨D, hD, hDF, _⟩ :=
    NamedFinalizationBridge.finalization_carrier_stateBefore S rho i reader
  by_cases hz : (Protocol.derive_named S.E S.cfg D).h_F = 0
  · have hgen := NamedFinalityCertificates.finalized_zero_is_genesis S.E S.cfg D hz
    refine ⟨.genesis, hcoh.2.2.1.1, hgen.symm.trans hDF, ?_⟩
    simp only [NamedBlock.compatible, Bool.or_eq_true]
    exact Or.inr (genesis_preceq Pn)
  · obtain ⟨F, hFD, hFErase, Q, hQ, hrows⟩ :=
      NamedFinalityCertificates.finality_certificate S.E S.cfg D hz
    have hFheld := ancestor_body_mem hcoh.2.2.1 hD hFD
    have hDscope := Proofs.NamedRuntime.blockInRun_of_direct S rho
      (Proofs.NamedRuntime.directBlock_of_prefix S rho hreader i hD)
    have hFscope := Proofs.NamedRuntime.blockInRun_of_ancestor S rho hDscope hFD
    have hbad := Proofs.NamedOutageInputs.boundary_faulty_lt_quorum S rho b0 b1 s hexec hmargin
      hsleep
    obtain ⟨signer, hsignerQ, hsignerHon⟩ := quorum_honest_member S rho Q hQ hbad
    obtain ⟨carrier, a, hcarrierD, hrow, hsigner, hpair⟩ := hrows signer hsignerQ
    have haHon : a.val_index ∈ rho.honest := by simpa only [hsigner] using hsignerHon
    obtain ⟨j, hj, received, hacc, hsend, hem⟩ :=
      NamedOutageProvenance.honest_held_ancestor_row_emission S rho
        hexec.core.toNamedUnforgeable i reader hD hcarrierD hrow haHon
    obtain ⟨e, he, _, het⟩ := hacc.1.2
    have hreceived : received < b0 := by simpa only [het] using hbefore j e hj he
    have hsent : S.a a.round < b0 := hsend.trans_lt hreceived
    refine ⟨F, hFheld, hFErase.trans hDF, ?_⟩
    exact hno.2 Pn hPn rfl a (S.a a.round) haHon hem hsent
      _ F.root hpair F hFscope rfl

omit [DecidableEq V] [Fintype V] in
private theorem event_prefix_before_boundary (rho : NamedRun V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key))
    (i : Nat) (e : NamedEvent V) (he : rho.events[i]? = some e)
    (b0 : Time) (ht : e.time < b0) :
    ∀ j earlier, j < i → rho.events[j]? = some earlier → earlier.time < b0 := by
  intro j earlier hj hEarlier
  obtain ⟨hjLen, hjGet⟩ := List.getElem?_eq_some_iff.mp hEarlier
  obtain ⟨hiLen, hiGet⟩ := List.getElem?_eq_some_iff.mp he
  have hkey := (List.pairwise_iff_getElem.mp hsorted) j i hjLen hiLen hj
  rw [hjGet, hiGet] at hkey
  have htime : earlier.time ≤ e.time := by
    rcases Prod.Lex.le_iff.mp hkey with hlt | ⟨heq, _⟩
    · exact hlt.le
    · exact heq.le
  exact htime.trans_lt ht

/-- Produce the actual full held finalized representative at the strict read.
The finality clause is used at every possible signed finality height. -/
theorem finalized_representative_compatible_before_boundary
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (s : Round)
    (hexec : OutageExecution S rho b0 b1) (hmargin : FormationMargin S s b0)
    (hsleep : OutageSleepyThroughout S rho)
    (Pn : NamedBlock V) (hPn : NamedRun.blockInRun S rho Pn)
    (hno : NoHonestConflictAbove S rho b0 Pn.erase)
    (reader : V) (hreader : reader ∈ rho.honest) (t : Time) (ht : t ≤ b0) :
    ∃ F : NamedBlock V,
      F ∈ (NamedRun.stateBeforeTime S rho t reader).st.bodies ∧
      F.erase = (NamedRun.stateBeforeTime S rho t reader).st.core.F ∧
      NamedBlock.compatible Pn F = true := by
  obtain ⟨i, hread, hbefore⟩ :=
    Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho hexec.core.sorted t
  rw [hread]
  exact indexed_finalizer_compatible S rho b0 b1 s hexec hmargin hsleep
    Pn hPn hno reader hreader i
    (fun j e hj he => (hbefore j e hj he).trans_le ht)

/-- Actual event-prefix query. Earlier deliveries at this same timestamp
are included in this store; sorted keys give time <= e.time < b0. -/
theorem protected_prefix_held_or_finality_guard_before_boundary
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (s : Round)
    (hexec : OutageExecution S rho b0 b1) (hmargin : FormationMargin S s b0)
    (hsleep : OutageSleepyThroughout S rho)
    (Pn : NamedBlock V) (hPn : NamedRun.blockInRun S rho Pn)
    (hno : NoHonestConflictAbove S rho b0 Pn.erase)
    (reader : V) (hreader : reader ∈ rho.honest)
    (i : Nat) (e : NamedEvent V) (he : rho.events[i]? = some e)
    (ht : e.time < b0) :
    Pn ∈ (NamedRun.stateBefore S rho i reader).st.bodies ∨
      Block.Preceq (NamedRun.stateBefore S rho i reader).st.core.F Pn.erase := by
  have hbefore := event_prefix_before_boundary rho hexec.core.sorted i e he b0 ht
  obtain ⟨F, hF, hErase, hcompat⟩ :=
    indexed_finalizer_compatible S rho b0 b1 s hexec hmargin hsleep
      Pn hPn hno reader hreader i hbefore
  have hcoh : Proofs.NamedStore.Coherent S.E S.cfg
      (NamedRun.stateBefore S rho i reader).st :=
    (Proofs.NamedRuntime.stateBefore_invariants S rho i reader).1.1.1
  simp only [NamedBlock.compatible, Bool.or_eq_true] at hcompat
  rcases hcompat with hPF | hFP
  · exact Or.inl (ancestor_body_mem hcoh.2.2.1 hF hPF)
  · exact Or.inr (by rw [← hErase]; exact Proofs.NamedWire.erase_preceq hFP)

/-- The same protected-prefix query at a strict time read. -/
theorem protected_prefix_held_or_finality_guard_before_boundary_time
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (s : Round)
    (hexec : OutageExecution S rho b0 b1) (hmargin : FormationMargin S s b0)
    (hsleep : OutageSleepyThroughout S rho)
    (Pn : NamedBlock V) (hPn : NamedRun.blockInRun S rho Pn)
    (hno : NoHonestConflictAbove S rho b0 Pn.erase)
    (reader : V) (hreader : reader ∈ rho.honest) (cut : Time) (hcut : cut ≤ b0) :
    Pn ∈ (NamedRun.stateBeforeTime S rho cut reader).st.bodies ∨
      Block.Preceq (NamedRun.stateBeforeTime S rho cut reader).st.core.F Pn.erase := by
  obtain ⟨F, hF, hErase, hcompat⟩ :=
    finalized_representative_compatible_before_boundary
      S rho b0 b1 s hexec hmargin hsleep Pn hPn hno reader hreader cut hcut
  have hcoh : Proofs.NamedStore.Coherent S.E S.cfg
      (NamedRun.stateBeforeTime S rho cut reader).st :=
    (Proofs.NamedRuntime.stateBeforeTime_invariants S rho cut reader).1.1.1
  simp only [NamedBlock.compatible, Bool.or_eq_true] at hcompat
  rcases hcompat with hPF | hFP
  · exact Or.inl (ancestor_body_mem hcoh.2.2.1 hF hPF)
  · exact Or.inr (by rw [← hErase]; exact Proofs.NamedWire.erase_preceq hFP)

end DecoupledConsensusModel.Proofs.NamedFinalityGuard

end
