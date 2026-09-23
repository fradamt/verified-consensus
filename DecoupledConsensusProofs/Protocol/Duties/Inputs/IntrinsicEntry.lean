module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.OutageInputs
public import DecoupledConsensusProofs.Protocol.ChainState.EntryHeight
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.ActionSources

@[expose] public section

/-! Local entry producers under the two-clause pre-outage history condition.
These are local producers. They do not prove all-reader holding or a joint step.
-/
namespace DecoupledConsensusModel.Proofs.NamedIntrinsicEntry
open Execution Internal.NamedOutageEntry Internal.NamedStableChainOutage
open Internal.NamedJointOutage
variable {V : Type} [DecidableEq V] [Fintype V]

private theorem stable_full_prefix_held (S : Setup V) (rho : NamedRun V)
    (v : V) (s : Round) (P : Block V) (hstable : stableAt S rho v s P) :
    ∃ Pn : NamedBlock V,
      Pn ∈ (roundConfirmationRead S rho v s).st.bodies ∧ Pn.erase = P := by
  obtain ⟨G, hG, hPG⟩ := hstable
  let n := roundConfirmationRead S rho v s
  have hcoh : Proofs.NamedStore.Coherent S.E S.cfg n.st :=
    NamedStore.coherent_clock S.E S.cfg _ (S.a s)
      (Proofs.NamedRuntime.stateBeforeTime_invariants S rho (S.a s) v).1.1.1
  have hmem : G ∈ n.st.core.T :=
    Proofs.NamedConfirmationMembership.frame_confirmation_candidate_mem n.cache
      S.E S.hc n.st.core.toHealing n.st.core.s G hG
  have hP := Proofs.NamedStoreRoots.core_ancestor_mem S.E S.cfg n.st hcoh hmem hPG
  rw [hcoh.1] at hP
  exact Finset.mem_image.mp hP

theorem stable_full_prefix_scoped (S : Setup V) (rho : NamedRun V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key))
    (v : V) (hv : v ∈ rho.honest) (s : Round) (P : Block V)
    (hstable : stableAt S rho v s P) :
    ∃ Pn : NamedBlock V,
      Pn ∈ (roundConfirmationRead S rho v s).st.bodies ∧
      Pn.erase = P ∧ NamedRun.blockInRun S rho Pn := by
  obtain ⟨Pn, hheld, he⟩ := stable_full_prefix_held S rho v s P hstable
  refine ⟨Pn, hheld, he, ?_⟩
  have hstrict : Pn ∈ (NamedRun.stateBeforeTime S rho (S.a s) v).st.bodies := hheld
  obtain ⟨i, hi, _⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho hsorted (S.a s)
  rw [hi] at hstrict
  exact Proofs.NamedRuntime.blockInRun_of_direct S rho
    (Proofs.NamedRuntime.directBlock_of_prefix S rho hv i hstrict)

/-- Membership for both successful source-selector arms. No source, Q2,
or reader-membership hypothesis is supplied from outside the actual store. -/
private theorem frame_fg_source_mem (S : Setup V) (cache : DecoupledConsensusModel.Protocol.Cache V)
    (st : Protocol.NamedStore V) (r : Round)
    (hinv : Proofs.NamedConfirmationMembership.Invariant S.E S.cfg st)
    {raw : Block V}
    (hs : Protocol.fg_source_with (NamedProfile.gradeContract cache)
      S.E S.hc st.core.toHealing r
      (Protocol.grade2_block_with (NamedProfile.gradeContract cache)
        S.E S.hc st.core.toHealing r) = some raw) : raw ∈ st.core.T :=
  NamedActionSources.frame_fg_source_mem S cache st r hinv hs

theorem emitted_height_signed_source (S : Setup V) (rho : NamedRun V)
    {a : NamedAttestation V}
    (hem : NamedRun.emits S rho a.val_index (.attest a) (S.a a.round))
    {h : Height} {root : BlockId} {timeout : Bool}
    (hp : a.height_pair = .vote h root timeout) :
    ∃ i : Nat, ∃ source entry : NamedBlock V,
      SignedSourceAt S rho i a source entry ∧
      (Protocol.derive_named S.E S.cfg source).h = h ∧
      entry.root = root := by
  obtain ⟨i, hi, ho, hrow, _, hr, _, _⟩ :=
    Proofs.NamedOutageInputs.emitted_attestation_stages S rho hem
  let n := actionReadFrom S (NamedRun.stateBefore S rho i a.val_index) a.round
  let gc := NamedProfile.gradeContract n.cache
  have hinv := Proofs.NamedOutageInputs.action_read_invariant S rho i a.val_index a.round
  have hcoh : Proofs.NamedStore.Coherent S.E S.cfg n.st := hinv.1.1
  have hpair : (Protocol.NamedActions.round_action_with gc S.E S.hc
      (S.node a.val_index) n.st.core.toHealing n.record).2.height_pair =
      .vote h root timeout := by
    change (Protocol.NamedDuties.attest_with gc S.E S.hc (S.node a.val_index)
      n.st n.record).2.2.height_pair = _
    rw [hrow]
    exact hp
  obtain ⟨nu, hfields⟩ := Proofs.NamedActions.round_action_names_source gc S.E S.hc
    (S.node a.val_index) n.st.core.toHealing n.record h root timeout hpair
  change (Protocol.fg_source_with gc S.E S.hc n.st.core.toHealing
      (S.hc.round_of n.st.core.s)
      (Protocol.grade2_block_with gc S.E S.hc n.st.core.toHealing
        (S.hc.round_of n.st.core.s))).map
      (fun q => ((n.st.core.σ q).h, (n.st.core.σ q).T_h.root,
        (n.st.core.σ q).nj)) = some (h, root, nu) at hfields
  rw [← hr] at hfields
  obtain ⟨raw, hraw, hvalues⟩ := Option.map_eq_some_iff.mp hfields
  have hmem : raw ∈ n.st.core.T := frame_fg_source_mem S n.cache n.st a.round hinv hraw
  rw [hcoh.1] at hmem
  obtain ⟨source, hsource, he⟩ := Finset.mem_image.mp hmem
  rw [← he] at hraw hvalues
  rw [hcoh.2.2.2.2 source hsource] at hvalues
  have hheight : (Protocol.derive_named S.E S.cfg source).h = h :=
    congrArg Prod.fst hvalues
  have hroot : (Protocol.derive_named S.E S.cfg source).T_h.root = root :=
    congrArg (fun x : Height × BlockId × Bool => x.2.1) hvalues
  obtain ⟨entry, hentry, heEntry, hentryHeight⟩ :=
    Proofs.NamedEntryHeight.entry_ancestor_same_height S.E S.cfg source
  have heroot : entry.root = root :=
    (Proofs.NamedWire.erase_root entry).symm.trans ((congrArg Block.root heEntry).trans hroot)
  refine ⟨i, source, entry, ?_, hheight, heroot⟩
  refine ⟨hi, ho, hrow, hsource, hraw, hentry, heEntry, hentryHeight, timeout, ?_⟩
  simpa only [hheight, heroot] using hp

private theorem signed_source_entry_scope (S : Setup V) (rho : NamedRun V)
    {i : Nat} {a : NamedAttestation V} {source entry : NamedBlock V}
    (ha : a.val_index ∈ rho.honest)
    (hs : SignedSourceAt S rho i a source entry) :
    NamedRun.blockInRun S rho source ∧ NamedRun.blockInRun S rho entry := by
  rcases hs with ⟨_, _, _, hsource, _, hentry, _⟩
  have hpre : source ∈ (NamedRun.stateBefore S rho i a.val_index).st.bodies := hsource
  have hscope := Proofs.NamedRuntime.blockInRun_of_direct S rho
    (Proofs.NamedRuntime.directBlock_of_prefix S rho ha i hpre)
  exact ⟨hscope, Proofs.NamedRuntime.blockInRun_of_ancestor S rho hscope hentry⟩

private theorem signed_entry_pre_boundary (S : Setup V) (rho : NamedRun V)
    (b0 : Time) (P : NamedBlock V) (hP : NamedRun.blockInRun S rho P)
    (hno : NoHonestConflictAbove S rho b0 P.erase)
    {i : Nat} {a : NamedAttestation V} {source entry : NamedBlock V}
    (ha : a.val_index ∈ rho.honest)
    (hs : SignedSourceAt S rho i a source entry)
    (ht : S.a a.round < b0) :
    NamedBlock.compatible P entry = true := by
  have hentryScope := (signed_source_entry_scope S rho ha hs).2
  rcases hs with ⟨hi, hem, _, _, _, _, _, _, timeout, hp⟩
  exact hno.1 P hP rfl a (S.a a.round) ha ⟨i, hi, hem⟩ ht
    _ entry.root timeout hp entry hentryScope rfl

/-- The scalar cut is an internal certificate for the chosen first action.
It is not an added outer outage premise. The r=0 case is vacuous. -/
theorem initial_intrinsic_history (S : Setup V) (rho : NamedRun V)
    (b0 : Time) (P : NamedBlock V) (r : Round)
    (hP : NamedRun.blockInRun S rho P)
    (hno : NoHonestConflictAbove S rho b0 P.erase)
    (hcut : S.a (r - 1) < b0) : IntrinsicHighEntryHistory S rho P r := by
  intro h entry he
  obtain ⟨i, a, source, ha, har, hs, _hheight⟩ := he
  have ht : S.a a.round < b0 :=
    (Assembly.a_mono S (Nat.le_sub_one_of_lt har)).trans_lt hcut
  exact signed_entry_pre_boundary S rho b0 P hP hno ha hs ht

end DecoupledConsensusModel.Proofs.NamedIntrinsicEntry

end
