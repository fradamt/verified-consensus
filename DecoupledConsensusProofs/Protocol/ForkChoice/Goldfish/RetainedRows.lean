module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.RowTrace
public import DecoupledConsensusProofs.Protocol.Grades.Premises

@[expose] public section


namespace DecoupledConsensusModel.Proofs.NamedOutageClosure
open Execution Internal.NamedOutageEntry Internal.NamedStableChainOutage DecoupledConsensusModel.Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Projections and `latest` -/

omit [DecidableEq V] [Fintype V] in
theorem sgVote_val (a : NamedAttestation V) :
    (Protocol.sgVote a.erase).val_index = a.val_index := rfl

omit [DecidableEq V] [Fintype V] in
theorem sgVote_round (a : NamedAttestation V) :
    (Protocol.sgVote a.erase).round = a.round := rfl

omit [DecidableEq V] [Fintype V] in
theorem sgVote_confirmed (a : NamedAttestation V) :
    (Protocol.sgVote a.erase).confirmed = a.confirmed := rfl

theorem latest_mem {inputs : Finset (Protocol.SGVote V)} {x : Protocol.SGVote V}
    (hx : x ∈ Internal.OutageEntryRevision.latest inputs) :
    x ∈ inputs ∧ ∀ y ∈ inputs, y.round ≤ x.round := by
  simpa only [Internal.OutageEntryRevision.latest, Finset.mem_filter] using hx

theorem latest_round_eq {inputs : Finset (Protocol.SGVote V)} {x y : Protocol.SGVote V}
    (hx : x ∈ Internal.OutageEntryRevision.latest inputs)
    (hy : y ∈ Internal.OutageEntryRevision.latest inputs) : x.round = y.round :=
  Nat.le_antisymm ((latest_mem hy).2 x (latest_mem hx).1) ((latest_mem hx).2 y (latest_mem hy).1)

theorem latest_nonempty {inputs : Finset (Protocol.SGVote V)} (h : inputs.Nonempty) :
    (Internal.OutageEntryRevision.latest inputs).Nonempty := by
  obtain ⟨x, hx, hmax⟩ := Finset.exists_max_image inputs (fun u => u.round) h
  refine ⟨x, ?_⟩
  simpa only [Internal.OutageEntryRevision.latest, Finset.mem_filter] using ⟨hx, hmax⟩

theorem latest_ge_of_mem {inputs : Finset (Protocol.SGVote V)} {x y : Protocol.SGVote V}
    (hx : x ∈ Internal.OutageEntryRevision.latest inputs) (hy : y ∈ inputs) :
    y.round ≤ x.round := (latest_mem hx).2 y hy

/-! ## Traceback of a retained raw row -/

/-- A block held at an honest reader's strict read is a run block. -/
theorem held_blockInRun (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (reader : V) (hreader : reader ∈ rho.honest)
    (t : Time) {H : NamedBlock V}
    (hH : H ∈ (NamedRun.stateBeforeTime S rho t reader).st.bodies) :
    NamedRun.blockInRun S rho H := by
  obtain ⟨n, hread, _⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho sch.sorted t
  rw [hread] at hH
  exact Proofs.NamedRuntime.blockInRun_of_direct S rho
    (Proofs.NamedRuntime.directBlock_of_prefix S rho hreader n hH)

/-- Every retained raw token of an honest sender, at an honest reader's strict
read, is the SG projection of an original full row that the sender emitted at
its own round action, strictly before the read. -/
theorem retained_trace (S : Setup V) (rho : NamedRun V)
    (sch : NamedScheduleWellFormed S rho) (auth : NamedUnforgeable S rho)
    (cut : Time) (reader : V) (sr : Round) (u : V) (hu : u ∈ rho.honest)
    {x : Protocol.SGVote V}
    (hx : x ∈ Internal.OutageEntryRevision.retainedRaw S
      (NamedRun.stateBeforeTime S rho cut reader).st.core sr cut u) :
    ∃ a : NamedAttestation V, a.val_index = u ∧ a.round = x.round ∧
      Protocol.sgVote a.erase = x ∧
      x.round ∈ Internal.OutageEntryRevision.retainedRounds S sr ∧
      S.a a.round < cut ∧ NamedRun.emits S rho u (.attest a) (S.a a.round) := by
  obtain ⟨hpool, hfields⟩ := Finset.mem_filter.mp hx
  obtain ⟨k, hk, hxk⟩ := Finset.mem_biUnion.mp hpool
  obtain ⟨a, hround, hproj, hmem⟩ := pool_token_row S rho sch cut reader hxk
  have hxround : x.round = a.round := by rw [← hproj, sgVote_round]
  have hval : a.val_index = u := by
    have : x.val_index = u := hfields.1
    rw [← hproj, sgVote_val] at this
    exact this
  subst hval
  obtain ⟨hlt, hem⟩ := honest_held_row_before_cut S rho sch auth cut reader hmem hu
  exact ⟨a, rfl, hxround.symm, hproj,
    by rw [hxround, hround]; exact hk, hlt, hem⟩

/-! ## Coverage and open from the stage-1 premises -/

section Premises
variable (S : Setup V) (rho : NamedRun V)

/-- A retained raw token of an honest sender, from a round at or above the
stable round, covers the protected prefix at the reader. This is the step the
 `HonestConfirmedAbove` alone cannot make: `covers` looks the confirmed
root up in the reader's own tree, which is what `HonestHeadHeldAbove` supplies. -/
theorem retained_covers_at
    (sch : NamedScheduleWellFormed S rho) (auth : NamedUnforgeable S rho)
    (roots : NamedRootCollisionFree S rho) (b0 tau : Time) (htau : tau ≤ b0)
    (hgrid : OnDeltaGrid S tau)
    (s : Round) (P : Block V)
    (hconf : HonestConfirmedAtOrAbove S rho b0 s P)
    (hhead : HonestHeadHeldAbove S rho b0 s P)
    (reader : V) (hreader : reader ∈ rho.honest) (u : V) (hu : u ∈ rho.honest)
    (hFP : Block.Preceq (NamedRun.stateBeforeTime S rho tau reader).st.core.F P)
    (sr : Round) {x : Protocol.SGVote V}
    (hx : x ∈ Internal.OutageEntryRevision.retainedRaw S
      (NamedRun.stateBeforeTime S rho tau reader).st.core sr tau u)
    (hs : s ≤ x.round) :
    Internal.OutageEntryRevision.covers (NamedRun.stateBeforeTime S rho tau reader).st.core P x
      = true := by
  obtain ⟨a, hval, haround, hproj, _, hlt, hem⟩ :=
    retained_trace S rho sch auth tau reader sr u hu hx
  obtain ⟨_, _, _, K, _, hkey⟩ := Proofs.NamedOutageInputs.emitted_attestation_head S rho hem
  have hsa : s ≤ a.round := by rw [haround]; exact hs
  have hlt0 : S.a a.round < b0 := lt_of_lt_of_le hlt htau
  have hdelta : S.a a.round + S.E.Δ ≤ tau :=
    a_add_delta_le_of_lt_grid S tau hgrid a.round hlt
  obtain ⟨H, hH, hroot, _, _⟩ :=
    hhead a (S.a a.round) (hval ▸ hu) (hval ▸ hem) (hdelta.trans htau) hsa reader hreader tau
      hdelta hFP K.root hkey
  have hHrun : NamedRun.blockInRun S rho H := held_blockInRun S rho sch reader hreader tau hH
  have hcover : Block.Preceq P H.erase :=
    hconf a (S.a a.round) (hval ▸ hu) (hval ▸ hem) hlt0 hsa K.root hkey H hHrun hroot
  have hfind : Block.find? (NamedRun.stateBeforeTime S rho tau reader).st.core.T H.root =
      some H.erase := by
    simpa only [Proofs.NamedWire.erase_root] using
      held_find_at_strict S rho sch roots reader hreader tau H hH
  have hxconf : x.confirmed = some H.root := by
    rw [← hproj, sgVote_confirmed, hkey, hroot]
  unfold Internal.OutageEntryRevision.covers
  rw [hxconf]
  show (match Block.find? (NamedRun.stateBeforeTime S rho tau reader).st.core.T H.root with
    | none => false
    | some B => Block.preceq P B) = true
  rw [hfind]
  exact hcover

/-- The boundary instance, kept at its historical signature for callers that
inventory at `b0` itself. -/
theorem retained_covers
    (sch : NamedScheduleWellFormed S rho) (auth : NamedUnforgeable S rho)
    (roots : NamedRootCollisionFree S rho) (b0 : Time) (hgrid : OnDeltaGrid S b0)
    (s : Round) (P : Block V)
    (hconf : HonestConfirmedAtOrAbove S rho b0 s P)
    (hhead : HonestHeadHeldAbove S rho b0 s P)
    (reader : V) (hreader : reader ∈ rho.honest) (u : V) (hu : u ∈ rho.honest)
    (hFP : Block.Preceq (NamedRun.stateBeforeTime S rho b0 reader).st.core.F P)
    (sr : Round) {x : Protocol.SGVote V}
    (hx : x ∈ Internal.OutageEntryRevision.retainedRaw S
      (NamedRun.stateBeforeTime S rho b0 reader).st.core sr b0 u)
    (hs : s ≤ x.round) :
    Internal.OutageEntryRevision.covers (NamedRun.stateBeforeTime S rho b0 reader).st.core P x
      = true :=
  retained_covers_at S rho sch auth roots b0 b0 le_rfl hgrid s P hconf hhead reader hreader u hu
    hFP sr hx hs

/-- The same row is body-ready at the reader: its head is found, stamped and
compatible with the reader's finalized prefix. -/
theorem retained_bodyReady
    (sch : NamedScheduleWellFormed S rho)
    (roots : NamedRootCollisionFree S rho) (b0 : Time) (s : Round) (P : Block V)
    (hhead : HonestHeadHeldAbove S rho b0 s P)
    (reader : V) (hreader : reader ∈ rho.honest) (u : V) (hu : u ∈ rho.honest)
    {a : NamedAttestation V} (hval : a.val_index = u) (hs : s ≤ a.round)
    (hlt : S.a a.round + S.E.Δ ≤ b0) (hem : NamedRun.emits S rho u (.attest a) (S.a a.round))
    (cut cutoff : Time) (hcut : S.a a.round + S.E.Δ ≤ cut)
    (hFP : Block.Preceq (NamedRun.stateBeforeTime S rho cut reader).st.core.F P)
    (hcutoff : S.a a.round + S.E.Δ ≤ cutoff) :
    DecoupledConsensusModel.Protocol.bodyReady
        (NamedRun.stateBeforeTime S rho cut reader).st.core.toHealing.gradeView
        (NamedRun.stateBeforeTime S rho cut reader).st.core.F cutoff
        (Protocol.sgVote a.erase) = true := by
  obtain ⟨_, _, _, K, _, hkey⟩ := Proofs.NamedOutageInputs.emitted_attestation_head S rho hem
  obtain ⟨H, hH, hroot, hcompat, hstamp⟩ :=
    hhead a (S.a a.round) (hval ▸ hu) (hval ▸ hem) hlt hs reader hreader cut hcut hFP
      K.root hkey
  have hfind : Block.find? (NamedRun.stateBeforeTime S rho cut reader).st.core.T H.root =
      some H.erase := by
    simpa only [Proofs.NamedWire.erase_root] using
      held_find_at_strict S rho sch roots reader hreader cut H hH
  have hconfirmed : (Protocol.sgVote a.erase).confirmed = some H.root := by
    rw [sgVote_confirmed, hkey, hroot]
  simp only [DecoupledConsensusModel.Protocol.bodyReady, hconfirmed]
  change (match Block.find? (NamedRun.stateBeforeTime S rho cut reader).st.core.T H.root with
    | none => false
    | some head => stampedBefore
        (NamedRun.stateBeforeTime S rho cut reader).st.core.timestamp_block cutoff head &&
          Block.compatible head
            (NamedRun.stateBeforeTime S rho cut reader).st.core.F) = true
  rw [hfind]
  exact Bool.and_eq_true_iff.mpr ⟨hstamp cutoff hcutoff, hcompat⟩

end Premises

#print axioms latest_nonempty
#print axioms retained_trace
#print axioms retained_covers_at
#print axioms retained_covers
#print axioms retained_bodyReady

end DecoupledConsensusModel.Proofs.NamedOutageClosure

end
