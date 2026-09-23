module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusModel.Protocol.Handlers
public import DecoupledConsensusProofs.Protocol.Handlers.NamedStore
public import DecoupledConsensusProofs.Protocol.Handlers.CarriedAdmissionChecks

@[expose] public section

/-! Named F1 proofs. SG-projection dedup is unchanged. New named
metadata is stored only when the one existing on_sg_vote call admits its row.
No named event runtime or acceptance/relay relation is asserted here. -/
namespace DecoupledConsensusModel.Proofs.NamedAdmission
open Protocol.NamedAdmission
open Execution
variable {V : Type} [DecidableEq V]

/-- The metadata wrapper uses exactly the previous SG handler result. -/
theorem admit_row_core (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (row : NamedAttestation V) : (admit_row hc st row).core =
      Protocol.on_sg_vote hc st.core row.erase := by
  dsimp only [admit_row]
  split_ifs <;> rfl

theorem admit_row_bodies (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (row : NamedAttestation V) : (admit_row hc st row).bodies = st.bodies := by
  dsimp only [admit_row]
  split_ifs <;> rfl

theorem admit_row_of_core_noop (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (row : NamedAttestation V) (h : Protocol.on_sg_vote hc st.core row.erase = st.core) :
    admit_row hc st row = st := by simp [admit_row, h]

/-- Local outcome of the existing handler, without a copied admission guard. -/
private theorem sg_outcome (hc : Protocol.HealConfig) (st : Protocol.Store V)
    (a : CombinedAttestation V) :
    Protocol.on_sg_vote hc st a = st ∨
      (a ∉ st.sg_pool a.round ∧
       a ∈ (Protocol.on_sg_vote hc st a).sg_pool a.round ∧
       ∀ r, (Protocol.on_sg_vote hc st a).sg_votes r =
         if r = a.round then st.sg_votes r ++ [a] else st.sg_votes r) := by
  by_cases hguard : a.round < hc.round_of st.s - hc.η_SG ∨ hc.round_of st.s < a.round ∨
      a.confirmed ∈ Protocol.round_votes st a ∨ (Protocol.round_votes st a).card = 2
  · exact Or.inl (if_pos hguard)
  · right
    refine ⟨?_, ?_, ?_⟩
    · intro ha
      apply hguard
      right; right; left
      unfold Protocol.round_votes
      exact Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, rfl⟩, rfl⟩
    · simp [Protocol.on_sg_vote, hguard, Protocol.Store.sg_pool]
    · intro r
      simp only [Protocol.on_sg_vote, if_neg hguard]

/-- Pool projection gives membership of the selected original named row's erasure. -/
theorem pool_view_mem (st : Protocol.NamedStore V) (hPool : NamedStore.PoolView st)
    (row : NamedAttestation V) (hrow : row ∈ st.sg_rows row.round) :
    row.erase ∈ st.core.sg_pool row.round := by
  unfold Protocol.Store.sg_pool
  rw [hPool row.round]
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨row, hrow, rfl⟩)


/-- A newly admitted row is retained with its exact named payload. -/
theorem admitted_original_row (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (row : NamedAttestation V) (hpre : row.erase ∉ st.core.sg_pool row.round)
    (hpost : row.erase ∈ (Protocol.on_sg_vote hc st.core row.erase).sg_pool row.round) :
    row ∈ (admit_row hc st row).sg_rows row.round := by
  simp [admit_row, hpre, hpost]

theorem admitted_receipt_stamp (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (row : NamedAttestation V) (hpre : row.erase ∉ st.core.sg_pool row.round)
    (hpost : row.erase ∈ (Protocol.on_sg_vote hc st.core row.erase).sg_pool row.round) :
    (admit_row hc st row).core.timestamp_sg_vote (Protocol.sgVote row.erase) =
      some (st.core.t : Stamp) := by
  rw [admit_row_core]
  exact CarriedAdmission.on_sg_vote_new_receipt_stamp hc st.core row.erase hpre hpost

/-- Existing own-bucket projections retain their receipt timestamp. -/
theorem existing_row_stamp (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (hPool : NamedStore.PoolView st) (incoming held : NamedAttestation V)
    (hheld : held ∈ st.sg_rows held.round) :
    (admit_row hc st incoming).core.timestamp_sg_vote (Protocol.sgVote held.erase) =
      st.core.timestamp_sg_vote (Protocol.sgVote held.erase) := by
  rw [admit_row_core]
  exact CarriedAdmission.on_sg_vote_existing_row_stamp hc st.core incoming.erase held.erase
    (pool_view_mem st hPool held hheld)

/-- The row wrapper changes no clock, body, or GF-vote field. -/
theorem admit_row_fixed_fields (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (row : NamedAttestation V) :
    let out := (admit_row hc st row).core
    out.t = st.core.t ∧ out.s = st.core.s ∧ out.T = st.core.T ∧
    out.timestamp_block = st.core.timestamp_block ∧ out.gf_votes = st.core.gf_votes ∧
    out.timestamp_vote = st.core.timestamp_vote := by
  simpa only [admit_row_core, List.foldl_cons, List.foldl_nil] using
    CarriedAdmission.fold_rows_fixed_fields hc [row.erase] st.core

/-- The projected carried fold is exactly the previous SG-row fold in original order. -/
theorem admit_rows_core (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (rows : List (NamedAttestation V)) :
    (admit_rows hc st rows).core =
      (rows.map NamedAttestation.erase).foldl (Protocol.on_sg_vote hc) st.core := by
  induction rows generalizing st with
  | nil => rfl
  | cons row rows ih =>
    simpa only [admit_rows, List.foldl_cons, List.map_cons, admit_row_core] using
      ih (admit_row hc st row)

theorem admit_rows_clock (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (rows : List (NamedAttestation V)) :
    (admit_rows hc st rows).core.t = st.core.t ∧ (admit_rows hc st rows).core.s = st.core.s := by
  rw [admit_rows_core]
  exact ⟨(CarriedAdmission.fold_rows_fixed_fields hc (rows.map NamedAttestation.erase) st.core).1,
    (CarriedAdmission.fold_rows_fixed_fields hc (rows.map NamedAttestation.erase) st.core).2.1⟩

/-- Each carried row uses the store after its exact preceding named row earlierRows. -/
theorem carried_row_prefix (hc : Protocol.HealConfig) (before after : Protocol.NamedStore V)
    (B : NamedBlock V) (earlierRows suffix : List (NamedAttestation V)) (row : NamedAttestation V)
    (hrows : B.attestations = earlierRows ++ row :: suffix)
    (hnew : B ∉ before.bodies) (hheld : B ∈ after.bodies) :
    admit_carried .alsoCarried hc before after B =
      admit_rows hc (admit_row hc (admit_rows hc after earlierRows) row) suffix := by
  simp only [admit_carried, if_pos (And.intro hnew hheld), hrows, admit_rows,
    List.foldl_append, List.foldl_cons]




section Coherence
variable [Fintype V]

private theorem coherent_of_core_fields (E : Env V) (cfg : Protocol.HeightConfig)
    (before after : Protocol.NamedStore V) (h : Proofs.NamedStore.Coherent E cfg before)
    (hT : after.core.T = before.core.T) (hSigma : after.core.σ = before.core.σ)
    (hBodies : after.bodies = before.bodies) (hPool : NamedStore.PoolView after) :
    Proofs.NamedStore.Coherent E cfg after := by
  rcases h with ⟨hTree, hUnique, hParent, _, hDerived⟩
  refine ⟨?_, ?_, ?_, hPool, ?_⟩
  · change after.core.T = after.bodies.image NamedBlock.erase
    rw [hT, hBodies]
    exact hTree
  · intro A hA B hB he
    rw [hBodies] at hA hB
    exact hUnique A hA B hB he
  · change NamedBlock.genesis ∈ after.bodies ∧ _
    rw [hBodies]
    exact hParent
  · intro B hB
    rw [hBodies] at hB
    rw [hSigma]
    exact hDerived B hB

/-- Pool projection and all named-body/derived-map facts survive actual F1 admission. -/
theorem coherent_admit_row (E : Env V) (hc : Protocol.HealConfig)
    (cfg : Protocol.HeightConfig) (st : Protocol.NamedStore V) (row : NamedAttestation V)
    (h : Proofs.NamedStore.Coherent E cfg st) : Proofs.NamedStore.Coherent E cfg (admit_row hc st row) := by
  apply coherent_of_core_fields E cfg st (admit_row hc st row) h
  · rw [admit_row_core]
    exact on_sg_vote_T hc st.core row.erase
  · rw [admit_row_core]
    exact (coreEq_on_sg_vote hc st.core row.erase).σ_eq
  · exact admit_row_bodies hc st row
  · rcases sg_outcome hc st.core row.erase with hNoop | ⟨hpre, hpost, hRows⟩
    · rw [admit_row_of_core_noop hc st row hNoop]
      exact h.2.2.2.1
    · change row.erase ∉ st.core.sg_pool row.round at hpre
      change row.erase ∈ (Protocol.on_sg_vote hc st.core row.erase).sg_pool row.round at hpost
      change ∀ r, (Protocol.on_sg_vote hc st.core row.erase).sg_votes r =
        if r = row.round then st.core.sg_votes r ++ [row.erase] else st.core.sg_votes r at hRows
      intro r
      rw [admit_row_core, hRows r]
      simp only [admit_row, if_pos (And.intro hpre hpost)]
      by_cases hr : r = row.round
      · simp [hr, h.2.2.2.1 row.round, List.map_append]
      · simp [hr, h.2.2.2.1 r]

theorem coherent_admit_rows (E : Env V) (hc : Protocol.HealConfig)
    (cfg : Protocol.HeightConfig) (st : Protocol.NamedStore V)
    (rows : List (NamedAttestation V)) (h : Proofs.NamedStore.Coherent E cfg st) :
    Proofs.NamedStore.Coherent E cfg (admit_rows hc st rows) := by
  induction rows generalizing st with
  | nil => exact h
  | cons row rows ih => exact ih (admit_row hc st row) (coherent_admit_row E hc cfg st row h)

theorem coherent_admit_carried (admission : Protocol.CarriedAdmission) (E : Env V)
    (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig)
    (before after : Protocol.NamedStore V) (B : NamedBlock V)
    (h : Proofs.NamedStore.Coherent E cfg after) :
    Proofs.NamedStore.Coherent E cfg (admit_carried admission hc before after B) := by
  cases admission with
  | alsoCarried =>
    dsimp only [admit_carried]
    split_ifs
    · exact coherent_admit_rows E hc cfg after B.attestations h
    · exact h

theorem coherent_on_block (admission : Protocol.CarriedAdmission) (E : Env V)
    (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig)
    (st : Protocol.NamedStore V) (B : NamedBlock V) (h : Proofs.NamedStore.Coherent E cfg st) :
    Proofs.NamedStore.Coherent E cfg (on_block_with admission E hc cfg st B) :=
  coherent_admit_carried admission E hc cfg st
    (Protocol.NamedStore.process_block_core E hc cfg st B)
    B (NamedStore.coherent_process_block E hc cfg st B h)

private theorem checked_clock (E : Env V) (hc : Protocol.HealConfig) (st : Protocol.Store V)
    (B : Block V) (buildState : Protocol.ChainState V → Protocol.ChainState V) :
    let out := Protocol.on_block_checked_using
      (fun current => Protocol.on_block_using E current B buildState) hc st B
    out.t = st.t ∧ out.s = st.s := by
  dsimp only [Protocol.on_block_checked_using]
  split_ifs
  · simp only [Protocol.on_block_using]
    split_ifs <;> first
      | exact ⟨rfl, rfl⟩
      | exact ⟨by rw [update_finality_time, foldl_on_goldfish_vote_checked_time E],
          by rw [Proofs.Optimistic.update_finality_slot, Proofs.Optimistic.foldl_on_goldfish_vote_checked_slot]⟩
  · exact ⟨rfl, rfl⟩

/-- The shared block earlierRows keeps the receiver clock used for its receipt stamp. -/
theorem process_block_clock (E : Env V) (hc : Protocol.HealConfig)
    (cfg : Protocol.HeightConfig) (st : Protocol.NamedStore V) (B : NamedBlock V) :
    (Protocol.NamedStore.process_block_core E hc cfg st B).core.t = st.core.t ∧
    (Protocol.NamedStore.process_block_core E hc cfg st B).core.s = st.core.s := by
  by_cases hp : B.parent ∈ st.bodies
  · simpa only [Protocol.NamedStore.process_block_core, if_neg (not_not.mpr hp),
      NamedStore.commit_core] using checked_clock E hc st.core B.erase
        (fun parentState => Protocol.named_transition E cfg parentState B)
  · simp [Protocol.NamedStore.process_block_core, hp]

/-- Both the concrete block earlierRows and F1 tail use the same receipt clock. -/
theorem on_block_clock (admission : Protocol.CarriedAdmission) (E : Env V)
    (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig)
    (st : Protocol.NamedStore V) (B : NamedBlock V) :
    (on_block_with admission E hc cfg st B).core.t = st.core.t ∧
    (on_block_with admission E hc cfg st B).core.s = st.core.s := by
  let after := Protocol.NamedStore.process_block_core E hc cfg st B
  have htail : (admit_carried admission hc st after B).core.t = after.core.t ∧
      (admit_carried admission hc st after B).core.s = after.core.s := by
    cases admission with
    | alsoCarried =>
      dsimp only [admit_carried]
      split_ifs
      · exact admit_rows_clock hc after B.attestations
      · exact ⟨rfl, rfl⟩
  exact ⟨htail.1.trans (process_block_clock E hc cfg st B).1,
    htail.2.trans (process_block_clock E hc cfg st B).2⟩

end Coherence

#print axioms admit_row_core
#print axioms admit_row_bodies
#print axioms admit_row_of_core_noop
#print axioms pool_view_mem
#print axioms admitted_original_row
#print axioms admitted_receipt_stamp
#print axioms existing_row_stamp
#print axioms admit_row_fixed_fields
#print axioms admit_rows_core
#print axioms admit_rows_clock
#print axioms carried_row_prefix
#print axioms coherent_admit_row
#print axioms coherent_admit_rows
#print axioms coherent_admit_carried
#print axioms coherent_on_block
#print axioms process_block_clock
#print axioms on_block_clock
end DecoupledConsensusModel.Proofs.NamedAdmission

end
