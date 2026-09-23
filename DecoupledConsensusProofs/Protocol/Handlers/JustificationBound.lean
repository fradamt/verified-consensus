module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge
public import DecoupledConsensusProofs.Protocol.Handlers.StoreFinality
public import DecoupledConsensusProofs.Protocol.Handlers.HMaxMonotone
public import DecoupledConsensusProofs.Protocol.ChainState.CheckpointHeights
public import DecoupledConsensusProofs.Protocol.ChainState.JustificationCertificates

@[expose] public section



namespace DecoupledConsensusModel.Proofs.NamedJustificationBound
open Execution Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## 1. The named transition keeps the chain-state invariant -/

/-- The named twin of `chainFinality_state_transition`. The hypothesis is the
same inductive one: the state being extended is the parent's, whose latest
block precedes the block's own erasure. -/
theorem chainFinality_named_transition (E : Env V) (cfg : HeightConfig)
    (st : ChainState V) (B : NamedBlock V) (h : ChainFinality st)
    (hL : Block.preceq st.L B.erase = true) :
    ChainFinality (named_transition E cfg st B) := by
  unfold Protocol.named_transition Protocol.transition_rows
    Protocol.fold_rows
  refine chainFinality_process_height_events E cfg _ ?_
  obtain ⟨_, f2, f3, f4, f5, f6, f7⟩ :=
    NamedDerivationGeometry.fold_context_fields (TimeoutBinding.targeted V)
      B.attestations ({ st with s := B.erase.slot } : ChainState V)
  exact
    { target_preceq_latest := by
        rw [f3]; exact Block.preceq_trans h.target_preceq_latest hL
      justified_preceq_target := by
        rw [f3, f4]; exact h.justified_preceq_target
      finalized_preceq_justified := by
        rw [f4, f6]; exact h.finalized_preceq_justified
      heights_ordered := by
        rw [f5, f7]; exact h.heights_ordered
      justified_below_height := by
        rw [f2, f5]; exact h.justified_below_height }

/-! ## 2. The pair carried by the named induction -/

/-- The state map is a valid chain-state map and the store's justification is
strictly below its running maximum. The first conjunct is
`Invariants2.StoreChainStates`; the second is `Internal.JustificationBelowMax`. -/
private def CoreJust (st : Protocol.Store V) : Prop :=
  ChainStatesOk st.σ ∧ st.h_j < st.h_max

omit [Fintype V] in
private theorem coreJust_of_eq {st st' : Protocol.Store V} (hs : st'.σ = st.σ)
    (hj : st'.h_j = st.h_j) (hm : st'.h_max = st.h_max) (h : CoreJust st) :
    CoreJust st' := by
  refine ⟨?_, ?_⟩
  · rw [ChainStatesOk, hs]; exact h.1
  · rw [hj, hm]; exact h.2

omit [Fintype V] in
/-- The write at one key preserves the map invariant when the written entry is
keyed at its own latest block and satisfies the §4 invariant. This is
`chainStatesOk_write` with the builder abstracted. -/
private theorem chainStatesOk_write_target {m : Block V → ChainState V} (B : Block V)
    (target : ChainState V) (hL : target.L = B) (hfin : ChainFinality target)
    (h : ChainStatesOk m) :
    ChainStatesOk (fun C => if C = B then target else m C) := by
  intro C
  by_cases hC : C = B
  · refine ⟨?_, ?_⟩ <;> simp only [if_pos hC]
    · rw [hC, hL]; exact Block.preceq_self _
    · exact hfin
  · refine ⟨?_, ?_⟩ <;> simp only [if_neg hC]
    · exact (h C).1
    · exact (h C).2

omit [Fintype V] in
/-- `update_finality` keeps the map untouched and raises the maximum, so the
pair survives whenever the offered chain state is itself below its height. -/
private theorem coreJust_update_finality (st : Protocol.Store V) (sigma : ChainState V)
    (hsig : sigma.h_j < sigma.h) (h : CoreJust st) :
    CoreJust (Protocol.update_finality st sigma) := by
  refine ⟨?_, ?_⟩
  · rw [ChainStatesOk, update_finality_σ]; exact h.1
  · exact StoreFinality.justificationBelowMax_update_finality st sigma h.2 hsig

private theorem gf_just (E : Env V) (st : Protocol.Store V) (u : GoldfishVote V)
    (h : CoreJust st) : CoreJust (Protocol.on_goldfish_vote_checked E st u) :=
  coreJust_of_eq (coreEq_on_goldfish_vote_checked E st u).σ_eq
    (coreEq_on_goldfish_vote_checked E st u).h_j_eq
    (on_goldfish_vote_checked_h_max E st u) h

/-- The shared block body over an arbitrary builder. The builder must key its
result at the block and keep the §4 invariant; the named builder does both. -/
private theorem raw_block_just (E : Env V) (st : Protocol.Store V) (B : Block V)
    (build : ChainState V → ChainState V) (hL : (build (st.σ B.parent)).L = B)
    (hfin : ChainFinality (st.σ B.parent) → ChainFinality (build (st.σ B.parent)))
    (h : CoreJust st) : CoreJust (Protocol.on_block_using E st B build) := by
  by_cases hs : st.s < B.slot ∨ B ∈ st.T ∨ B.parent ∉ st.T
  · rw [show Protocol.on_block_using E st B build = st by
      simp only [Protocol.on_block_using, if_pos hs]]
    exact h
  by_cases hadm : (!Block.preceq st.F B) = true
  · rw [show Protocol.on_block_using E st B build = st by
      simp only [Protocol.on_block_using, if_neg hs, if_pos hadm]]
    exact h
  by_cases hprop : B.proposer? ≠ some (E.proposer B.slot)
  · rw [show Protocol.on_block_using E st B build = st by
      simp only [Protocol.on_block_using, if_neg hs, if_neg hadm, if_pos hprop]]
    exact h
  by_cases hslot : ¬ (B.parent.slot < B.slot)
  · rw [show Protocol.on_block_using E st B build = st by
      simp only [Protocol.on_block_using, if_neg hs, if_neg hadm, if_neg hprop,
        if_pos hslot]]
    exact h
  set stored : Protocol.Store V :=
      { st with
        σ := fun C => if C = B then build (st.σ B.parent) else st.σ C
        T := insert B st.T
        timestamp_block := fun C =>
          if C = B then some (st.t : Stamp) else st.timestamp_block C }
      with hstoredDef
  set unpacked : Protocol.Store V :=
    B.gf_votes.foldl (Protocol.on_goldfish_vote_checked E) stored with hunpackedDef
  have hres : Protocol.on_block_using E st B build =
      Protocol.update_finality unpacked (unpacked.σ B) := by
    unfold Protocol.on_block_using
    rw [if_neg hs, if_neg hadm, if_neg hprop, if_neg hslot]
  have hmap : ChainStatesOk stored.σ := by
    rw [hstoredDef]
    exact chainStatesOk_write_target B _ hL
      (hfin (h.1 B.parent).2) h.1
  have hσu : unpacked.σ = stored.σ :=
    (coreEq_foldl_on_goldfish_vote_checked E B.gf_votes stored).σ_eq
  have hju : unpacked.h_j = stored.h_j :=
    (coreEq_foldl_on_goldfish_vote_checked E B.gf_votes stored).h_j_eq
  have hmaxu : unpacked.h_max = stored.h_max :=
    foldl_on_goldfish_vote_checked_h_max E B.gf_votes stored
  have hu : CoreJust unpacked := by
    refine ⟨?_, ?_⟩
    · rw [ChainStatesOk, hσu]; exact hmap
    · rw [hju, hmaxu, hstoredDef]; exact h.2
  have hsig : (unpacked.σ B).h_j < (unpacked.σ B).h := by
    have hchain : ChainFinality (unpacked.σ B) := by
      rw [hσu]
      exact (hmap B).2
    exact hchain.justified_below_height
  rw [hres]
  exact coreJust_update_finality unpacked (unpacked.σ B) hsig hu

/-! ## 3. The named handlers -/

private theorem named_core_just (S : Setup V) (st : Protocol.NamedStore V)
    (B : NamedBlock V) (h : CoreJust st.core) :
    CoreJust (Protocol.NamedStore.process_block_core S.E S.hc S.cfg st B).core := by
  dsimp only [Protocol.NamedStore.process_block_core]
  split_ifs <;> first
    | exact h
    | (rw [NamedStore.commit_core]
       dsimp only [Protocol.on_block_checked_using]
       split_ifs
       · refine raw_block_just S.E st.core B.erase _
           (NamedDerivationGeometry.named_transition_latest S.E S.cfg _ B) ?_ h
         intro hpar
         exact chainFinality_named_transition S.E S.cfg _ B hpar
           (Block.preceq_trans (h.1 B.erase.parent).1 (preceq_parent B.erase))
       · exact h)

omit [Fintype V] in
private theorem row_just (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (a : NamedAttestation V) (h : CoreJust st.core) :
    CoreJust (Protocol.NamedAdmission.admit_row hc st a).core := by
  rw [NamedAdmission.admit_row_core]
  exact coreJust_of_eq (coreEq_on_sg_vote hc st.core a.erase).σ_eq
    (coreEq_on_sg_vote hc st.core a.erase).h_j_eq
    (on_sg_vote_h_max hc st.core a.erase) h

omit [Fintype V] in
private theorem rows_just (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (rows : List (NamedAttestation V)) (h : CoreJust st.core) :
    CoreJust (Protocol.NamedAdmission.admit_rows hc st rows).core := by
  induction rows generalizing st with
  | nil => exact h
  | cons a rows ih => exact ih _ (row_just hc st a h)

private theorem block_just (S : Setup V) (st : Protocol.NamedStore V) (B : NamedBlock V)
    (h : CoreJust st.core) :
    CoreJust
      (Protocol.NamedAdmission.on_block_with .alsoCarried S.E S.hc S.cfg st B).core := by
  have hcore := named_core_just S st B h
  dsimp only [Protocol.NamedAdmission.on_block_with, Protocol.NamedAdmission.admit_carried]
  split_ifs
  · exact rows_just S.hc _ B.attestations hcore
  · exact hcore

private theorem clock_just (E : Env V) (st : Protocol.NamedStore V) (t : Time)
    (h : CoreJust st.core) : CoreJust (Protocol.NamedStore.setClock E st t).core := h

private theorem confirmation_just (gc : Protocol.GradeContract V) (S : Setup V)
    (st : Protocol.NamedStore V) (s : Slot) (h : CoreJust st.core) :
    CoreJust (Protocol.NamedDuties.update_confirmation_with gc S.E S.hc st s).core := h

private theorem propose_just (gc : Protocol.GradeContract V) (S : Setup V)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V) (h : CoreJust st.core) :
    CoreJust (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg nd st).1.core := by
  unfold Protocol.NamedDuties.propose_block_with
  split
  · exact h
  · exact block_just S st _ h

private theorem vote_just (gc : Protocol.GradeContract V) (S : Setup V)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V) (h : CoreJust st.core) :
    CoreJust (Protocol.NamedDuties.goldfish_vote_with gc S.E S.hc nd st).1.core := by
  dsimp only [Protocol.NamedDuties.goldfish_vote_with, Protocol.goldfish_vote_with]
  split_ifs
  · exact gf_just S.E st.core _ h
  · exact h

private theorem attest_just (gc : Protocol.GradeContract V) (S : Setup V)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (record : Protocol.NamedRecord) (h : CoreJust st.core) :
    CoreJust (Protocol.NamedDuties.attest_with gc S.E S.hc nd st record).1.core :=
  row_just S.hc st _ h

private theorem tick_just (gc : Protocol.GradeContract V) (S : Setup V)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (record : Protocol.NamedRecord) (t : Time) (h : CoreJust st.core) :
    CoreJust (Protocol.NamedTick.tick gc S.E S.hc S.cfg nd st record t).1.core := by
  let s := S.E.slotOf t
  let st0 := Protocol.NamedStore.setClock S.E st t
  let st1 := if 0 < s ∧ t = Protocol.proposal_time S.E s ∧ S.E.proposer s = nd.val_index then
    (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg nd st0).1 else st0
  let st2 := if 0 < s ∧ t = Protocol.vote_time S.E s then
    (Protocol.NamedDuties.goldfish_vote_with gc S.E S.hc nd st1).1 else st1
  let st3 := if 0 < s ∧ t = Protocol.support_cutoff S.E s then
    Protocol.NamedDuties.update_confirmation_with gc S.E S.hc st2 (s - 1) else st2
  have h0 := clock_just S.E st t h
  have h1 : CoreJust st1.core := by
    dsimp only [st1]
    split_ifs
    · exact propose_just gc S nd st0 h0
    · exact h0
  have h2 : CoreJust st2.core := by
    dsimp only [st2]
    split_ifs
    · exact vote_just gc S nd st1 h1
    · exact h1
  have h3 : CoreJust st3.core := by
    dsimp only [st3]
    split_ifs
    · exact confirmation_just gc S st2 (s - 1) h2
    · exact h2
  have hstore : (Protocol.NamedTick.tick gc S.E S.hc S.cfg nd st record t).1 =
      (if t = S.hc.a S.E.Δ (S.hc.round_of st3.core.s) ∧
          nd.awake (S.hc.round_of st3.core.s) = true then
        (Protocol.NamedDuties.attest_with gc S.E S.hc nd st3 record).1 else st3) := by
    rw [NamedTick.tick_computed_duties]
    dsimp only [st3, st2, st1, st0, s]
    split_ifs <;> rfl
  rw [hstore]
  split_ifs
  · exact attest_just gc S nd st3 record h3
  · exact h3

private theorem node_tick_just (S : Setup V) (v : V) (n : NamedNodeState V) (t : Time)
    (h : CoreJust n.st.core) :
    CoreJust (Execution.NamedNode.tick S v n t).1.st.core :=
  tick_just (NamedProfile.gradeContract
    (DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache)) S (S.node v)
    n.st n.record t h

private theorem node_process_just (S : Setup V) (n : NamedNodeState V) (o : NamedObject V)
    (h : CoreJust n.st.core) :
    CoreJust (Execution.NamedNode.process S n o).st.core := by
  cases o with
  | block B => exact block_just S n.st B h
  | gfVote u => exact gf_just S.E n.st.core u h
  | attest a => exact row_just S.hc n.st a h

private theorem world_just (S : Setup V) (w : NamedWorld V) (e : NamedEvent V)
    (h : ∀ v, CoreJust (w v).st.core) :
    ∀ v, CoreJust (NamedWorld.step S w e v).st.core := by
  intro v
  cases e with
  | tick u t =>
    by_cases hv : v = u
    · subst u
      simpa only [NamedWorld.step, Function.update_self] using node_tick_just S v (w v) t (h v)
    · simpa only [NamedWorld.step, Function.update_of_ne hv] using h v
  | deliver u o t =>
    by_cases hv : v = u
    · subst u
      simpa only [NamedWorld.step, Function.update_self] using node_process_just S (w v) o (h v)
    · simpa only [NamedWorld.step, Function.update_of_ne hv] using h v

omit [Fintype V] in
private theorem initial_just (v : V) :
    CoreJust (NamedWorld.init v : NamedNodeState V).st.core :=
  ⟨chainStatesOk_const_initial, Nat.zero_lt_one⟩

private theorem fold_just (S : Setup V) (events : List (NamedEvent V)) (w : NamedWorld V)
    (h : ∀ v, CoreJust (w v).st.core) :
    ∀ v, CoreJust (events.foldl (NamedWorld.step S) w v).st.core := by
  induction events generalizing w with
  | nil => exact h
  | cons e events ih => exact ih _ (world_just S w e h)

/-! ## 3b. B13, the named no-high-justifications fold

`Internal.NamedNoHighJustifications` is the named twin of B13: every held body's
own named justification height is at or below the store's. earlier proves it over
the retired `DepSteps`, carrying agreement, provenance and store finality
alongside (`noHighJustifications_depSteps`). The named fold carries a smaller
bundle, because the named derivation supplies for free what the erased proof
had to reconstruct from the store: `chainOrder_derive_named` gives
`h_j < h` at every body, and `NamedCheckpointHeights` gives the justified block
as a full named ancestor at its own height. What is left to carry is the pair
`F ⪯ J` and "the justification is a held body at height `h_j`", plus the
coherence the caller already has.

The hard case is earlier's: an accepted block whose offered justification fails
the store's ancestry filter. There the offered justification is below the
store's finalized block, and the finalized block is below the justification
height, so the offered height cannot exceed the store's. Every height
comparison is store-local: an erased ancestor of a held body is the erasure of
a held body (parent closure), and erasure is injective on held bodies
(`ErasureUnique`), so `derive_height_mono` transfers. -/

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

/-- Named heights are monotone along erased ancestry between held bodies. -/
private theorem body_height_mono (S : Setup V) {st : Protocol.NamedStore V}
    (hco : Proofs.NamedStore.Coherent S.E S.cfg st) {A B : NamedBlock V}
    (hA : A ∈ st.bodies) (hB : B ∈ st.bodies) (hAB : Block.Preceq A.erase B.erase) :
    (derive_named S.E S.cfg A).h ≤ (derive_named S.E S.cfg B).h := by
  obtain ⟨A', hA'B, hA'e⟩ := Proofs.NamedAncestry.erased_ancestor_lift B hAB
  have hA'mem : A' ∈ st.bodies := ancestor_body_mem hco.2.2.1 hB hA'B
  have hEq : A' = A := hco.2.1 A' hA'mem A hA hA'e
  rw [← hEq]
  exact Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hA'B

/-- The bundle the B13 fold carries beside the node invariant. -/
private def Bundle (S : Setup V) (st : Protocol.NamedStore V) : Prop :=
  Block.preceq st.core.F st.core.J = true ∧
    (st.core.J = Block.genesis ∨
      ∃ Jb ∈ st.bodies, Jb.erase = st.core.J ∧
        (derive_named S.E S.cfg Jb).h = st.core.h_j) ∧
    Internal.NamedNoHighJustifications S.E S.cfg st

private theorem bundle_of_eq (S : Setup V) {st st' : Protocol.NamedStore V}
    (h : Bundle S st) (hb : st'.bodies = st.bodies) (hF : st'.core.F = st.core.F)
    (hJ : st'.core.J = st.core.J) (hhj : st'.core.h_j = st.core.h_j) : Bundle S st' := by
  obtain ⟨horder, hjust, hnh⟩ := h
  refine ⟨by rw [hF, hJ]; exact horder, ?_, ?_⟩
  · rw [hJ]
    rcases hjust with hz | ⟨Jb, hJb, hJbe, hJbh⟩
    · exact Or.inl hz
    · exact Or.inr ⟨Jb, by rw [hb]; exact hJb, hJbe, by rw [hhj]; exact hJbh⟩
  · intro C hC
    rw [hb] at hC
    rw [hhj]
    exact hnh C hC

/-- The store's finalized block sits at or below the justification height.
earlier's `finalized_height_le_justification`, named and store-local. -/
private theorem finalized_height_le_hj (S : Setup V) {st : Protocol.NamedStore V}
    (hco : Proofs.NamedStore.Coherent S.E S.cfg st) (h : Bundle S st)
    {Fb : NamedBlock V} (hFb : Fb ∈ st.bodies) (hFbe : Fb.erase = st.core.F) :
    st.core.F = Block.genesis ∨ (derive_named S.E S.cfg Fb).h ≤ st.core.h_j := by
  rcases h.2.1 with hz | ⟨Jb, hJb, hJbe, hJbh⟩
  · left
    refine Block.preceq_antisymm ?_ (Protocol.preceq_genesis st.core.F)
    have := h.1
    rwa [hz] at this
  · right
    have hmono : (derive_named S.E S.cfg Fb).h ≤ (derive_named S.E S.cfg Jb).h :=
      body_height_mono S hco hFb hJb (by rw [hFbe, hJbe]; exact h.1)
    rw [hJbh] at hmono
    exact hmono

private theorem just_witness_ne (S : Setup V) {B Jn : NamedBlock V}
    (hJnh : (derive_named S.E S.cfg Jn).h = (derive_named S.E S.cfg B).h_j) : Jn ≠ B := by
  intro hEq
  have hlt : (derive_named S.E S.cfg B).h_j < (derive_named S.E S.cfg B).h :=
    (NamedDerivationGeometry.chainOrder_derive_named S.E S.cfg B).justified_below_height
  rw [hEq] at hJnh
  exact absurd hJnh (Nat.ne_of_gt hlt)

/-- The justification witness of an incoming block whose parent the store holds
is itself held: it is a proper named ancestor, so parent closure reaches it. -/
private theorem just_witness_body (S : Setup V) {st : Protocol.NamedStore V}
    (hco : Proofs.NamedStore.Coherent S.E S.cfg st) {B Jn : NamedBlock V}
    (hpar : B.parent ∈ st.bodies) (hJnB : NamedBlock.Preceq Jn B)
    (hne : Jn ≠ B) : Jn ∈ st.bodies := by
  cases B with
  | genesis =>
    simp only [NamedBlock.Preceq, NamedBlock.preceq, decide_eq_true_eq] at hJnB
    exact absurd hJnB hne
  | node parent s root votes support rows proposer =>
    simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
      decide_eq_true_eq] at hJnB
    rcases hJnB with hEq | hp
    · exact absurd hEq hne
    · exact ancestor_body_mem hco.2.2.1 hpar hp

/-- The offered justification of an accepted block is not above the store the
finality update produces. earlier's `offered_justification_le_update_finality`,
named: the height comparisons run on `derive_named` at held bodies. -/
private theorem offered_le_update (S : Setup V) {st : Protocol.NamedStore V}
    (hco : Proofs.NamedStore.Coherent S.E S.cfg st) (hFT : st.core.F ∈ st.core.T)
    (h : Bundle S st) {B : NamedBlock V} (hpar : B.parent ∈ st.bodies)
    (hFB : Block.preceq st.core.F B.erase = true) :
    (derive_named S.E S.cfg B).h_j ≤
      (Protocol.update_finality st.core (derive_named S.E S.cfg B)).h_j := by
  by_cases hFJ : Block.preceq st.core.F (derive_named S.E S.cfg B).J = true
  · by_cases hlex : Protocol.HeightId.mk st.core.h_j st.core.J.root <
        Protocol.HeightId.mk (derive_named S.E S.cfg B).h_j
          (derive_named S.E S.cfg B).J.root
    · have hguard : (Block.preceq st.core.F (derive_named S.E S.cfg B).J &&
          decide (Protocol.HeightId.mk st.core.h_j st.core.J.root <
            Protocol.HeightId.mk (derive_named S.E S.cfg B).h_j
              (derive_named S.E S.cfg B).J.root)) = true := by
        rw [Bool.and_eq_true]
        exact ⟨hFJ, decide_eq_true hlex⟩
      have hwrite : (Protocol.update_finality st.core
          (derive_named S.E S.cfg B)).h_j = (derive_named S.E S.cfg B).h_j := by
        unfold Protocol.update_finality
        dsimp only
        rw [if_pos hguard]
        split_ifs <;> rfl
      rw [hwrite]
    · exact le_trans (heightId_height_le_of_le (not_lt.mp hlex))
        (heightId_height_le_of_le
          (update_finality_heightId st.core (derive_named S.E S.cfg B)))
  · refine le_trans ?_ (heightId_height_le_of_le
      (update_finality_heightId st.core (derive_named S.E S.cfg B)))
    rcases NamedCheckpointHeights.justified_ancestor_height S.E S.cfg B with hz | hwit
    · rw [hz]
      exact Nat.zero_le _
    obtain ⟨Jn, hJnB, hJnE, hJnh⟩ := hwit
    have hJB : Block.Preceq (derive_named S.E S.cfg B).J B.erase :=
      (Proofs.NamedStoreRoots.derive_named_anchors_preceq S.E S.cfg B).2
    have hJF : Block.Preceq (derive_named S.E S.cfg B).J st.core.F :=
      (Block.preceq_linear hJB hFB).resolve_right hFJ
    obtain ⟨Fb, hFb, hFbe⟩ : ∃ Fb ∈ st.bodies, Fb.erase = st.core.F := by
      have hmem : st.core.F ∈ st.bodies.image NamedBlock.erase := by
        rw [← hco.1]; exact hFT
      obtain ⟨Fb, hFb, hFbe⟩ := Finset.mem_image.mp hmem
      exact ⟨Fb, hFb, hFbe⟩
    have hJnbody : Jn ∈ st.bodies :=
      just_witness_body S hco hpar hJnB (just_witness_ne S hJnh)
    have hFbound : (derive_named S.E S.cfg Fb).h ≤ st.core.h_j := by
      rcases finalized_height_le_hj S hco h hFb hFbe with hFg | hb
      · exfalso
        apply hFJ
        have hgen : (derive_named S.E S.cfg B).J = Block.genesis :=
          Block.preceq_antisymm (by rwa [hFg] at hJF)
            (Protocol.preceq_genesis (derive_named S.E S.cfg B).J)
        rw [hFg, hgen]
        exact Block.preceq_self _
      · exact hb
    calc (derive_named S.E S.cfg B).h_j = (derive_named S.E S.cfg Jn).h := hJnh.symm
      _ ≤ (derive_named S.E S.cfg Fb).h :=
        body_height_mono S hco hJnbody hFb (by rw [hJnE, hFbe]; exact hJF)
      _ ≤ st.core.h_j := hFbound

/-- The block body is the identity, or it is one `update_finality` over a store
that differs from the incoming one only in the tree and the written entry. One
guard split, so no consumer below splits again. Public: the named
`FinalizedViable` producer runs the same split over the same builder. -/
theorem raw_eq_or_accepted (E : Env V) (st : Protocol.Store V) (B : Block V)
    (build : ChainState V → ChainState V) :
    Protocol.on_block_using E st B build = st ∨
      ∃ u : Protocol.Store V,
        u.T = insert B st.T ∧ u.F = st.F ∧ u.J = st.J ∧ u.h_j = st.h_j ∧
        u.h_max = st.h_max ∧
        u.σ = (fun C => if C = B then build (st.σ B.parent) else st.σ C) ∧
        B ∉ st.T ∧ Block.preceq st.F B = true ∧
        Protocol.on_block_using E st B build = Protocol.update_finality u (u.σ B) := by
  by_cases hs : st.s < B.slot ∨ B ∈ st.T ∨ B.parent ∉ st.T
  · left
    simp only [Protocol.on_block_using, if_pos hs]
  by_cases hadm : (!Block.preceq st.F B) = true
  · left
    simp only [Protocol.on_block_using, if_neg hs, if_pos hadm]
  by_cases hprop : B.proposer? ≠ some (E.proposer B.slot)
  · left
    simp only [Protocol.on_block_using, if_neg hs, if_neg hadm, if_pos hprop]
  by_cases hslot : ¬ (B.parent.slot < B.slot)
  · left
    simp only [Protocol.on_block_using, if_neg hs, if_neg hadm, if_neg hprop, if_pos hslot]
  right
  refine ⟨B.gf_votes.foldl (Protocol.on_goldfish_vote_checked E)
      { st with
        σ := fun C => if C = B then build (st.σ B.parent) else st.σ C
        T := insert B st.T
        timestamp_block := fun C =>
          if C = B then some (st.t : Stamp) else st.timestamp_block C },
    ?hT, ?hF, ?hJ, ?hhj, ?hmax, ?hsig,
    fun hm => hs (Or.inr (Or.inl hm)), by simpa using hadm, ?hres⟩
  case hmax => exact foldl_on_goldfish_vote_checked_h_max E _ _
  case hT => exact Proofs.foldl_on_goldfish_vote_checked_T E _ _
  case hF => exact (coreEq_foldl_on_goldfish_vote_checked E B.gf_votes _).F_eq
  case hJ => exact (coreEq_foldl_on_goldfish_vote_checked E B.gf_votes _).J_eq
  case hhj => exact (coreEq_foldl_on_goldfish_vote_checked E B.gf_votes _).h_j_eq
  case hsig => exact (coreEq_foldl_on_goldfish_vote_checked E B.gf_votes _).σ_eq
  case hres =>
    unfold Protocol.on_block_using
    rw [if_neg hs, if_neg hadm, if_neg hprop, if_neg hslot]

omit [Fintype V] in
/-- The justification height written by `update_finality` reads only the
store's own `F`, `J` and `h_j`. -/
private theorem update_finality_h_j_congr {a b : Protocol.Store V} (sigma : ChainState V)
    (hF : a.F = b.F) (hJ : a.J = b.J) (hhj : a.h_j = b.h_j) :
    (Protocol.update_finality a sigma).h_j = (Protocol.update_finality b sigma).h_j := by
  unfold Protocol.update_finality
  dsimp only
  rw [hF, hJ, hhj]
  split_ifs <;> rfl

omit [Fintype V] in
/-- `update_finality` either carries the justification pair or installs the
offered one. -/
private theorem update_finality_just_cases (st : Protocol.Store V) (sigma : ChainState V) :
    ((Protocol.update_finality st sigma).J = st.J ∧
        (Protocol.update_finality st sigma).h_j = st.h_j) ∨
      ((Protocol.update_finality st sigma).J = sigma.J ∧
        (Protocol.update_finality st sigma).h_j = sigma.h_j) := by
  unfold Protocol.update_finality
  dsimp only
  split_ifs <;> first
    | exact Or.inl ⟨rfl, rfl⟩
    | exact Or.inr ⟨rfl, rfl⟩

private theorem bundle_commit_same (S : Setup V) (st : Protocol.NamedStore V)
    (B : NamedBlock V) (h : Bundle S st) :
    Bundle S (Protocol.NamedStore.commitBlock st st.core B) := by
  dsimp only [Protocol.NamedStore.commitBlock]
  split_ifs with hg
  · exact absurd hg.2 hg.1
  · exact bundle_of_eq S h rfl rfl rfl rfl

/-- B13 across the named block core. -/
private theorem bundle_block_core (S : Setup V) (st : Protocol.NamedStore V)
    (B : NamedBlock V) (hco : Proofs.NamedStore.Coherent S.E S.cfg st)
    (hFT : st.core.F ∈ st.core.T) (h : Bundle S st) :
    Bundle S (Protocol.NamedStore.process_block_core S.E S.hc S.cfg st B) := by
  by_cases hpar : B.parent ∈ st.bodies
  · have hred : Protocol.NamedStore.process_block_core S.E S.hc S.cfg st B =
        Protocol.NamedStore.commitBlock st
          (Protocol.on_block_checked_using
            (fun current => Protocol.on_block_using S.E current B.erase
              (fun parentState => named_transition S.E S.cfg parentState B))
            S.hc st.core B.erase) B := by
      dsimp only [Protocol.NamedStore.process_block_core]
      rw [if_neg (not_not.mpr hpar)]
    rw [hred]
    by_cases hvalid : Protocol.carried_attestations_admissible S.hc B.erase = true
    · rw [show Protocol.on_block_checked_using
            (fun current => Protocol.on_block_using S.E current B.erase
              (fun parentState => named_transition S.E S.cfg parentState B))
            S.hc st.core B.erase =
          Protocol.on_block_using S.E st.core B.erase
            (fun parentState => named_transition S.E S.cfg parentState B) by
        simp only [Protocol.on_block_checked_using, if_pos hvalid]]
      rcases raw_eq_or_accepted S.E st.core B.erase
        (fun parentState => named_transition S.E S.cfg parentState B) with hid | hacc
      · rw [hid]
        exact bundle_commit_same S st B h
      obtain ⟨u, huT, huF, huJ, huhj, _humax, husigma, hfresh, hFB, hres⟩ := hacc
      have hgen : B ≠ NamedBlock.genesis := by
        intro hEq
        apply hfresh
        rw [hEq, hco.1]
        exact Finset.mem_image_of_mem _ hco.2.2.1.1
      have hsigmaB : u.σ B.erase = derive_named S.E S.cfg B := by
        simp only [husigma]
        rw [Proofs.NamedWire.erase_parent, hco.2.2.2.2 B.parent hpar]
        exact (BlockProcessingDefaults.derive_named_of_not_genesis S.E S.cfg B hgen).symm
      have hguard : B.erase ∉ st.core.T ∧ B.erase ∈
          (Protocol.on_block_using S.E st.core B.erase
            (fun parentState => named_transition S.E S.cfg parentState B)).T := by
        refine ⟨hfresh, ?_⟩
        rw [hres, Proofs.update_finality_T, huT]
        exact Finset.mem_insert_self _ _
      have hbodies : (Protocol.NamedStore.commitBlock st
          (Protocol.on_block_using S.E st.core B.erase
            (fun parentState => named_transition S.E S.cfg parentState B)) B).bodies =
          insert B st.bodies := by
        dsimp only [Protocol.NamedStore.commitBlock]
        rw [if_pos hguard]
      have hcore : (Protocol.NamedStore.commitBlock st
          (Protocol.on_block_using S.E st.core B.erase
            (fun parentState => named_transition S.E S.cfg parentState B)) B).core =
          Protocol.update_finality u (derive_named S.E S.cfg B) := by
        rw [NamedStore.commit_core, hres, hsigmaB]
      have hmono : st.core.h_j ≤ (Protocol.update_finality u
          (derive_named S.E S.cfg B)).h_j := by
        rw [← huhj]
        exact heightId_height_le_of_le (update_finality_heightId u _)
      refine ⟨?_, ?_, ?_⟩
      · rw [hcore]
        refine update_finality_preceq u _ ?_
        rw [huF, huJ]
        exact h.1
      · rw [hcore, hbodies]
        rcases update_finality_just_cases u (derive_named S.E S.cfg B) with
          ⟨hJ, hhj⟩ | ⟨hJ, hhj⟩
        · rw [hJ, hhj, huJ, huhj]
          rcases h.2.1 with hz | ⟨Jb, hJb, hJbe, hJbh⟩
          · exact Or.inl hz
          · exact Or.inr ⟨Jb, Finset.mem_insert_of_mem hJb, hJbe, hJbh⟩
        · rw [hJ, hhj]
          rcases NamedCheckpointHeights.justified_ancestor_height S.E S.cfg B with hz | hwit
          · exact Or.inl (NamedJustificationCertificates.justified_zero_is_genesis
              S.E S.cfg B hz)
          · obtain ⟨Jn, hJnB, hJnE, hJnh⟩ := hwit
            exact Or.inr ⟨Jn, Finset.mem_insert_of_mem
              (just_witness_body S hco hpar hJnB (just_witness_ne S hJnh)), hJnE, hJnh⟩
      · intro C hC
        rw [hbodies] at hC
        rw [hcore]
        rcases Finset.mem_insert.mp hC with hCB | hCold
        · subst C
          rw [update_finality_h_j_congr (derive_named S.E S.cfg B) huF huJ huhj]
          exact offered_le_update S hco hFT h hpar hFB
        · exact le_trans (h.2.2 C hCold) hmono
    · rw [show Protocol.on_block_checked_using
            (fun current => Protocol.on_block_using S.E current B.erase
              (fun parentState => named_transition S.E S.cfg parentState B))
            S.hc st.core B.erase = st.core by
        simp only [Protocol.on_block_checked_using, if_neg hvalid]]
      exact bundle_commit_same S st B h
  · have hred : Protocol.NamedStore.process_block_core S.E S.hc S.cfg st B = st := by
      dsimp only [Protocol.NamedStore.process_block_core]
      rw [if_pos hpar]
    rw [hred]
    exact h

private theorem bundle_row (S : Setup V) (st : Protocol.NamedStore V)
    (a : NamedAttestation V) (h : Bundle S st) :
    Bundle S (Protocol.NamedAdmission.admit_row S.hc st a) := by
  refine bundle_of_eq S h ?_ ?_ ?_ ?_
  · dsimp only [Protocol.NamedAdmission.admit_row]
    split_ifs <;> rfl
  · rw [NamedAdmission.admit_row_core]
    exact (coreEq_on_sg_vote S.hc st.core a.erase).F_eq
  · rw [NamedAdmission.admit_row_core]
    exact (coreEq_on_sg_vote S.hc st.core a.erase).J_eq
  · rw [NamedAdmission.admit_row_core]
    exact (coreEq_on_sg_vote S.hc st.core a.erase).h_j_eq

private theorem bundle_rows (S : Setup V) (st : Protocol.NamedStore V)
    (rows : List (NamedAttestation V)) (h : Bundle S st) :
    Bundle S (Protocol.NamedAdmission.admit_rows S.hc st rows) := by
  induction rows generalizing st with
  | nil => exact h
  | cons a rows ih => exact ih _ (bundle_row S st a h)

private theorem bundle_block_with (S : Setup V) (st : Protocol.NamedStore V)
    (B : NamedBlock V) (hco : Proofs.NamedStore.Coherent S.E S.cfg st)
    (hFT : st.core.F ∈ st.core.T) (h : Bundle S st) :
    Bundle S (Protocol.NamedAdmission.on_block_with .alsoCarried S.E S.hc S.cfg st B) := by
  have hcore := bundle_block_core S st B hco hFT h
  dsimp only [Protocol.NamedAdmission.on_block_with, Protocol.NamedAdmission.admit_carried]
  split_ifs
  · exact bundle_rows S _ B.attestations hcore
  · exact hcore

private theorem bundle_clock (S : Setup V) (st : Protocol.NamedStore V) (t : Time)
    (h : Bundle S st) : Bundle S (Protocol.NamedStore.setClock S.E st t) := h

private theorem bundle_confirmation (gc : Protocol.GradeContract V) (S : Setup V)
    (st : Protocol.NamedStore V) (s : Slot) (h : Bundle S st) :
    Bundle S (Protocol.NamedDuties.update_confirmation_with gc S.E S.hc st s) := h

private theorem bundle_vote (gc : Protocol.GradeContract V) (S : Setup V)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V) (h : Bundle S st) :
    Bundle S (Protocol.NamedDuties.goldfish_vote_with gc S.E S.hc nd st).1 := by
  dsimp only [Protocol.NamedDuties.goldfish_vote_with, Protocol.goldfish_vote_with]
  split_ifs
  · refine bundle_of_eq S h rfl ?_ ?_ ?_
    · exact (coreEq_on_goldfish_vote_checked S.E st.core _).F_eq
    · exact (coreEq_on_goldfish_vote_checked S.E st.core _).J_eq
    · exact (coreEq_on_goldfish_vote_checked S.E st.core _).h_j_eq
  · exact h

private theorem bundle_propose (gc : Protocol.GradeContract V) (S : Setup V)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (hco : Proofs.NamedStore.Coherent S.E S.cfg st) (hFT : st.core.F ∈ st.core.T)
    (h : Bundle S st) :
    Bundle S (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg nd st).1 := by
  unfold Protocol.NamedDuties.propose_block_with
  split
  · exact h
  · exact bundle_block_with S st _ hco hFT h

private theorem bundle_attest (gc : Protocol.GradeContract V) (S : Setup V)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (record : Protocol.NamedRecord) (h : Bundle S st) :
    Bundle S (Protocol.NamedDuties.attest_with gc S.E S.hc nd st record).1 :=
  bundle_row S st _ h

private theorem bundle_tick (gc : Protocol.GradeContract V) (S : Setup V)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (record : Protocol.NamedRecord) (t : Time)
    (hco : Proofs.NamedStore.Coherent S.E S.cfg st) (hFT : st.core.F ∈ st.core.T)
    (h : Bundle S st) :
    Bundle S (Protocol.NamedTick.tick gc S.E S.hc S.cfg nd st record t).1 := by
  let s := S.E.slotOf t
  let st0 := Protocol.NamedStore.setClock S.E st t
  let st1 := if 0 < s ∧ t = Protocol.proposal_time S.E s ∧ S.E.proposer s = nd.val_index then
    (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg nd st0).1 else st0
  let st2 := if 0 < s ∧ t = Protocol.vote_time S.E s then
    (Protocol.NamedDuties.goldfish_vote_with gc S.E S.hc nd st1).1 else st1
  let st3 := if 0 < s ∧ t = Protocol.support_cutoff S.E s then
    Protocol.NamedDuties.update_confirmation_with gc S.E S.hc st2 (s - 1) else st2
  have h0 : Bundle S st0 := bundle_clock S st t h
  have hco0 : Proofs.NamedStore.Coherent S.E S.cfg st0 := NamedStore.coherent_clock S.E S.cfg st t hco
  have hFT0 : st0.core.F ∈ st0.core.T := hFT
  have h1 : Bundle S st1 := by
    dsimp only [st1]
    split_ifs
    · exact bundle_propose gc S nd st0 hco0 hFT0 h0
    · exact h0
  have h2 : Bundle S st2 := by
    dsimp only [st2]
    split_ifs
    · exact bundle_vote gc S nd st1 h1
    · exact h1
  have h3 : Bundle S st3 := by
    dsimp only [st3]
    split_ifs
    · exact bundle_confirmation gc S st2 (s - 1) h2
    · exact h2
  have hstore : (Protocol.NamedTick.tick gc S.E S.hc S.cfg nd st record t).1 =
      (if t = S.hc.a S.E.Δ (S.hc.round_of st3.core.s) ∧
          nd.awake (S.hc.round_of st3.core.s) = true then
        (Protocol.NamedDuties.attest_with gc S.E S.hc nd st3 record).1 else st3) := by
    rw [NamedTick.tick_computed_duties]
    dsimp only [st3, st2, st1, st0, s]
    split_ifs <;> rfl
  rw [hstore]
  split_ifs
  · exact bundle_attest gc S nd st3 record h3
  · exact h3

private theorem node_tick_bundle (S : Setup V) (v : V) (n : NamedNodeState V) (t : Time)
    (hco : Proofs.NamedStore.Coherent S.E S.cfg n.st) (hFT : n.st.core.F ∈ n.st.core.T)
    (h : Bundle S n.st) :
    Bundle S (Execution.NamedNode.tick S v n t).1.st :=
  bundle_tick (NamedProfile.gradeContract
    (DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache)) S (S.node v)
    n.st n.record t hco hFT h

private theorem node_process_bundle (S : Setup V) (n : NamedNodeState V) (o : NamedObject V)
    (hco : Proofs.NamedStore.Coherent S.E S.cfg n.st) (hFT : n.st.core.F ∈ n.st.core.T)
    (h : Bundle S n.st) :
    Bundle S (Execution.NamedNode.process S n o).st := by
  cases o with
  | block B => exact bundle_block_with S n.st B hco hFT h
  | gfVote u =>
    refine bundle_of_eq S h rfl ?_ ?_ ?_
    · exact (coreEq_on_goldfish_vote_checked S.E n.st.core u).F_eq
    · exact (coreEq_on_goldfish_vote_checked S.E n.st.core u).J_eq
    · exact (coreEq_on_goldfish_vote_checked S.E n.st.core u).h_j_eq
  | attest a => exact bundle_row S n.st a h

private theorem initial_bundle (S : Setup V) (v : V) :
    Bundle S (NamedWorld.init v : NamedNodeState V).st := by
  refine ⟨Block.preceq_self _, Or.inl rfl, ?_⟩
  intro C hC
  have hCg : C = NamedBlock.genesis := Finset.mem_singleton.mp hC
  rw [hCg]
  exact Nat.le_refl _

private theorem fold_bundle (S : Setup V) (events : List (NamedEvent V)) (w : NamedWorld V)
    (hinv : ∀ v, Proofs.NamedConfirmationMembership.Invariant S.E S.cfg (w v).st ∧
      NamedTickRecord.Invariant (w v).record)
    (h : ∀ v, Bundle S (w v).st) :
    ∀ v, Bundle S (events.foldl (NamedWorld.step S) w v).st := by
  induction events generalizing w with
  | nil => exact h
  | cons e events ih =>
    apply ih
    · intro v
      cases e with
      | tick u t =>
        by_cases hv : v = u
        · subst u
          exact ⟨by simpa [NamedWorld.step] using
              NamedNode.confirmation_invariant_tick S v (w v) t (hinv v).1,
            by simpa [NamedWorld.step] using
              NamedNode.record_invariant_tick S v (w v) t (hinv v).2⟩
        · simpa [NamedWorld.step, Function.update_of_ne hv] using hinv v
      | deliver u o t =>
        by_cases hv : v = u
        · subst u
          simpa [NamedWorld.step] using
            NamedNode.invariants_process S (w v) o (hinv v).1 (hinv v).2
        · simpa [NamedWorld.step, Function.update_of_ne hv] using hinv v
    · intro v
      cases e with
      | tick u t =>
        by_cases hv : v = u
        · subst u
          simpa [NamedWorld.step] using
            node_tick_bundle S v (w v) t (hinv v).1.1.1 (hinv v).1.1.2.1 (h v)
        · simpa [NamedWorld.step, Function.update_of_ne hv] using h v
      | deliver u o t =>
        by_cases hv : v = u
        · subst u
          simpa [NamedWorld.step] using
            node_process_bundle S (w v) o (hinv v).1.1.1 (hinv v).1.1.2.1 (h v)
        · simpa [NamedWorld.step, Function.update_of_ne hv] using h v

/-! ## 4. The exports
Both halves at every named read, with no premise. `justificationBelowMax_*` is
the replacement for the retired `justificationBelowMax_depReachable`;
`storeChainStates_*` and `storeFinality_*` are the named producers of the
bundle that `Invariants2.storeFinality_reachable` delivers from
`ReachableStore`. -/


theorem storeChainStates_stateBeforeTime (S : Setup V) (rho : Run V) (t : Time) (v : V) :
    StoreChainStates (rho.stateBeforeTime S t v).st.core :=
  (fold_just S _ NamedWorld.init initial_just v).1




theorem justificationBelowMax_stateBefore (S : Setup V) (rho : Run V) (i : Nat) (v : V) :
    Internal.JustificationBelowMax (rho.stateBefore S i v).st.core :=
  (fold_just S (rho.events.take i) NamedWorld.init initial_just v).2

theorem justificationBelowMax_stateBeforeTime (S : Setup V) (rho : Run V) (t : Time)
    (v : V) : Internal.JustificationBelowMax (rho.stateBeforeTime S t v).st.core :=
  (fold_just S _ NamedWorld.init initial_just v).2

theorem justificationBelowMax_readAt (S : Setup V) (rho : Run V) (t : Time) (v : V) :
    Internal.JustificationBelowMax (Run.readAt S rho t v).st.core :=
  (fold_just S _ NamedWorld.init initial_just v).2

theorem justificationBelowMax_stateAt (S : Setup V) (rho : Run V) (t : Time) (v : V) :
    Internal.JustificationBelowMax (Run.stateAt S rho t v).st.core :=
  justificationBelowMax_readAt S rho t v




theorem noHighJustifications_stateBefore (S : Setup V) (rho : Run V) (i : Nat) (v : V) :
    Internal.NamedNoHighJustifications S.E S.cfg (rho.stateBefore S i v).st :=
  (fold_bundle S (rho.events.take i) NamedWorld.init
    (fun _ => NamedNode.initial_invariants S) (initial_bundle S) v).2.2

theorem noHighJustifications_stateBeforeTime (S : Setup V) (rho : Run V) (t : Time) (v : V) :
    Internal.NamedNoHighJustifications S.E S.cfg (rho.stateBeforeTime S t v).st :=
  (fold_bundle S _ NamedWorld.init
    (fun _ => NamedNode.initial_invariants S) (initial_bundle S) v).2.2

theorem noHighJustifications_readAt (S : Setup V) (rho : Run V) (t : Time) (v : V) :
    Internal.NamedNoHighJustifications S.E S.cfg (Run.readAt S rho t v).st :=
  (fold_bundle S _ NamedWorld.init
    (fun _ => NamedNode.initial_invariants S) (initial_bundle S) v).2.2

theorem noHighJustifications_stateAt (S : Setup V) (rho : Run V) (t : Time) (v : V) :
    Internal.NamedNoHighJustifications S.E S.cfg (Run.stateAt S rho t v).st :=
  noHighJustifications_readAt S rho t v





theorem storeFinality_stateBeforeTime (S : Setup V) (rho : Run V) (t : Time) (v : V) :
    StoreFinality (rho.stateBeforeTime S t v).st.core :=
  ⟨storeChainStates_stateBeforeTime S rho t v,
    Proofs.NamedStoreBridge.finalized_preceq_justified_stateBeforeTime S rho t v⟩




#print axioms chainFinality_named_transition
#print axioms justificationBelowMax_stateBeforeTime

end DecoupledConsensusModel.Proofs.NamedJustificationBound

end
