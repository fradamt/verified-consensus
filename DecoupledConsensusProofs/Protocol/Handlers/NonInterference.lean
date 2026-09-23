module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.BodyRetention
public import DecoupledConsensusProofs.Protocol.Handlers.FGProtection
public import DecoupledConsensusProofs.Execution.FinalityGuard
public import DecoupledConsensusProofs.Protocol.ChainState.JustificationCertificates
public import DecoupledConsensusProofs.Protocol.Handlers.MaximumCarrier
public import DecoupledConsensusProofs.Protocol.Handlers.JustificationCarrier
public import DecoupledConsensusProofs.Execution.ConflictingCarrierBand
public import DecoupledConsensusProofs.Protocol.Handlers.CheckpointRows
public import DecoupledConsensusProofs.Protocol.Duties.Inputs.IntrinsicEntry
public import DecoupledConsensusProofs.Execution.OutageInputs
public import DecoupledConsensusProofs.Protocol.Handlers.Invariants2
public import DecoupledConsensusInternal.Definitions.NamedJointOutage

@[expose] public section



namespace DecoupledConsensusModel.Proofs.NamedOutageClosure
open Execution Internal.NamedOutageEntry Internal.NamedStableChainOutage
open Internal.NamedJointOutage Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Copied private fold: `F` precedes `J` at every strict read. -/

private def CoreOrder (st : Protocol.Store V) : Prop :=
  Block.Preceq st.F st.J

omit [Fintype V] in
private theorem initial_core_order :
    CoreOrder (Protocol.NamedStore.initial : Protocol.NamedStore V).core := by
  exact Block.preceq_self _

private theorem gf_order (E : Env V) (st : Protocol.Store V) (u : GoldfishVote V)
    (h : CoreOrder st) : CoreOrder (Protocol.on_goldfish_vote_checked E st u) := by
  dsimp only [Protocol.on_goldfish_vote_checked, Protocol.on_goldfish_vote]
  split_ifs <;> exact h

private theorem gf_fold_order (E : Env V) (st : Protocol.Store V)
    (votes : List (GoldfishVote V)) (h : CoreOrder st) :
    CoreOrder (votes.foldl (Protocol.on_goldfish_vote_checked E) st) := by
  induction votes generalizing st with
  | nil => exact h
  | cons u votes ih => exact ih _ (gf_order E st u h)

private theorem raw_block_order (E : Env V) (st : Protocol.Store V) (B : Block V)
    (build : ChainState V → ChainState V)
    (h : CoreOrder st) : CoreOrder (Protocol.on_block_using E st B build) := by
  dsimp only [Protocol.on_block_using]
  split_ifs <;> first
    | exact h
    | (apply update_finality_preceq
       exact gf_fold_order E _ B.gf_votes h)

private theorem process_core_order (S : Setup V) (st : Protocol.NamedStore V)
    (B : NamedBlock V) (hco : Proofs.NamedStore.Coherent S.E S.cfg st)
    (h : CoreOrder st.core) :
    CoreOrder (Protocol.NamedStore.process_block_core S.E S.hc S.cfg st B).core := by
  cases B with
  | genesis =>
    have hmem : Block.genesis ∈ st.core.T := by
      rw [hco.1]
      exact Finset.mem_image_of_mem NamedBlock.erase hco.2.2.1.1
    have hpgen : NamedBlock.genesis.parent ∈ st.bodies := by
      change NamedBlock.genesis ∈ st.bodies
      exact hco.2.2.1.1
    rw [Protocol.NamedStore.process_block_core,
      if_neg (not_not.mpr hpgen), NamedStore.commit_core]
    dsimp only [Protocol.on_block_checked_using]
    split_ifs
    · change CoreOrder (Protocol.on_block_using S.E st.core Block.genesis _)
      simpa [Protocol.on_block_using, hmem] using h
    · exact h
  | node parent slot root votes support rows proposer =>
   let B : NamedBlock V := .node parent slot root votes support rows proposer
   change CoreOrder
     (Protocol.NamedStore.process_block_core S.E S.hc S.cfg st B).core
   by_cases hp : B.parent ∈ st.bodies
   · rw [Protocol.NamedStore.process_block_core, if_neg (not_not.mpr hp), NamedStore.commit_core]
     dsimp only [Protocol.on_block_checked_using]
     split_ifs
     · exact raw_block_order S.E st.core B.erase _ h
     · exact h
   · simpa [Protocol.NamedStore.process_block_core, hp] using h

omit [Fintype V] in
private theorem row_order (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (a : NamedAttestation V) (h : CoreOrder st.core) :
    CoreOrder (Protocol.NamedAdmission.admit_row hc st a).core := by
  rw [NamedAdmission.admit_row_core]
  dsimp only [Protocol.on_sg_vote]
  split_ifs <;> exact h

omit [Fintype V] in
private theorem rows_order (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (rows : List (NamedAttestation V)) (h : CoreOrder st.core) :
    CoreOrder (Protocol.NamedAdmission.admit_rows hc st rows).core := by
  induction rows generalizing st with
  | nil => exact h
  | cons a rows ih => exact ih _ (row_order hc st a h)

private theorem block_order (S : Setup V) (st : Protocol.NamedStore V) (B : NamedBlock V)
    (hco : Proofs.NamedStore.Coherent S.E S.cfg st) (h : CoreOrder st.core) :
    CoreOrder
      (Protocol.NamedAdmission.on_block_with .alsoCarried S.E S.hc S.cfg st B).core := by
  have hc := process_core_order S st B hco h
  dsimp only [Protocol.NamedAdmission.on_block_with, Protocol.NamedAdmission.admit_carried]
  split_ifs
  · exact rows_order S.hc _ B.attestations hc
  · exact hc

private theorem clock_order (E : Env V) (st : Protocol.NamedStore V) (t : Time)
    (h : CoreOrder st.core) : CoreOrder (Protocol.NamedStore.setClock E st t).core := h

private theorem confirmation_order (gc : Protocol.GradeContract V) (S : Setup V)
    (st : Protocol.NamedStore V) (s : Slot) (h : CoreOrder st.core) :
    CoreOrder (Protocol.NamedDuties.update_confirmation_with gc S.E S.hc st s).core := h

private theorem propose_order (gc : Protocol.GradeContract V) (S : Setup V)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (hco : Proofs.NamedStore.Coherent S.E S.cfg st) (h : CoreOrder st.core) :
    CoreOrder (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg nd st).1.core := by
  unfold Protocol.NamedDuties.propose_block_with
  split
  · exact h
  · exact block_order S st _ hco h

private theorem vote_order (gc : Protocol.GradeContract V) (S : Setup V)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V) (h : CoreOrder st.core) :
    CoreOrder (Protocol.NamedDuties.goldfish_vote_with gc S.E S.hc nd st).1.core := by
  dsimp only [Protocol.NamedDuties.goldfish_vote_with, Protocol.goldfish_vote_with]
  split_ifs
  · exact gf_order S.E st.core _ h
  · exact h

private theorem attest_order (gc : Protocol.GradeContract V) (S : Setup V)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V) (record : Protocol.NamedRecord)
    (h : CoreOrder st.core) :
    CoreOrder (Protocol.NamedDuties.attest_with gc S.E S.hc nd st record).1.core :=
  row_order S.hc st _ h

private theorem tick_order (gc : Protocol.GradeContract V) (S : Setup V)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V) (record : Protocol.NamedRecord)
    (t : Time) (hco : Proofs.NamedStore.Coherent S.E S.cfg st) (h : CoreOrder st.core) :
    CoreOrder (Protocol.NamedTick.tick gc S.E S.hc S.cfg nd st record t).1.core := by
  let s := S.E.slotOf t
  let st0 := Protocol.NamedStore.setClock S.E st t
  let st1 := if 0 < s ∧ t = Protocol.proposal_time S.E s ∧ S.E.proposer s = nd.val_index then
    (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg nd st0).1 else st0
  let st2 := if 0 < s ∧ t = Protocol.vote_time S.E s then
    (Protocol.NamedDuties.goldfish_vote_with gc S.E S.hc nd st1).1 else st1
  let st3 := if 0 < s ∧ t = Protocol.support_cutoff S.E s then
    Protocol.NamedDuties.update_confirmation_with gc S.E S.hc st2 (s - 1) else st2
  have h0 := clock_order S.E st t h
  have hc0 := NamedStore.coherent_clock S.E S.cfg st t hco
  have h1 : CoreOrder st1.core := by dsimp [st1]; split_ifs
    <;> first | exact propose_order gc S nd st0 hc0 h0 | exact h0
  have h2 : CoreOrder st2.core := by dsimp [st2]; split_ifs
    <;> first | exact vote_order gc S nd st1 h1 | exact h1
  have h3 : CoreOrder st3.core := by
    by_cases hs : 0 < s ∧ t = Protocol.support_cutoff S.E s
    · simpa [st3, hs] using confirmation_order gc S st2 (s - 1) h2
    · simpa [st3, hs] using h2
  have hstore : (Protocol.NamedTick.tick gc S.E S.hc S.cfg nd st record t).1 =
      (if t = S.hc.a S.E.Δ (S.hc.round_of st3.core.s) ∧
          nd.awake (S.hc.round_of st3.core.s) = true then
        (Protocol.NamedDuties.attest_with gc S.E S.hc nd st3 record).1 else st3) := by
    rw [NamedTick.tick_computed_duties]
    dsimp only [st3, st2, st1, st0, s]
    split_ifs <;> rfl
  rw [hstore]
  split_ifs
  · exact attest_order gc S nd st3 record h3
  · exact h3

private theorem node_tick_order (S : Setup V) (v : V) (n : NamedNodeState V) (t : Time)
    (hco : Proofs.NamedStore.Coherent S.E S.cfg n.st) (h : CoreOrder n.st.core) :
    CoreOrder (Execution.NamedNode.tick S v n t).1.st.core :=
  tick_order (NamedProfile.gradeContract
    (DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache)) S (S.node v)
    n.st n.record t hco h

private theorem node_process_order (S : Setup V) (n : NamedNodeState V) (o : NamedObject V)
    (hco : Proofs.NamedStore.Coherent S.E S.cfg n.st) (h : CoreOrder n.st.core) :
    CoreOrder (Execution.NamedNode.process S n o).st.core := by
  cases o with
  | block B => exact block_order S n.st B hco h
  | gfVote u => exact gf_order S.E n.st.core u h
  | attest a => exact row_order S.hc n.st a h

private theorem fold_order (S : Setup V) (events : List (NamedEvent V)) (w : NamedWorld V)
    (hinv : ∀ v, Proofs.NamedConfirmationMembership.Invariant S.E S.cfg (w v).st ∧
      NamedTickRecord.Invariant (w v).record)
    (h : ∀ v, CoreOrder (w v).st.core) :
    ∀ v, CoreOrder (events.foldl (NamedWorld.step S) w v).st.core := by
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
          simpa [NamedWorld.step] using NamedNode.invariants_process S (w v) o (hinv v).1 (hinv v).2
        · simpa [NamedWorld.step, Function.update_of_ne hv] using hinv v
    · intro v
      cases e with
      | tick u t =>
        by_cases hv : v = u
        · subst u
          simpa [NamedWorld.step] using
            node_tick_order S v (w v) t (hinv v).1.1.1 (h v)
        · simpa [NamedWorld.step, Function.update_of_ne hv] using h v
      | deliver u o t =>
        by_cases hv : v = u
        · subst u; simpa [NamedWorld.step] using
            node_process_order S (w v) o (hinv v).1.1.1 (h v)
        · simpa [NamedWorld.step, Function.update_of_ne hv] using h v

theorem order_stateBeforeTime
    (S : Setup V) (rho : NamedRun V) (t : Time) (v : V) :
    Block.Preceq (NamedRun.stateBeforeTime S rho t v).st.core.F
      (NamedRun.stateBeforeTime S rho t v).st.core.J :=
  fold_order S _ NamedWorld.init (fun _ => NamedNode.initial_invariants S)
    (fun _ => initial_core_order) v

/-- The FG root is the justified prefix or the finalized one, and the finalized
prefix precedes the justified one, so anything at or below the finalized prefix
is at or below the FG root. -/
theorem preceq_fg_root_of_preceq_F (S : Setup V) (rho : NamedRun V) (t : Time) (v : V)
    (P : Block V) (h : Block.Preceq P (NamedRun.stateBeforeTime S rho t v).st.core.F) :
    Block.Preceq P (Protocol.get_fg_root
      (NamedRun.stateBeforeTime S rho t v).st.core.toHealing.toFG) := by
  unfold Protocol.get_fg_root
  split_ifs
  · exact Block.preceq_trans h (order_stateBeforeTime S rho t v)
  · exact h


/-! ## Copied small helpers (private in their home modules). -/

omit [DecidableEq V] [Fintype V] in
private theorem time_le_of_key_le {e f : NamedEvent V} (h : e.key ≤ f.key) :
    e.time ≤ f.time := by
  rcases Prod.Lex.le_iff.mp h with hlt | ⟨heq, _⟩
  · exact hlt.le
  · exact heq.le

omit [DecidableEq V] [Fintype V] in
private theorem strict_filter_eq_take (rho : NamedRun V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key)) (cut : Time) :
    rho.events.filter (fun e => decide (e.time < cut)) =
      rho.events.take (rho.events.filter (fun e => decide (e.time < cut))).length := by
  have hdown : ∀ e f : NamedEvent V, e.key ≤ f.key →
      decide (f.time < cut) = true → decide (e.time < cut) = true := by
    intro e f hkey hf
    simp only [decide_eq_true_eq] at hf ⊢
    exact (time_le_of_key_le hkey).trans_lt hf
  refine List.prefix_iff_eq_take.mp ?_
  rw [Proofs.Bridges.filter_eq_takeWhile_of_pairwise hdown _ hsorted]
  exact List.takeWhile_prefix _

private theorem stateBeforeTime_eq_filter_len (S : Setup V) (rho : NamedRun V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key)) (cut : Time) :
    NamedRun.stateBeforeTime S rho cut =
      NamedRun.stateBefore S rho
        (rho.events.filter (fun e => decide (e.time < cut))).length :=
  congrArg (fun events => events.foldl (NamedWorld.step S) NamedWorld.init)
    (strict_filter_eq_take rho hsorted cut)

omit [DecidableEq V] [Fintype V] in
private theorem strict_filter_len_mono (rho : NamedRun V) {t t' : Time} (h : t ≤ t') :
    (rho.events.filter (fun e => decide (e.time < t))).length ≤
      (rho.events.filter (fun e => decide (e.time < t'))).length := by
  have hfun : (fun a : NamedEvent V => decide (a.time < t) && decide (a.time < t')) =
      fun a : NamedEvent V => decide (a.time < t) := by
    funext a
    by_cases hlt : a.time < t
    · simp only [hlt, decide_true, Bool.true_and, decide_eq_true_eq]
      exact hlt.trans_le h
    · simp only [hlt, decide_false, Bool.false_and]
  have hre : (rho.events.filter (fun e => decide (e.time < t'))).filter
      (fun e => decide (e.time < t)) =
        rho.events.filter (fun e => decide (e.time < t)) := by
    simp only [List.filter_filter, hfun]
  calc (rho.events.filter (fun e => decide (e.time < t))).length
      = ((rho.events.filter (fun e => decide (e.time < t'))).filter
          (fun e => decide (e.time < t))).length := by rw [hre]
    _ ≤ (rho.events.filter (fun e => decide (e.time < t'))).length :=
        List.length_filter_le _ _

/-- Bodies held at a strict read are retained at every later strict read. -/
private theorem bodies_time_mono (S : Setup V) (rho : NamedRun V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key)) (v : V) {t t' : Time}
    (h : t ≤ t') :
    (NamedRun.stateBeforeTime S rho t v).st.bodies ⊆
      (NamedRun.stateBeforeTime S rho t' v).st.bodies := by
  rw [stateBeforeTime_eq_filter_len S rho hsorted t,
    stateBeforeTime_eq_filter_len S rho hsorted t']
  exact NamedBodyRetention.stateBefore_bodies_mono S rho v (strict_filter_len_mono rho h)

omit [Fintype V] in
private theorem named_preceq_self (B : NamedBlock V) : NamedBlock.Preceq B B := by
  cases B <;> simp [NamedBlock.Preceq, NamedBlock.preceq]

omit [Fintype V] in
private theorem genesis_preceq (B : NamedBlock V) : NamedBlock.Preceq .genesis B := by
  induction B with
  | genesis => simp [NamedBlock.Preceq, NamedBlock.preceq]
  | node parent s root votes support rows proposer ih =>
    simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true]
    exact Or.inr ih



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

private theorem scope_of_held_strict (S : Setup V) (rho : NamedRun V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key))
    (reader : V) (hreader : reader ∈ rho.honest) (t : Time) {D : NamedBlock V}
    (hD : D ∈ (NamedRun.stateBeforeTime S rho t reader).st.bodies) :
    NamedRun.blockInRun S rho D := by
  obtain ⟨i, hread, _⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho hsorted t
  rw [hread] at hD
  exact Proofs.NamedRuntime.blockInRun_of_direct S rho
    (Proofs.NamedRuntime.directBlock_of_prefix S rho hreader i hD)

/-! ## The post-boundary replacement for `NoHonestConflictAbove`.

Pre-`b0` the guard is temporal: every honest row carried by a held body was
emitted strictly before `b0`, so the first clause of `NoHonestConflictAbove`
applies. On `[b0, S.a r]` the same rows are bounded by ROUND instead of by
time: `honest_held_ancestor_row_before_action` puts every honest row of a
body held at the round-`r` checkpoint at a round strictly below `r`, and
`IntrinsicHighEntryHistory` is exactly the compatibility statement for the
entries such rows sign. Root injectivity identifies the entry the signing
node actually derived with the certificate's named target. -/
private theorem held_row_target_compatible (S : Setup V) (rho : NamedRun V)
    (b0 b1 : Time) (r : Round) (Pn : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1)
    (hentry : IntrinsicHighEntryHistory S rho Pn r)
    (reader : V) (t : Time) (ht : t ≤ S.a r)
    {D carrier X : NamedBlock V}
    (hD : D ∈ (NamedRun.stateBeforeTime S rho t reader).st.bodies)
    (hcarrier : NamedBlock.Preceq carrier D)
    {a : NamedAttestation V} (hrow : a ∈ carrier.attestations)
    (ha : a.val_index ∈ rho.honest)
    {h : Height} {root : BlockId} {timeout : Bool}
    (hp : a.height_pair = .vote h root timeout)
    (hXscope : NamedRun.blockInRun S rho X) (hXroot : X.root = root) :
    NamedBlock.compatible Pn X = true := by
  have hDr : D ∈ (NamedRun.stateBeforeTime S rho (S.a r) reader).st.bodies :=
    bodies_time_mono S rho hexec.core.sorted reader ht hD
  obtain ⟨har, hem⟩ :=
    NamedOutageProvenance.honest_held_ancestor_row_before_action S rho
      hexec.core.toNamedScheduleWellFormed hexec.core.toNamedUnforgeable
      reader r hDr hcarrier hrow ha
  obtain ⟨i, source, entry, hSigned, hSourceHeight, hEntryRoot⟩ :=
    Proofs.NamedIntrinsicEntry.emitted_height_signed_source S rho hem hp
  have hEntryBefore : HonestEntryBefore S rho r h entry :=
    ⟨i, a, source, ha, har, hSigned, hSourceHeight⟩
  have hcompat : NamedBlock.compatible Pn entry = true := hentry h entry hEntryBefore
  rcases hSigned with ⟨_, _, _, hSourceHeld, _, hEntrySource, _, _, _⟩
  have hPre : source ∈ (NamedRun.stateBefore S rho i a.val_index).st.bodies := hSourceHeld
  have hSourceScope : NamedRun.blockInRun S rho source :=
    Proofs.NamedRuntime.blockInRun_of_direct S rho
      (Proofs.NamedRuntime.directBlock_of_prefix S rho ha i hPre)
  have hRootEq : entry.root = X.root := hEntryRoot.trans hXroot.symm
  have hEntryEq : entry = X :=
    hexec.core.toNamedRootCollisionFree.root_injective source X hSourceScope hXscope
      entry X (Or.inl hEntrySource) (Or.inr (named_preceq_self X)) hRootEq
  exact hEntryEq ▸ hcompat

/-! ## Justified, finalized and FG-root compatibility on `[b0, S.a r]`. -/

private theorem justified_compatible_after_boundary (S : Setup V) (rho : NamedRun V)
    (b0 b1 : Time) (s r : Round) (Pn : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1) (hmargin : FormationMargin S s b0)
    (hsleep : OutageSleepyThroughout S rho)
    (hentry : IntrinsicHighEntryHistory S rho Pn r)
    (reader : V) (hreader : reader ∈ rho.honest) (t : Time) (ht : t ≤ S.a r) :
    Block.compatible Pn.erase
      (NamedRun.stateBeforeTime S rho t reader).st.core.J = true := by
  obtain ⟨D, hD, hDJ, _⟩ :=
    NamedJustificationCarrier.justification_carrier_stateBeforeTime S rho t reader
  by_cases hz : (derive_named S.E S.cfg D).h_j = 0
  · have hgen := NamedJustificationCertificates.justified_zero_is_genesis S.E S.cfg D hz
    rw [← hDJ, hgen]
    have hc : NamedBlock.compatible Pn .genesis = true := by
      simp only [NamedBlock.compatible, Bool.or_eq_true]
      exact Or.inr (genesis_preceq Pn)
    exact Proofs.NamedWire.erase_compatible hc
  · obtain ⟨J, hJD, hJE, Q, hQ, hrows⟩ :=
      NamedJustificationCertificates.justification_certificate S.E S.cfg D hz
    have hDscope := scope_of_held_strict S rho hexec.core.sorted reader hreader t hD
    have hJscope := Proofs.NamedRuntime.blockInRun_of_ancestor S rho hDscope hJD
    have hbad := Proofs.NamedOutageInputs.boundary_faulty_lt_quorum S rho b0 b1 s hexec hmargin hsleep
    obtain ⟨signer, hsignerQ, hsignerHon⟩ := quorum_honest_member S rho Q hQ hbad
    obtain ⟨carrier, a, hcarrier, hrow, hv, hp⟩ := hrows signer hsignerQ
    have ha : a.val_index ∈ rho.honest := by simpa only [hv] using hsignerHon
    have hcompatible := held_row_target_compatible S rho b0 b1 r Pn hexec hentry
      reader t ht hD hcarrier hrow ha hp hJscope rfl
    have hraw := Proofs.NamedWire.erase_compatible hcompatible
    simpa only [hJE, hDJ] using hraw

/-- Despite the name this needs no boundary: `hentry` is the intrinsic
whole-history premise, so the conclusion holds at EVERY read at or before round
`r`'s action, including reads strictly before `b0`. -/
theorem finalized_compatible_after_boundary (S : Setup V) (rho : NamedRun V)
    (b0 b1 : Time) (s r : Round) (Pn : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1) (hmargin : FormationMargin S s b0)
    (hsleep : OutageSleepyThroughout S rho)
    (hentry : IntrinsicHighEntryHistory S rho Pn r)
    (reader : V) (hreader : reader ∈ rho.honest) (t : Time) (ht : t ≤ S.a r) :
    Block.compatible Pn.erase
      (NamedRun.stateBeforeTime S rho t reader).st.core.F = true := by
  have hJ := justified_compatible_after_boundary S rho b0 b1 s r Pn hexec hmargin hsleep
    hentry reader hreader t ht
  have hFJ : Block.Preceq (NamedRun.stateBeforeTime S rho t reader).st.core.F
      (NamedRun.stateBeforeTime S rho t reader).st.core.J :=
    order_stateBeforeTime S rho t reader
  rcases (show Block.Preceq Pn.erase (NamedRun.stateBeforeTime S rho t reader).st.core.J ∨
      Block.Preceq (NamedRun.stateBeforeTime S rho t reader).st.core.J Pn.erase by
    simpa only [Block.compatible, Bool.or_eq_true] using hJ) with hPJ | hJP
  · exact Block.compatible_of_preceq_common hPJ hFJ
  · simp only [Block.compatible, Bool.or_eq_true]
    exact Or.inr (Block.preceq_trans hFJ hJP)

private theorem fg_root_compatible_after_boundary (S : Setup V) (rho : NamedRun V)
    (b0 b1 : Time) (s r : Round) (Pn : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1) (hmargin : FormationMargin S s b0)
    (hsleep : OutageSleepyThroughout S rho)
    (hentry : IntrinsicHighEntryHistory S rho Pn r)
    (reader : V) (hreader : reader ∈ rho.honest) (t : Time) (ht : t ≤ S.a r) :
    Block.compatible Pn.erase
      (Protocol.get_fg_root
        (NamedRun.stateBeforeTime S rho t reader).st.core.toHealing.toFG) = true := by
  have hJ := justified_compatible_after_boundary S rho b0 b1 s r Pn hexec hmargin hsleep
    hentry reader hreader t ht
  have hF := finalized_compatible_after_boundary S rho b0 b1 s r Pn hexec hmargin hsleep
    hentry reader hreader t ht
  unfold Protocol.get_fg_root
  split_ifs <;> assumption

/-! ## The conflicting-carrier band at a post-boundary read. -/

private theorem held_band_after_boundary (S : Setup V) (rho : NamedRun V)
    (b0 b1 : Time) (r : Round) (Pn : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1)
    (hband : IntrinsicConflictingCarrierBand S rho Pn r)
    (reader : V) (hreader : reader ∈ rho.honest) (t : Time) (ht : t ≤ S.a r)
    {D : NamedBlock V} (hD : D ∈ (NamedRun.stateBeforeTime S rho t reader).st.bodies)
    (hConflict : NamedBlock.compatible Pn D = false) :
    (derive_named S.E S.cfg D).h ≤ (derive_named S.E S.cfg Pn).h + 1 := by
  have hDr : D ∈ (NamedRun.stateBeforeTime S rho (S.a r) reader).st.bodies :=
    bodies_time_mono S rho hexec.core.sorted reader ht hD
  have hprior : PriorCarrierRows S rho r D :=
    NamedCheckpointRows.prior_carrier_rows_at_checkpoint S rho
      hexec.core.toNamedScheduleWellFormed hexec.core.toNamedUnforgeable reader r hDr
  have hDscope := scope_of_held_strict S rho hexec.core.sorted reader hreader t hD
  exact hband D hDscope hprior hConflict

/-! ## L4: post-boundary FG non-interference on the cut `[b0, S.a r]`. -/


/-- **A held protected prefix is VIABLE at every strict read in `[b0, S.a r]`.**
The witness half of `fg_noninterference_after_boundary`, with no FG-root clause
on the conclusion, because viability and the root descent are independent halves
of the candidate tree.

The witness is found in one of two places. Either the reader's maximum carrier
is within one height of `Pn`'s own, and then `Pn` is its own witness; or it is
not, and then that maximum carrier EXTENDS `Pn`, because a carrier conflicting
with `Pn` cannot stand that high inside the window (`held_band_after_boundary`,
which is where the band spends itself).

 24 made the stable record's write range over the viable
tree, so the window needs this half on its own: the duty writes the deepest
VIABLE ancestor of the round's frozen G2 root, and it carries `Pn` only when
`Pn` is walkable at the writing node. The pre-boundary twin is
`NamedFGProtection.viable_of_held_before_boundary`. -/
theorem viable_after_boundary
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (r : Round) (Pn : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1)
    (hband : IntrinsicConflictingCarrierBand S rho Pn r)
    (w : V) (hw : w ∈ rho.honest) (t : Time) (ht : t ≤ S.a r)
    (hheld : Pn ∈ (NamedRun.stateBeforeTime S rho t w).st.bodies)
    (hFP : Block.Preceq (NamedRun.stateBeforeTime S rho t w).st.core.F Pn.erase) :
    Pn.erase ∈ Protocol.V_tree
      (NamedRun.stateBeforeTime S rho t w).st.core.toHealing.toFG := by
  set st := (NamedRun.stateBeforeTime S rho t w).st with hst
  have hcoh : Proofs.NamedStore.Coherent S.E S.cfg st :=
    (Proofs.NamedRuntime.stateBeforeTime_invariants S rho t w).1.1.1
  have hPraw : Pn.erase ∈ st.core.T := by
    rw [hcoh.1]
    exact Finset.mem_image_of_mem NamedBlock.erase hheld
  have hWitness : ∃ W ∈ st.core.T, Block.Preceq Pn.erase W ∧
      st.core.h_max - 1 ≤ (st.core.σ W).h := by
    by_cases hLow : st.core.h_max ≤ (derive_named S.E S.cfg Pn).h + 1
    · refine ⟨Pn.erase, hPraw, Block.preceq_self _, ?_⟩
      rw [hcoh.2.2.2.2 Pn hheld]
      exact Nat.sub_le_iff_le_add.mpr hLow
    · obtain ⟨D, hD, hMax⟩ :=
        NamedMaximumCarrier.maximum_carrier_stateBeforeTime S rho t w
      have hDcompatible : NamedBlock.compatible Pn D = true := by
        by_contra hc
        have hBand := held_band_after_boundary S rho b0 b1 r Pn hexec hband
          w hw t ht hD (Bool.eq_false_of_not_eq_true hc)
        rw [hMax] at hBand
        exact hLow hBand
      have hPD : NamedBlock.Preceq Pn D := by
        rcases (show NamedBlock.Preceq Pn D ∨ NamedBlock.Preceq D Pn by
          simpa only [NamedBlock.compatible, Bool.or_eq_true] using hDcompatible) with
            hAbove | hAncestor
        · exact hAbove
        · have hle := Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hAncestor
          rw [hMax] at hle
          exact False.elim (hLow (hle.trans (Nat.le_succ _)))
      have hDraw : D.erase ∈ st.core.T := by
        rw [hcoh.1]
        exact Finset.mem_image_of_mem NamedBlock.erase hD
      refine ⟨D.erase, hDraw, Proofs.NamedWire.erase_preceq hPD, ?_⟩
      rw [hcoh.2.2.2.2 D hD, hMax]
      exact Nat.sub_le _ _
  change Pn.erase ∈ Protocol.viable_tree st.core.σ st.core.F st.core.h_max st.core.T
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_filter.mpr ⟨hPraw, hFP⟩, ?_⟩
  simpa only [Protocol.viable, decide_eq_true_eq] using hWitness

#print axioms viable_after_boundary

/-- Every honest reader still holds `Pn`, still keeps `Pn` inside its FG
choice (either past the FG root or in the filtered tree), and still has a
finalized block compatible with `Pn`, at every strict read in `[b0, S.a r]`.

`hslash` and `hno` are unused: with `hband` and `hentry` given as premises the
accountable bound and the pre-`b0` honest-behaviour guard do no work here.
`hheld0` replaces `NamedBoundaryHolding.stable_prefix_held_at_boundary`, whose
`stableAt` premise is not among this target's premises. -/
theorem fg_noninterference_after_boundary
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (s r : Round) (Pn : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1)
    (_hslash : Internal.NamedOutageEntry.SlashableBound S rho)
    (hmargin : FormationMargin S s b0) (hsleep : OutageSleepyThroughout S rho)
    (_hPn : NamedRun.blockInRun S rho Pn)
    (_hno : NoHonestConflictAbove S rho b0 Pn.erase)
    (hband : IntrinsicConflictingCarrierBand S rho Pn r)
    (hentry : IntrinsicHighEntryHistory S rho Pn r)
    (hheld0 : ∀ u ∈ rho.honest, Pn ∈ (NamedRun.stateBeforeTime S rho b0 u).st.bodies)
    (w : V) (hw : w ∈ rho.honest) (t : Time) (hb0 : b0 ≤ t) (ht : t ≤ S.a r) :
    Pn ∈ (NamedRun.stateBeforeTime S rho t w).st.bodies ∧
    (Block.Preceq Pn.erase
       (Protocol.get_fg_root (NamedRun.stateBeforeTime S rho t w).st.core.toHealing.toFG) ∨
     Pn.erase ∈ Protocol.get_filtered_block_tree
       (NamedRun.stateBeforeTime S rho t w).st.core.toHealing.toFG) ∧
    Block.compatible Pn.erase (NamedRun.stateBeforeTime S rho t w).st.core.F = true := by
  have hheld : Pn ∈ (NamedRun.stateBeforeTime S rho t w).st.bodies :=
    bodies_time_mono S rho hexec.core.sorted w hb0 (hheld0 w hw)
  refine ⟨hheld, ?_, finalized_compatible_after_boundary S rho b0 b1 s r Pn hexec
    hmargin hsleep hentry w hw t ht⟩
  set st := (NamedRun.stateBeforeTime S rho t w).st with hst
  have hcoh : Proofs.NamedStore.Coherent S.E S.cfg st :=
    (Proofs.NamedRuntime.stateBeforeTime_invariants S rho t w).1.1.1
  have hcompatible := fg_root_compatible_after_boundary S rho b0 b1 s r Pn hexec
    hmargin hsleep hentry w hw t ht
  rcases (show Block.Preceq Pn.erase (Protocol.get_fg_root st.core.toHealing.toFG) ∨
      Block.Preceq (Protocol.get_fg_root st.core.toHealing.toFG) Pn.erase by
    simpa only [Block.compatible, Bool.or_eq_true] using hcompatible) with hPast | hRoot
  · exact Or.inl hPast
  · right
    have hFRoot : Block.Preceq st.core.F (Protocol.get_fg_root st.core.toHealing.toFG) :=
      Proofs.Records.preceq_get_fg_root_of_F (st := st.core.toHealing.toFG)
        (order_stateBeforeTime S rho t w)
    have hFP : Block.Preceq st.core.F Pn.erase := Block.preceq_trans hFRoot hRoot
    exact Proofs.Records.mem_filtered_of_mem_V_tree
      (viable_after_boundary S rho b0 b1 r Pn hexec hband w hw t ht hheld hFP) hRoot

/-! ## The non-strict `readAt` form.

`NamedRun.readAt` keeps every event with `e.time <= t`, so it is the strict
fold one unit later. The window therefore shortens by one at the top: the
`readAt` form holds for `b0 <= t < S.a r` and NOT at `t = S.a r`, where the
reader may already have processed the round-`r` action events that every
checkpoint lemma excludes. -/
private theorem readAt_eq_stateBeforeTime_succ (S : Setup V) (rho : NamedRun V) (t : Time) :
    NamedRun.readAt S rho t = NamedRun.stateBeforeTime S rho (t + 1) := by
  have hp : (fun e : NamedEvent V => decide (e.time ≤ t)) =
      fun e : NamedEvent V => decide (e.time < t + 1) := by
    funext e
    exact decide_eq_decide.mpr Int.lt_add_one_iff.symm
  unfold NamedRun.readAt NamedRun.stateBeforeTime
  rw [hp]

theorem fg_noninterference_after_boundary_readAt
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (s r : Round) (Pn : NamedBlock V)
    (hexec : OutageExecution S rho b0 b1)
    (hslash : Internal.NamedOutageEntry.SlashableBound S rho)
    (hmargin : FormationMargin S s b0) (hsleep : OutageSleepyThroughout S rho)
    (hPn : NamedRun.blockInRun S rho Pn)
    (hno : NoHonestConflictAbove S rho b0 Pn.erase)
    (hband : IntrinsicConflictingCarrierBand S rho Pn r)
    (hentry : IntrinsicHighEntryHistory S rho Pn r)
    (hheld0 : ∀ u ∈ rho.honest, Pn ∈ (NamedRun.stateBeforeTime S rho b0 u).st.bodies)
    (w : V) (hw : w ∈ rho.honest) (t : Time) (hb0 : b0 ≤ t) (ht : t < S.a r) :
    Pn ∈ (NamedRun.readAt S rho t w).st.bodies ∧
    (Block.Preceq Pn.erase
       (Protocol.get_fg_root (NamedRun.readAt S rho t w).st.core.toHealing.toFG) ∨
     Pn.erase ∈ Protocol.get_filtered_block_tree
       (NamedRun.readAt S rho t w).st.core.toHealing.toFG) ∧
    Block.compatible Pn.erase (NamedRun.readAt S rho t w).st.core.F = true := by
  rw [readAt_eq_stateBeforeTime_succ S rho t]
  exact fg_noninterference_after_boundary S rho b0 b1 s r Pn hexec hslash hmargin hsleep
    hPn hno hband hentry hheld0 w hw (t + 1) (Int.le_add_one hb0)
    (Int.add_one_le_iff.mpr ht)

#print axioms Proofs.NamedOutageInputs.boundary_faulty_lt_quorum
#print axioms fg_noninterference_after_boundary
#print axioms fg_noninterference_after_boundary_readAt

end DecoupledConsensusModel.Proofs.NamedOutageClosure

end
