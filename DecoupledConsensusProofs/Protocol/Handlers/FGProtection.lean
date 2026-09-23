module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ChainState.JustificationCertificates
public import DecoupledConsensusProofs.Protocol.Handlers.JustificationCarrier
public import DecoupledConsensusProofs.Protocol.Handlers.MaximumCarrier
public import DecoupledConsensusProofs.Execution.FinalityGuard
public import DecoupledConsensusProofs.Protocol.Handlers.Invariants2

@[expose] public section

namespace DecoupledConsensusModel.Proofs.NamedFGProtection
open Execution Internal.NamedOutageEntry Internal.NamedStableChainOutage Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

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

private theorem order_stateBeforeTime
    (S : Setup V) (rho : NamedRun V) (t : Time) (v : V) :
    Block.Preceq (NamedRun.stateBeforeTime S rho t v).st.core.F
      (NamedRun.stateBeforeTime S rho t v).st.core.J :=
  fold_order S _ NamedWorld.init (fun _ => NamedNode.initial_invariants S)
    (fun _ => initial_core_order) v

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
private theorem genesis_preceq (B : NamedBlock V) : NamedBlock.Preceq .genesis B := by
  induction B with
  | genesis => simp [NamedBlock.Preceq, NamedBlock.preceq]
  | node parent s root votes support rows proposer ih =>
    simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true]
    exact Or.inr ih

omit [Fintype V] in
private theorem named_extend {A parent : NamedBlock V} (s : Slot) (root : BlockId)
    (votes support : List (GoldfishVote V)) (rows : List (NamedAttestation V)) (proposer : V)
    (h : NamedBlock.Preceq A parent) :
    NamedBlock.Preceq A (.node parent s root votes support rows proposer) := by
  simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true]
  exact Or.inr h

omit [Fintype V] in
private theorem named_trans {A B C : NamedBlock V}
    (hAB : NamedBlock.Preceq A B) (hBC : NamedBlock.Preceq B C) : NamedBlock.Preceq A C := by
  induction C with
  | genesis =>
    simp only [NamedBlock.Preceq, NamedBlock.preceq, decide_eq_true_eq] at hBC
    subst B
    exact hAB
  | node parent s root votes support rows proposer ih =>
    simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true, decide_eq_true_eq] at hBC
    rcases hBC with rfl | hparent
    · exact hAB
    · exact named_extend s root votes support rows proposer (ih hparent)

private theorem scope_of_held_strict (S : Setup V) (rho : NamedRun V)
    (hsorted : rho.events.Pairwise (fun e f => e.key ≤ f.key))
    (reader : V) (hreader : reader ∈ rho.honest) (t : Time) {D : NamedBlock V}
    (hD : D ∈ (NamedRun.stateBeforeTime S rho t reader).st.bodies) :
    NamedRun.blockInRun S rho D := by
  obtain ⟨i, hread, _⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho hsorted t
  rw [hread] at hD
  exact Proofs.NamedRuntime.blockInRun_of_direct S rho
    (Proofs.NamedRuntime.directBlock_of_prefix S rho hreader i hD)

private theorem honest_held_row_before_boundary
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time)
    (hexec : OutageExecution S rho b0 b1)
    (reader : V) (t : Time) (ht : t ≤ b0) {D carrier : NamedBlock V}
    (hD : D ∈ (NamedRun.stateBeforeTime S rho t reader).st.bodies)
    (hcarrier : NamedBlock.Preceq carrier D) {a : NamedAttestation V}
    (hrow : a ∈ carrier.attestations) (ha : a.val_index ∈ rho.honest) :
    NamedRun.emits S rho a.val_index (.attest a) (S.a a.round) ∧ S.a a.round < b0 := by
  obtain ⟨i, hread, hbefore⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix S rho hexec.core.sorted t
  rw [hread] at hD
  obtain ⟨j, hj, received, hacc, hsend, hem⟩ :=
    NamedOutageProvenance.honest_held_ancestor_row_emission S rho
      hexec.core.toNamedUnforgeable i reader hD hcarrier hrow ha
  obtain ⟨e, he, _, het⟩ := hacc.1.2
  have hreceived : received < t := by simpa only [het] using hbefore j e hj he
  exact ⟨hem, (hsend.trans_lt hreceived).trans_le ht⟩

private theorem justified_compatible_before_boundary
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (s : Round)
    (hexec : OutageExecution S rho b0 b1) (hmargin : FormationMargin S s b0)
    (hsleep : OutageSleepyThroughout S rho)
    (P : NamedBlock V) (hP : NamedRun.blockInRun S rho P)
    (hno : NoHonestConflictAbove S rho b0 P.erase)
    (reader : V) (hreader : reader ∈ rho.honest) (t : Time) (ht : t ≤ b0) :
    Block.compatible P.erase (NamedRun.stateBeforeTime S rho t reader).st.core.J = true := by
  obtain ⟨D, hD, hDJ, _⟩ :=
    NamedJustificationCarrier.justification_carrier_stateBeforeTime S rho t reader
  by_cases hz : (derive_named S.E S.cfg D).h_j = 0
  · have hgen := NamedJustificationCertificates.justified_zero_is_genesis S.E S.cfg D hz
    rw [← hDJ, hgen]
    have hc : NamedBlock.compatible P .genesis = true := by
      simp only [NamedBlock.compatible, Bool.or_eq_true]
      exact Or.inr (genesis_preceq P)
    exact Proofs.NamedWire.erase_compatible hc
  · obtain ⟨J, hJD, hJE, Q, hQ, hrows⟩ :=
      NamedJustificationCertificates.justification_certificate S.E S.cfg D hz
    have hDscope := scope_of_held_strict S rho hexec.core.sorted reader hreader t hD
    have hJscope := Proofs.NamedRuntime.blockInRun_of_ancestor S rho hDscope hJD
    have hbad := Proofs.NamedOutageInputs.boundary_faulty_lt_quorum S rho b0 b1 s hexec hmargin
      hsleep
    obtain ⟨signer, hsignerQ, hsignerHon⟩ := quorum_honest_member S rho Q hQ hbad
    obtain ⟨carrier, a, hcarrier, hrow, hv, hp⟩ := hrows signer hsignerQ
    have ha : a.val_index ∈ rho.honest := by simpa only [hv] using hsignerHon
    obtain ⟨hem, hsent⟩ := honest_held_row_before_boundary S rho b0 b1 hexec
      reader t ht hD hcarrier hrow ha
    have hcompatible := hno.1 P hP rfl a (S.a a.round) ha hem hsent
      _ J.root false hp J hJscope rfl
    have hraw := Proofs.NamedWire.erase_compatible hcompatible
    simpa only [hJE, hDJ] using hraw

private theorem fg_root_compatible_before_boundary
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (s : Round)
    (hexec : OutageExecution S rho b0 b1) (hmargin : FormationMargin S s b0)
    (hsleep : OutageSleepyThroughout S rho)
    (P : NamedBlock V) (hP : NamedRun.blockInRun S rho P)
    (hno : NoHonestConflictAbove S rho b0 P.erase)
    (reader : V) (hreader : reader ∈ rho.honest) (t : Time) (ht : t ≤ b0) :
    Block.compatible P.erase
      (Protocol.get_fg_root (NamedRun.stateBeforeTime S rho t reader).st.core.toHealing.toFG) =
        true := by
  have hJ := justified_compatible_before_boundary S rho b0 b1 s hexec hmargin hsleep
    P hP hno reader hreader t ht
  obtain ⟨F, _hF, hFE, hFcompatible⟩ :=
    NamedFinalityGuard.finalized_representative_compatible_before_boundary
      S rho b0 b1 s hexec hmargin hsleep P hP hno reader hreader t ht
  have hF := Proofs.NamedWire.erase_compatible hFcompatible
  rw [hFE] at hF
  unfold Protocol.get_fg_root
  split_ifs <;> assumption

omit [DecidableEq V] [Fintype V] in
private theorem matching_vote (a : NamedAttestation V) (h : Height) (root : BlockId)
    (hm : a.height_pair.matchesEntry h root = true) :
    ∃ timeout : Bool, a.height_pair = .vote h root timeout := by
  cases hp : a.height_pair with
  | empty => simp [hp, NamedHeightPair.matchesEntry] at hm
  | vote height entry timeout =>
    have heq : height = h ∧ entry = root := by
      simpa only [hp, NamedHeightPair.matchesEntry, decide_eq_true_eq] using hm
    rcases heq with ⟨rfl, rfl⟩
    exact ⟨timeout, rfl⟩

-- Direct strict-read band: original row provenance supplies the temporal cut.
-- No first-checkpoint history, interpolation, or support input is required.
private theorem held_conflicting_carrier_band_before_boundary
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (s : Round)
    (hexec : OutageExecution S rho b0 b1) (hmargin : FormationMargin S s b0)
    (hsleep : OutageSleepyThroughout S rho)
    (P : NamedBlock V) (hP : NamedRun.blockInRun S rho P)
    (hno : NoHonestConflictAbove S rho b0 P.erase)
    (reader : V) (hreader : reader ∈ rho.honest) (t : Time) (ht : t ≤ b0)
    {D : NamedBlock V} (hD : D ∈ (NamedRun.stateBeforeTime S rho t reader).st.bodies)
    (hConflict : NamedBlock.compatible P D = false) :
    (derive_named S.E S.cfg D).h ≤ (derive_named S.E S.cfg P).h + 1 := by
  by_contra hNot
  let H := (derive_named S.E S.cfg P).h + 1
  have hPassed : H < (derive_named S.E S.cfg D).h := Nat.lt_of_not_ge hNot
  obtain ⟨X, hXD, hXHeight, Q, hQ, hrows⟩ :=
    NamedFinalityCertificates.height_crossing S.E S.cfg D H
      (Nat.succ_le_succ (Nat.zero_le _)) hPassed
  have hDscope := scope_of_held_strict S rho hexec.core.sorted reader hreader t hD
  have hXscope := Proofs.NamedRuntime.blockInRun_of_ancestor S rho hDscope hXD
  have hbad := Proofs.NamedOutageInputs.boundary_faulty_lt_quorum S rho b0 b1 s hexec hmargin
    hsleep
  obtain ⟨signer, hsignerQ, hsignerHon⟩ := quorum_honest_member S rho Q hQ hbad
  obtain ⟨carrier, a, hcarrier, hrow, hv, hm⟩ := hrows signer hsignerQ
  have ha : a.val_index ∈ rho.honest := by simpa only [hv] using hsignerHon
  obtain ⟨hem, hsent⟩ := honest_held_row_before_boundary S rho b0 b1 hexec
    reader t ht hD hcarrier hrow ha
  obtain ⟨timeout, hp⟩ := matching_vote a H X.root hm
  have hcompatible := hno.1 P hP rfl a (S.a a.round) ha hem hsent
    H X.root timeout hp X hXscope rfl
  simp only [NamedBlock.compatible, Bool.or_eq_true] at hcompatible
  rcases hcompatible with hPX | hXP
  · have hnamed : NamedBlock.Preceq P D := named_trans hPX hXD
    have hc : NamedBlock.compatible P D = true := by
      simp only [NamedBlock.compatible, Bool.or_eq_true]
      exact Or.inl hnamed
    exact Bool.false_ne_true (hConflict.symm.trans hc)
  · have hle := Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hXP
    rw [hXHeight] at hle
    exact (Nat.not_le_of_gt (Nat.lt_succ_self _)) hle


/-- **A held protected prefix is VIABLE at a strict read before the boundary.**
This is the witness half of `fg_protection_of_held_before_boundary`, with no
FG-root clause on the conclusion, because viability and the root descent are
independent halves of the candidate tree.

The witness is found in one of two places. Either the reader's own maximum is
within one height of `P`'s carrier, and then `P` is its own witness; or it is
not, and then the maximum carrier itself extends `P`, because a carrier that
CONFLICTS with `P` cannot stand that high before the boundary
(`held_conflicting_carrier_band_before_boundary`, which is where the no-honest-
conflict premise and the sleepy window are spent).

 24 made the stable record's write range over the viable
tree, so the outage window now needs this half on its own: the duty writes the
deepest VIABLE ancestor of the round's frozen G2 root, and it can only carry `P`
when `P` itself is viable at the writing node. -/
theorem viable_of_held_before_boundary
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (s : Round)
    (hexec : OutageExecution S rho b0 b1) (hmargin : FormationMargin S s b0)
    (hsleep : OutageSleepyThroughout S rho)
    (P : NamedBlock V) (hno : NoHonestConflictAbove S rho b0 P.erase)
    (reader : V) (hreader : reader ∈ rho.honest) (t : Time) (ht : t ≤ b0)
    (hheld : P ∈ (NamedRun.stateBeforeTime S rho t reader).st.bodies)
    (hFP : Block.Preceq (NamedRun.stateBeforeTime S rho t reader).st.core.F P.erase) :
    P.erase ∈ Protocol.V_tree
      (NamedRun.stateBeforeTime S rho t reader).st.core.toHealing.toFG := by
  let st := (NamedRun.stateBeforeTime S rho t reader).st
  have hcoh : Proofs.NamedStore.Coherent S.E S.cfg st :=
    (Proofs.NamedRuntime.stateBeforeTime_invariants S rho t reader).1.1.1
  have hP := scope_of_held_strict S rho hexec.core.sorted reader hreader t hheld
  have hPraw : P.erase ∈ st.core.T := by
    rw [hcoh.1]
    exact Finset.mem_image_of_mem NamedBlock.erase hheld
  have hWitness : ∃ W ∈ st.core.T, Block.Preceq P.erase W ∧
      st.core.h_max - 1 ≤ (st.core.σ W).h := by
    by_cases hLow : st.core.h_max ≤ (derive_named S.E S.cfg P).h + 1
    · refine ⟨P.erase, hPraw, Block.preceq_self _, ?_⟩
      rw [hcoh.2.2.2.2 P hheld]
      exact Nat.sub_le_iff_le_add.mpr hLow
    · obtain ⟨D, hD, hMax⟩ :=
        NamedMaximumCarrier.maximum_carrier_stateBeforeTime S rho t reader
      have hDcompatible : NamedBlock.compatible P D = true := by
        by_contra hc
        have hBand := held_conflicting_carrier_band_before_boundary
          S rho b0 b1 s hexec hmargin hsleep P hP hno reader hreader t ht hD
          (Bool.eq_false_of_not_eq_true hc)
        rw [hMax] at hBand
        exact hLow hBand
      have hPD : NamedBlock.Preceq P D := by
        rcases (show NamedBlock.Preceq P D ∨ NamedBlock.Preceq D P by
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
  change P.erase ∈ Protocol.viable_tree st.core.σ st.core.F st.core.h_max st.core.T
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_filter.mpr ⟨hPraw, hFP⟩, ?_⟩
  simpa only [Protocol.viable, decide_eq_true_eq] using hWitness

#print axioms viable_of_held_before_boundary

/-- Internal strict-read consumer of an actually held full protected prefix.
The result supplies either an FG root past P or P's filtered-tree membership.
No active SG, support, maximum witness, or viability callback is an input. -/
theorem fg_protection_of_held_before_boundary
    (S : Setup V) (rho : NamedRun V) (b0 b1 : Time) (s : Round)
    (hexec : OutageExecution S rho b0 b1) (hmargin : FormationMargin S s b0)
    (hsleep : OutageSleepyThroughout S rho)
    (P : NamedBlock V) (hno : NoHonestConflictAbove S rho b0 P.erase)
    (reader : V) (hreader : reader ∈ rho.honest) (t : Time) (ht : t ≤ b0)
    (hheld : P ∈ (NamedRun.stateBeforeTime S rho t reader).st.bodies) :
    Block.Preceq P.erase
      (Protocol.get_fg_root
        (NamedRun.stateBeforeTime S rho t reader).st.core.toHealing.toFG) ∨
    P.erase ∈ Protocol.get_filtered_block_tree
      (NamedRun.stateBeforeTime S rho t reader).st.core.toHealing.toFG := by
  let st := (NamedRun.stateBeforeTime S rho t reader).st
  have hcoh : Proofs.NamedStore.Coherent S.E S.cfg st :=
    (Proofs.NamedRuntime.stateBeforeTime_invariants S rho t reader).1.1.1
  have hP := scope_of_held_strict S rho hexec.core.sorted reader hreader t hheld
  have hcompatible := fg_root_compatible_before_boundary
    S rho b0 b1 s hexec hmargin hsleep P hP hno reader hreader t ht
  rcases (show Block.Preceq P.erase (Protocol.get_fg_root st.core.toHealing.toFG) ∨
      Block.Preceq (Protocol.get_fg_root st.core.toHealing.toFG) P.erase by
    simpa only [Block.compatible, Bool.or_eq_true] using hcompatible) with hPast | hRoot
  · exact Or.inl hPast
  · right
    have hFRoot : Block.Preceq st.core.F (Protocol.get_fg_root st.core.toHealing.toFG) :=
      Proofs.Records.preceq_get_fg_root_of_F (st := st.core.toHealing.toFG)
        (order_stateBeforeTime S rho t reader)
    have hFP : Block.Preceq st.core.F P.erase := Block.preceq_trans hFRoot hRoot
    exact Proofs.Records.mem_filtered_of_mem_V_tree
      (viable_of_held_before_boundary S rho b0 b1 s hexec hmargin hsleep P hno reader
        hreader t ht hheld hFP) hRoot

end DecoupledConsensusModel.Proofs.NamedFGProtection

end
