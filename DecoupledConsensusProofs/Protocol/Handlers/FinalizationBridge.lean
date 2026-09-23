module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Handlers.NumericStore
public import DecoupledConsensusProofs.Execution.NamedAncestry

@[expose] public section

namespace DecoupledConsensusModel.Proofs.NamedFinalizationBridge
open Execution Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

private def CoreFinalizer (st : Protocol.Store V) : Prop :=
  ∃ D ∈ st.T, (st.σ D).F = st.F ∧ (st.σ D).h_F < st.h_max

omit [Fintype V] in
private theorem initial_core_finalizer :
    CoreFinalizer (Protocol.NamedStore.initial : Protocol.NamedStore V).core := by
  exact ⟨Block.genesis, Finset.mem_singleton_self _, rfl, Nat.zero_lt_succ 0⟩

omit [DecidableEq V] [Fintype V] in
private theorem unchanged {st next : Protocol.Store V}
    (hT : next.T = st.T) (hSigma : next.σ = st.σ)
    (hF : next.F = st.F) (hMax : st.h_max ≤ next.h_max)
    (h : CoreFinalizer st) : CoreFinalizer next := by
  obtain ⟨D, hD, hDF, hDh⟩ := h
  refine ⟨D, ?_, ?_, ?_⟩
  · rwa [hT]
  · rwa [hSigma, hF]
  · rw [hSigma]
    exact hDh.trans_le hMax

private theorem gf_fields (E : Env V) (st : Protocol.Store V) (u : GoldfishVote V) :
    let out := Protocol.on_goldfish_vote_checked E st u
    out.T = st.T ∧ out.σ = st.σ ∧ out.F = st.F ∧ out.h_max = st.h_max := by
  dsimp only [Protocol.on_goldfish_vote_checked, Protocol.on_goldfish_vote]
  split_ifs <;> exact ⟨rfl, rfl, rfl, rfl⟩

private theorem gf_fold_fields (E : Env V) (st : Protocol.Store V)
    (votes : List (GoldfishVote V)) :
    let out := votes.foldl (Protocol.on_goldfish_vote_checked E) st
    out.T = st.T ∧ out.σ = st.σ ∧ out.F = st.F ∧ out.h_max = st.h_max := by
  induction votes generalizing st with
  | nil => exact ⟨rfl, rfl, rfl, rfl⟩
  | cons u votes ih =>
    have rest := ih (Protocol.on_goldfish_vote_checked E st u)
    have one := gf_fields E st u
    exact ⟨rest.1.trans one.1, rest.2.1.trans one.2.1,
      rest.2.2.1.trans one.2.2.1, rest.2.2.2.trans one.2.2.2⟩

omit [Fintype V] in
private theorem update_finalizer (st : Protocol.Store V) (B : Block V)
    (sigma : ChainState V) (hB : B ∈ st.T) (hSigma : st.σ B = sigma)
    (hStrict : sigma.h_F < sigma.h) (h : CoreFinalizer st) :
    CoreFinalizer (Protocol.update_finality st sigma) := by
  obtain ⟨D, hD, hDF, hDh⟩ := h
  have hOld : (st.σ D).h_F < max st.h_max sigma.h :=
    hDh.trans_le (Nat.le_max_left _ _)
  have hNew : (st.σ B).h_F < max st.h_max sigma.h := by
    rw [hSigma]
    exact hStrict.trans_le (Nat.le_max_right _ _)
  have hNewF : (st.σ B).F = sigma.F := congrArg ChainState.F hSigma
  dsimp only [Protocol.update_finality]
  split_ifs <;> first
    | exact ⟨B, hB, hNewF, hNew⟩
    | exact ⟨D, hD, hDF, hOld⟩

private theorem raw_block_finalizer (E : Env V) (st : Protocol.Store V) (B : Block V)
    (build : ChainState V → ChainState V)
    (hStrict : (build (st.σ B.parent)).h_F < (build (st.σ B.parent)).h)
    (h : CoreFinalizer st) : CoreFinalizer (Protocol.on_block_using E st B build) := by
  dsimp only [Protocol.on_block_using]
  split_ifs with hguard hpre hproposer hslot <;> first
    | exact h
    | (let sigma := build (st.σ B.parent)
       let stored : Protocol.Store V := { st with
         σ := fun C => if C = B then sigma else st.σ C
         T := insert B st.T
         timestamp_block := fun C => if C = B then some (st.t : Stamp) else st.timestamp_block C }
       let unpacked := B.gf_votes.foldl (Protocol.on_goldfish_vote_checked E) stored
       have hFresh : B ∉ st.T := fun hB => hguard (Or.inr (Or.inl hB))
       have hStored : CoreFinalizer stored := by
         obtain ⟨D, hD, hDF, hDh⟩ := h
         have hDB : D ≠ B := by intro heq; subst D; exact hFresh hD
         exact ⟨D, Finset.mem_insert_of_mem hD, by simpa [stored, if_neg hDB] using hDF,
           by simpa [stored, if_neg hDB] using hDh⟩
       have fields := gf_fold_fields E stored B.gf_votes
       change CoreFinalizer (Protocol.update_finality unpacked (unpacked.σ B))
       have hsigma : unpacked.σ B = sigma := by
         rw [fields.2.1]
         simp [stored, sigma]
       rw [hsigma]
       apply update_finalizer _ B sigma
       · rw [fields.1]
         exact Finset.mem_insert_self _ _
       · exact hsigma
       · exact hStrict
       · exact unchanged fields.1 fields.2.1 fields.2.2.1
           (by rw [fields.2.2.2]) hStored)

private theorem process_core_finalizer (S : Setup V) (st : Protocol.NamedStore V)
    (B : NamedBlock V) (hco : Proofs.NamedStore.Coherent S.E S.cfg st)
    (h : CoreFinalizer st.core) :
    CoreFinalizer (Protocol.NamedStore.process_block_core S.E S.hc S.cfg st B).core := by
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
    · change CoreFinalizer (Protocol.on_block_using S.E st.core Block.genesis _)
      simpa [Protocol.on_block_using, hmem] using h
    · exact h
  | node parent slot root votes support rows proposer =>
   let B : NamedBlock V := .node parent slot root votes support rows proposer
   change CoreFinalizer
     (Protocol.NamedStore.process_block_core S.E S.hc S.cfg st B).core
   by_cases hp : B.parent ∈ st.bodies
   · have hParent := hco.2.2.2.2 B.parent hp
     have hStrict :
        (named_transition S.E S.cfg (st.core.σ B.erase.parent) B).h_F <
          (named_transition S.E S.cfg (st.core.σ B.erase.parent) B).h := by
       rw [Proofs.NamedWire.erase_parent, hParent]
       change (derive_named S.E S.cfg B).h_F < (derive_named S.E S.cfg B).h
       exact (Proofs.NamedStoreRoots.chainOrder_derive_named S.E S.cfg B).heights_ordered.trans_lt
         (Proofs.NamedStoreRoots.chainOrder_derive_named S.E S.cfg B).justified_below_height
     rw [Protocol.NamedStore.process_block_core, if_neg (not_not.mpr hp), NamedStore.commit_core]
     dsimp only [Protocol.on_block_checked_using]
     split_ifs
     · exact raw_block_finalizer S.E st.core B.erase _ hStrict h
     · exact h
   · simpa [Protocol.NamedStore.process_block_core, hp] using h

omit [Fintype V] in
private theorem row_finalizer (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (a : NamedAttestation V) (h : CoreFinalizer st.core) :
    CoreFinalizer (Protocol.NamedAdmission.admit_row hc st a).core := by
  rw [NamedAdmission.admit_row_core]
  dsimp only [Protocol.on_sg_vote]
  split_ifs <;> exact h

omit [Fintype V] in
private theorem rows_finalizer (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (rows : List (NamedAttestation V)) (h : CoreFinalizer st.core) :
    CoreFinalizer (Protocol.NamedAdmission.admit_rows hc st rows).core := by
  induction rows generalizing st with
  | nil => exact h
  | cons a rows ih => exact ih _ (row_finalizer hc st a h)

private theorem block_finalizer (S : Setup V) (st : Protocol.NamedStore V) (B : NamedBlock V)
    (hco : Proofs.NamedStore.Coherent S.E S.cfg st) (h : CoreFinalizer st.core) :
    CoreFinalizer
      (Protocol.NamedAdmission.on_block_with .alsoCarried S.E S.hc S.cfg st B).core := by
  have hc := process_core_finalizer S st B hco h
  dsimp only [Protocol.NamedAdmission.on_block_with, Protocol.NamedAdmission.admit_carried]
  split_ifs
  · exact rows_finalizer S.hc _ B.attestations hc
  · exact hc

private theorem gf_finalizer (E : Env V) (st : Protocol.Store V) (u : GoldfishVote V)
    (h : CoreFinalizer st) : CoreFinalizer (Protocol.on_goldfish_vote_checked E st u) := by
  have f := gf_fields E st u
  exact unchanged f.1 f.2.1 f.2.2.1 (by rw [f.2.2.2]) h

private theorem clock_finalizer (E : Env V) (st : Protocol.NamedStore V) (t : Time)
    (h : CoreFinalizer st.core) : CoreFinalizer (Protocol.NamedStore.setClock E st t).core := h

private theorem confirmation_finalizer (gc : Protocol.GradeContract V) (S : Setup V)
    (st : Protocol.NamedStore V) (s : Slot) (h : CoreFinalizer st.core) :
    CoreFinalizer (Protocol.NamedDuties.update_confirmation_with gc S.E S.hc st s).core := h

private theorem propose_finalizer (gc : Protocol.GradeContract V) (S : Setup V)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (hco : Proofs.NamedStore.Coherent S.E S.cfg st) (h : CoreFinalizer st.core) :
    CoreFinalizer (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg nd st).1.core := by
  unfold Protocol.NamedDuties.propose_block_with
  split
  · exact h
  · exact block_finalizer S st _ hco h

private theorem vote_finalizer (gc : Protocol.GradeContract V) (S : Setup V)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V) (h : CoreFinalizer st.core) :
    CoreFinalizer (Protocol.NamedDuties.goldfish_vote_with gc S.E S.hc nd st).1.core := by
  dsimp only [Protocol.NamedDuties.goldfish_vote_with, Protocol.goldfish_vote_with]
  split_ifs
  · exact gf_finalizer S.E st.core _ h
  · exact h

private theorem attest_finalizer (gc : Protocol.GradeContract V) (S : Setup V)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V) (record : Protocol.NamedRecord)
    (h : CoreFinalizer st.core) :
    CoreFinalizer (Protocol.NamedDuties.attest_with gc S.E S.hc nd st record).1.core :=
  row_finalizer S.hc st _ h

private theorem tick_finalizer (gc : Protocol.GradeContract V) (S : Setup V)
    (nd : Protocol.Node V) (st : Protocol.NamedStore V) (record : Protocol.NamedRecord)
    (t : Time) (hco : Proofs.NamedStore.Coherent S.E S.cfg st) (h : CoreFinalizer st.core) :
    CoreFinalizer (Protocol.NamedTick.tick gc S.E S.hc S.cfg nd st record t).1.core := by
  let s := S.E.slotOf t
  let st0 := Protocol.NamedStore.setClock S.E st t
  let st1 := if 0 < s ∧ t = Protocol.proposal_time S.E s ∧ S.E.proposer s = nd.val_index then
    (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg nd st0).1 else st0
  let st2 := if 0 < s ∧ t = Protocol.vote_time S.E s then
    (Protocol.NamedDuties.goldfish_vote_with gc S.E S.hc nd st1).1 else st1
  let st3 := if 0 < s ∧ t = Protocol.support_cutoff S.E s then
    Protocol.NamedDuties.update_confirmation_with gc S.E S.hc st2 (s - 1) else st2
  have h0 := clock_finalizer S.E st t h
  have hc0 := NamedStore.coherent_clock S.E S.cfg st t hco
  have h1 : CoreFinalizer st1.core := by dsimp [st1]; split_ifs
    <;> first | exact propose_finalizer gc S nd st0 hc0 h0 | exact h0
  have h2 : CoreFinalizer st2.core := by dsimp [st2]; split_ifs
    <;> first | exact vote_finalizer gc S nd st1 h1 | exact h1
  have h3 : CoreFinalizer st3.core := by
    by_cases hs : 0 < s ∧ t = Protocol.support_cutoff S.E s
    · simpa [st3, hs] using confirmation_finalizer gc S st2 (s - 1) h2
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
  · exact attest_finalizer gc S nd st3 record h3
  · exact h3

private theorem node_tick_finalizer (S : Setup V) (v : V) (n : NamedNodeState V) (t : Time)
    (hco : Proofs.NamedStore.Coherent S.E S.cfg n.st) (h : CoreFinalizer n.st.core) :
    CoreFinalizer (Execution.NamedNode.tick S v n t).1.st.core :=
  tick_finalizer (NamedProfile.gradeContract
    (DecoupledConsensusModel.Protocol.onPhaseTick S.E S.hc n.st.core.toHealing t n.cache)) S (S.node v)
    n.st n.record t hco h

private theorem node_process_finalizer (S : Setup V) (n : NamedNodeState V) (o : NamedObject V)
    (hco : Proofs.NamedStore.Coherent S.E S.cfg n.st) (h : CoreFinalizer n.st.core) :
    CoreFinalizer (Execution.NamedNode.process S n o).st.core := by
  cases o with
  | block B => exact block_finalizer S n.st B hco h
  | gfVote u => exact gf_finalizer S.E n.st.core u h
  | attest a => exact row_finalizer S.hc n.st a h

private theorem fold_finalizer (S : Setup V) (events : List (NamedEvent V)) (w : NamedWorld V)
    (hinv : ∀ v, Proofs.NamedConfirmationMembership.Invariant S.E S.cfg (w v).st ∧
      NamedTickRecord.Invariant (w v).record)
    (h : ∀ v, CoreFinalizer (w v).st.core) :
    ∀ v, CoreFinalizer (events.foldl (NamedWorld.step S) w v).st.core := by
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
            node_tick_finalizer S v (w v) t (hinv v).1.1.1 (h v)
        · simpa [NamedWorld.step, Function.update_of_ne hv] using h v
      | deliver u o t =>
        by_cases hv : v = u
        · subst u; simpa [NamedWorld.step] using
            node_process_finalizer S (w v) o (hinv v).1.1.1 (h v)
        · simpa [NamedWorld.step, Function.update_of_ne hv] using h v

private theorem named_finalizer (S : Setup V) (st : Protocol.NamedStore V)
    (hco : Proofs.NamedStore.Coherent S.E S.cfg st) (h : CoreFinalizer st.core) :
    ∃ D : NamedBlock V, D ∈ st.bodies ∧ (derive_named S.E S.cfg D).F = st.core.F ∧
      (derive_named S.E S.cfg D).h_F < st.core.h_max := by
  obtain ⟨raw, hraw, hF, hh⟩ := h
  rw [hco.1] at hraw
  obtain ⟨D, hD, rfl⟩ := Finset.mem_image.mp hraw
  rw [hco.2.2.2.2 D hD] at hF hh
  exact ⟨D, hD, hF, hh⟩

theorem finalization_carrier_stateBefore (S : Setup V) (rho : NamedRun V) (i : Nat) (v : V) :
    ∃ D : NamedBlock V, D ∈ (NamedRun.stateBefore S rho i v).st.bodies ∧
      (derive_named S.E S.cfg D).F = (NamedRun.stateBefore S rho i v).st.core.F ∧
      (derive_named S.E S.cfg D).h_F < (NamedRun.stateBefore S rho i v).st.core.h_max :=
  named_finalizer S _ (Proofs.NamedRuntime.stateBefore_invariants S rho i v).1.1.1
    (fold_finalizer S (rho.events.take i) NamedWorld.init
      (fun _ => NamedNode.initial_invariants S) (fun _ => initial_core_finalizer) v)

theorem finalization_carrier_stateBeforeTime (S : Setup V) (rho : NamedRun V) (t : Time) (v : V) :
    ∃ D : NamedBlock V, D ∈ (NamedRun.stateBeforeTime S rho t v).st.bodies ∧
      (derive_named S.E S.cfg D).F = (NamedRun.stateBeforeTime S rho t v).st.core.F ∧
      (derive_named S.E S.cfg D).h_F < (NamedRun.stateBeforeTime S rho t v).st.core.h_max :=
  named_finalizer S _ (Proofs.NamedRuntime.stateBeforeTime_invariants S rho t v).1.1.1
    (fold_finalizer S _ NamedWorld.init (fun _ => NamedNode.initial_invariants S)
      (fun _ => initial_core_finalizer) v)

theorem finalization_carrier_readAt (S : Setup V) (rho : NamedRun V) (t : Time) (v : V) :
    ∃ D : NamedBlock V, D ∈ (NamedRun.readAt S rho t v).st.bodies ∧
      (derive_named S.E S.cfg D).F = (NamedRun.readAt S rho t v).st.core.F ∧
      (derive_named S.E S.cfg D).h_F < (NamedRun.readAt S rho t v).st.core.h_max :=
  named_finalizer S _ (Proofs.NamedRuntime.readAt_invariants S rho t v).1.1.1
    (fold_finalizer S _ NamedWorld.init (fun _ => NamedNode.initial_invariants S)
      (fun _ => initial_core_finalizer) v)


/-- Two named run blocks are root-injective on their erased ancestors.

This is the named-vocabulary restatement of the earlier tree's
`RootInjectiveOnAncestors` consequence of `RootCollisionFree.root_injective`.
The erased ancestor witnesses are lifted to named ancestors before the
run-wide collision-free hypothesis is applied. -/
theorem rootInjectiveOnAncestors_of_collisionFree
    (S : Setup V) (rho : NamedRun V) (hroot : NamedRootCollisionFree S rho)
    (A B : NamedBlock V) (hA : NamedRun.blockInRun S rho A)
    (hB : NamedRun.blockInRun S rho B) :
    Execution.RootInjectiveOnAncestors A.erase B.erase := by
  intro X Y hX hY hroots
  obtain ⟨Z, hZmem, hXZ⟩ := hX
  obtain ⟨W, hWmem, hYW⟩ := hY
  simp only [Finset.mem_insert, Finset.mem_singleton] at hZmem hWmem
  rcases hZmem with hZmem | hZmem <;> subst hZmem <;>
      rcases hWmem with hWmem | hWmem <;> subst hWmem
  · obtain ⟨X', hX'anc, hX'erase⟩ := Proofs.NamedAncestry.erased_ancestor_lift A hXZ
    obtain ⟨Y', hY'anc, hY'erase⟩ := Proofs.NamedAncestry.erased_ancestor_lift A hYW
    have hXr : X'.root = X.root := by
      rw [← Proofs.NamedWire.erase_root X', hX'erase]
    have hYr : Y'.root = Y.root := by
      rw [← Proofs.NamedWire.erase_root Y', hY'erase]
    have hEq := hroot.root_injective A B hA hB X' Y'
      (Or.inl hX'anc) (Or.inl hY'anc) (hXr.trans (hroots.trans hYr.symm))
    rw [← hX'erase, ← hY'erase, hEq]
  · obtain ⟨X', hX'anc, hX'erase⟩ := Proofs.NamedAncestry.erased_ancestor_lift A hXZ
    obtain ⟨Y', hY'anc, hY'erase⟩ := Proofs.NamedAncestry.erased_ancestor_lift B hYW
    have hXr : X'.root = X.root := by
      rw [← Proofs.NamedWire.erase_root X', hX'erase]
    have hYr : Y'.root = Y.root := by
      rw [← Proofs.NamedWire.erase_root Y', hY'erase]
    have hEq := hroot.root_injective A B hA hB X' Y'
      (Or.inl hX'anc) (Or.inr hY'anc) (hXr.trans (hroots.trans hYr.symm))
    rw [← hX'erase, ← hY'erase, hEq]
  · obtain ⟨X', hX'anc, hX'erase⟩ := Proofs.NamedAncestry.erased_ancestor_lift B hXZ
    obtain ⟨Y', hY'anc, hY'erase⟩ := Proofs.NamedAncestry.erased_ancestor_lift A hYW
    have hXr : X'.root = X.root := by
      rw [← Proofs.NamedWire.erase_root X', hX'erase]
    have hYr : Y'.root = Y.root := by
      rw [← Proofs.NamedWire.erase_root Y', hY'erase]
    have hEq := hroot.root_injective A B hA hB X' Y'
      (Or.inr hX'anc) (Or.inl hY'anc) (hXr.trans (hroots.trans hYr.symm))
    rw [← hX'erase, ← hY'erase, hEq]
  · obtain ⟨X', hX'anc, hX'erase⟩ := Proofs.NamedAncestry.erased_ancestor_lift B hXZ
    obtain ⟨Y', hY'anc, hY'erase⟩ := Proofs.NamedAncestry.erased_ancestor_lift B hYW
    have hXr : X'.root = X.root := by
      rw [← Proofs.NamedWire.erase_root X', hX'erase]
    have hYr : Y'.root = Y.root := by
      rw [← Proofs.NamedWire.erase_root Y', hY'erase]
    have hEq := hroot.root_injective A B hA hB X' Y'
      (Or.inr hX'anc) (Or.inr hY'anc) (hXr.trans (hroots.trans hYr.symm))
    rw [← hX'erase, ← hY'erase, hEq]

end DecoupledConsensusModel.Proofs.NamedFinalizationBridge

end
