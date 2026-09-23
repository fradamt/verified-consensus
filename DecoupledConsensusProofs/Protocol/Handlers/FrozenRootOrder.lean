module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Handlers.JustificationCarrier
public import DecoupledConsensusProofs.Protocol.Handlers.StoreRoots
public import DecoupledConsensusProofs.Protocol.Handlers.Invariants
public import DecoupledConsensusProofs.Protocol.Handlers.Invariants2
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.Records
public import DecoupledConsensusProofs.Execution.Runtime
public import DecoupledConsensusInternal.Definitions.NamedStableChainOutage

@[expose] public section


namespace DecoupledConsensusModel.Proofs.NamedOutageClosure
open Execution Internal.NamedStableChainOutage
open DecoupledConsensusModel.Protocol Protocol
variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## 1. `F ⪯ J` at every named prefix state -/

/-- The generic `on_block_using` transition preserves `F ⪯ J`. Only its final
branch touches these fields, through `update_finality`; the intervening
carried-vote fold leaves them untouched. -/
theorem frozen_on_block_using_preceq (E : Env V) (st : Protocol.Store V) (B : Block V)
    (buildState : ChainState V → ChainState V)
    (h : Block.Preceq st.F st.J) :
    Block.Preceq (Protocol.on_block_using E st B buildState).F
      (Protocol.on_block_using E st B buildState).J := by
  simp only [Protocol.on_block_using]
  split_ifs <;> first
    | exact h
    | (apply update_finality_preceq
       have hCE := coreEq_foldl_on_goldfish_vote_checked E B.gf_votes
         ({ st with
             σ := fun C => if C = B then buildState (st.σ B.parent) else st.σ C
             T := insert B st.T
             timestamp_block := fun C =>
               if C = B then some (st.t : Stamp) else st.timestamp_block C } : Protocol.Store V)
       rw [hCE.F_eq, hCE.J_eq]
       exact h)

/-- Named block-core processing preserves `F ⪯ J`: unchanged when the parent
is not held, and routed through `frozen_on_block_using_preceq` under the
carried-round guard otherwise. -/
theorem frozen_process_block_core_preceq (E : Env V) (hc : Protocol.HealConfig)
    (cfg : Protocol.HeightConfig) (st : Protocol.NamedStore V) (B : NamedBlock V)
    (h : Block.Preceq st.core.F st.core.J) :
    Block.Preceq (Protocol.NamedStore.process_block_core E hc cfg st B).core.F
      (Protocol.NamedStore.process_block_core E hc cfg st B).core.J := by
  simp only [Protocol.NamedStore.process_block_core]
  split_ifs <;> first
    | exact h
    | (rw [NamedStore.commit_core]
       simp only [Protocol.on_block_checked_using]
       split_ifs <;> first
         | exact frozen_on_block_using_preceq E st.core B.erase _ h
         | exact h)

/-- Row admission (`on_sg_vote`) never touches `F`/`J`. -/
theorem frozen_admit_row_preceq (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (row : NamedAttestation V) (h : Block.Preceq st.core.F st.core.J) :
    Block.Preceq (Protocol.NamedAdmission.admit_row hc st row).core.F
      (Protocol.NamedAdmission.admit_row hc st row).core.J := by
  simp only [Protocol.NamedAdmission.admit_row]
  have hCE := coreEq_on_sg_vote hc st.core row.erase
  split_ifs <;> (rw [hCE.F_eq, hCE.J_eq]; exact h)

theorem frozen_admit_rows_preceq (hc : Protocol.HealConfig) (st : Protocol.NamedStore V)
    (rows : List (NamedAttestation V)) (h : Block.Preceq st.core.F st.core.J) :
    Block.Preceq (Protocol.NamedAdmission.admit_rows hc st rows).core.F
      (Protocol.NamedAdmission.admit_rows hc st rows).core.J := by
  unfold Protocol.NamedAdmission.admit_rows
  induction rows generalizing st with
  | nil => exact h
  | cons row rows ih => exact ih _ (frozen_admit_row_preceq hc st row h)

theorem frozen_admit_carried_preceq (admission : Protocol.CarriedAdmission)
    (hc : Protocol.HealConfig) (before after : Protocol.NamedStore V) (B : NamedBlock V)
    (h : Block.Preceq after.core.F after.core.J) :
    Block.Preceq (Protocol.NamedAdmission.admit_carried admission hc before after B).core.F
      (Protocol.NamedAdmission.admit_carried admission hc before after B).core.J := by
  cases admission with
  | alsoCarried =>
    unfold Protocol.NamedAdmission.admit_carried
    split_ifs
    · exact frozen_admit_rows_preceq hc after B.attestations h
    · exact h

theorem frozen_on_block_with_preceq (admission : Protocol.CarriedAdmission)
    (E : Env V) (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig)
    (st : Protocol.NamedStore V) (B : NamedBlock V) (h : Block.Preceq st.core.F st.core.J) :
    Block.Preceq (Protocol.NamedAdmission.on_block_with admission E hc cfg st B).core.F
      (Protocol.NamedAdmission.on_block_with admission E hc cfg st B).core.J :=
  frozen_admit_carried_preceq admission hc st _ B (frozen_process_block_core_preceq E hc cfg st B h)

/-- `goldfish_vote_with` (any contract) never touches `F`/`J`: it either calls
`on_goldfish_vote_checked` or leaves the store unchanged. -/
theorem frozen_goldfish_vote_with_preceq (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (h : Block.Preceq st.core.F st.core.J) :
    Block.Preceq (Protocol.NamedDuties.goldfish_vote_with gc E hc nd st).1.core.F
      (Protocol.NamedDuties.goldfish_vote_with gc E hc nd st).1.core.J := by
  show Block.Preceq (Protocol.goldfish_vote_with gc E hc nd st.core).1.F
    (Protocol.goldfish_vote_with gc E hc nd st.core).1.J
  simp only [Protocol.goldfish_vote_with]
  split_ifs <;> first
    | exact h
    | (rw [(coreEq_on_goldfish_vote_checked E st.core _).F_eq,
        (coreEq_on_goldfish_vote_checked E st.core _).J_eq]
       exact h)

/-- `update_confirmation_with` (any contract) writes only the confirmation
fields. -/
theorem frozen_update_confirmation_with_preceq (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (st : Protocol.NamedStore V) (s : Slot)
    (h : Block.Preceq st.core.F st.core.J) :
    Block.Preceq (Protocol.NamedDuties.update_confirmation_with gc E hc st s).core.F
      (Protocol.NamedDuties.update_confirmation_with gc E hc st s).core.J :=
  h

/-- `attest_with` admits exactly one row. -/
theorem frozen_attest_with_preceq (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (nd : Protocol.Node V) (st : Protocol.NamedStore V)
    (record : Protocol.NamedRecord) (h : Block.Preceq st.core.F st.core.J) :
    Block.Preceq (Protocol.NamedDuties.attest_with gc E hc nd st record).1.core.F
      (Protocol.NamedDuties.attest_with gc E hc nd st record).1.core.J := by
  unfold Protocol.NamedDuties.attest_with
  exact frozen_admit_row_preceq hc st _ h

/-- `propose_block_with` either leaves the store unchanged or admits the
proposed block. -/
theorem frozen_propose_block_with_preceq (gc : Protocol.GradeContract V) (E : Env V)
    (hc : Protocol.HealConfig) (cfg : Protocol.HeightConfig) (nd : Protocol.Node V)
    (st : Protocol.NamedStore V) (h : Block.Preceq st.core.F st.core.J) :
    Block.Preceq (Protocol.NamedDuties.propose_block_with gc E hc cfg nd st).1.core.F
      (Protocol.NamedDuties.propose_block_with gc E hc cfg nd st).1.core.J := by
  unfold Protocol.NamedDuties.propose_block_with
  split
  · exact h
  · exact frozen_on_block_with_preceq .alsoCarried E hc cfg st _ h

/-- **`F ⪯ J` through one named tick.** Mirrors
`Proofs.NamedNode.confirmation_named_tick`'s exact duty sequencing, with the
membership invariant replaced by the order fact. -/
theorem frozen_named_tick_preceq (S : Setup V) (cache : DecoupledConsensusModel.Protocol.Cache V)
    (v : V) (st : Protocol.NamedStore V) (record : Protocol.NamedRecord) (t : Time)
    (h : Block.Preceq st.core.F st.core.J) :
    Block.Preceq
      (Protocol.NamedTick.tick (DecoupledConsensusModel.Protocol.frameContract cache)
        S.E S.hc S.cfg (S.node v) st record t).1.core.F
      (Protocol.NamedTick.tick (DecoupledConsensusModel.Protocol.frameContract cache)
        S.E S.hc S.cfg (S.node v) st record t).1.core.J := by
  let gc := DecoupledConsensusModel.Protocol.frameContract cache
  let s := S.E.slotOf t
  let st0 := Protocol.NamedStore.setClock S.E st t
  let st1 := if 0 < s ∧ t = Protocol.proposal_time S.E s ∧
      S.E.proposer s = (S.node v).val_index then
    (Protocol.NamedDuties.propose_block_with gc S.E S.hc S.cfg (S.node v) st0).1 else st0
  let st2 := if 0 < s ∧ t = Protocol.vote_time S.E s then
    (Protocol.NamedDuties.goldfish_vote_with gc S.E S.hc (S.node v) st1).1 else st1
  let st3 := if 0 < s ∧ t = Protocol.support_cutoff S.E s then
    Protocol.NamedDuties.update_confirmation_with gc S.E S.hc st2 (s - 1) else st2
  have h0 : Block.Preceq st0.core.F st0.core.J := h
  have h1 : Block.Preceq st1.core.F st1.core.J := by
    dsimp only [st1]
    split_ifs
    · exact frozen_propose_block_with_preceq gc S.E S.hc S.cfg (S.node v) st0 h0
    · exact h0
  have h2 : Block.Preceq st2.core.F st2.core.J := by
    dsimp only [st2]
    split_ifs
    · exact frozen_goldfish_vote_with_preceq gc S.E S.hc (S.node v) st1 h1
    · exact h1
  have h3 : Block.Preceq st3.core.F st3.core.J := by
    dsimp only [st3]
    split_ifs
    · exact frozen_update_confirmation_with_preceq gc S.E S.hc st2 (s - 1) h2
    · exact h2
  have hstage : (Protocol.NamedTick.tick gc S.E S.hc S.cfg (S.node v) st record t).1 =
      if t = S.hc.a S.E.Δ (S.hc.round_of st3.core.s) ∧
          (S.node v).awake (S.hc.round_of st3.core.s) = true then
        (Protocol.NamedDuties.attest_with gc S.E S.hc (S.node v) st3 record).1
      else st3 := by
    rw [NamedTick.tick_computed_duties]
    dsimp only
    rw [apply_ite (fun out : Protocol.NamedStore V × Protocol.NamedRecord ×
      List (NamedObject V) => out.1)]
  show Block.Preceq
    (Protocol.NamedTick.tick gc S.E S.hc S.cfg (S.node v) st record t).1.core.F
    (Protocol.NamedTick.tick gc S.E S.hc S.cfg (S.node v) st record t).1.core.J
  rw [hstage]
  split_ifs
  · exact frozen_attest_with_preceq gc S.E S.hc (S.node v) st3 record h3
  · exact h3

theorem frozen_tick_preceq (S : Setup V) (v : V) (n : NamedNodeState V) (t : Time)
    (h : Block.Preceq n.st.core.F n.st.core.J) :
    Block.Preceq (NamedNode.tick S v n t).1.st.core.F (NamedNode.tick S v n t).1.st.core.J :=
  frozen_named_tick_preceq S _ v n.st n.record t h

/-- **`F ⪯ J` through one named receipt.** The three object cases: block
admission, a bare goldfish vote (never touches `F`/`J`), and row admission. -/
theorem frozen_process_preceq (S : Setup V) (n : NamedNodeState V) (o : NamedObject V)
    (h : Block.Preceq n.st.core.F n.st.core.J) :
    Block.Preceq (NamedNode.process S n o).st.core.F (NamedNode.process S n o).st.core.J := by
  show Block.Preceq (NamedReceipt.process S n.st o).core.F
    (NamedReceipt.process S n.st o).core.J
  cases o with
  | block B => exact frozen_on_block_with_preceq .alsoCarried S.E S.hc S.cfg n.st B h
  | gfVote u =>
    show Block.Preceq (Protocol.on_goldfish_vote_checked S.E n.st.core u).F
      (Protocol.on_goldfish_vote_checked S.E n.st.core u).J
    have hCE := coreEq_on_goldfish_vote_checked S.E n.st.core u
    rw [hCE.F_eq, hCE.J_eq]
    exact h
  | attest a => exact frozen_admit_row_preceq S.hc n.st a h

private theorem frozen_step (S : Setup V) (w : NamedWorld V) (e : NamedEvent V)
    (h : ∀ v, Block.Preceq (w v).st.core.F (w v).st.core.J) :
    ∀ v, Block.Preceq (NamedWorld.step S w e v).st.core.F (NamedWorld.step S w e v).st.core.J := by
  intro v
  by_cases hv : v = e.node
  · cases e with
    | tick u t =>
      change v = u at hv
      subst v
      rw [Proofs.NamedRuntime.step_tick]
      exact frozen_tick_preceq S u (w u) t (h u)
    | deliver u o t =>
      change v = u at hv
      subst v
      rw [Proofs.NamedRuntime.step_deliver]
      exact frozen_process_preceq S (w u) o (h u)
  · rw [Proofs.NamedRuntime.step_other S w e v hv]
    exact h v

private theorem frozen_fold (S : Setup V) (events : List (NamedEvent V)) :
    ∀ w : NamedWorld V, (∀ v, Block.Preceq (w v).st.core.F (w v).st.core.J) →
      ∀ v, Block.Preceq (events.foldl (NamedWorld.step S) w v).st.core.F
        (events.foldl (NamedWorld.step S) w v).st.core.J := by
  induction events with
  | nil => intro w h; exact h
  | cons e events ih => intro w h; exact ih _ (frozen_step S w e h)

theorem frozen_initial (S : Setup V) (v : V) :
    Block.Preceq (NamedWorld.init v : NamedNodeState V).st.core.F
      (NamedWorld.init v : NamedNodeState V).st.core.J :=
  Block.preceq_self _


/-- **`Σ.F ⪯ Σ.J` at every named strict-read prefix state.** The named twin of
P6 (`Invariants2.finalizedPrecedesJustifiedInvariant`), proved directly over
the event fold rather than by resurrecting `ReachableStore`. -/
theorem stateBeforeTime_F_preceq_J (S : Setup V) (rho : NamedRun V) (t : Time) (v : V) :
    Block.Preceq (NamedRun.stateBeforeTime S rho t v).st.core.F
      (NamedRun.stateBeforeTime S rho t v).st.core.J :=
  frozen_fold S _ NamedWorld.init (frozen_initial S) v

#print axioms stateBeforeTime_F_preceq_J

/-! ## 2. The justified-root cascade

When the FG root is the justified checkpoint, it is a filtered-tree member:
the named twin of `FrameStoreRoot.fgRoot_mem_filtered_of_state_facts`'s
justified branch. -/

/-- The justified checkpoint is viable: `NamedJustificationCarrier` supplies a
processed named witness whose derived justification pair matches the store's,
`Protocol.ChainOrder` on that witness puts its height at or past `h_j`, and
`Proofs.NamedStore.Coherent`'s `DerivedView`/`TreeView` transports both facts to the
store's own `σ`/`T`. -/
theorem justifiedRoot_viable_of_state (S : Setup V) (rho : NamedRun V) (t : Time) (v : V)
    (hgate : (NamedRun.stateBeforeTime S rho t v).st.core.h_max =
      (NamedRun.stateBeforeTime S rho t v).st.core.h_j + 1) :
    (NamedRun.stateBeforeTime S rho t v).st.core.J ∈
      Protocol.V_tree (NamedRun.stateBeforeTime S rho t v).st.core.toHealing.toFG := by
  set st := (NamedRun.stateBeforeTime S rho t v).st with hst
  have hinv := Proofs.NamedRuntime.stateBeforeTime_invariants S rho t v
  have hcoh : Proofs.NamedStore.Coherent S.E S.cfg st := hinv.1.1.1
  have hroots : Proofs.NamedStoreRoots.RootsInTree st := hinv.1.1.2
  obtain ⟨D, hD, hDJ, hDhj⟩ :=
    NamedJustificationCarrier.justification_carrier_stateBeforeTime S rho t v
  have hDorder := Proofs.NamedStoreRoots.chainOrder_derive_named S.E S.cfg D
  have hDanchors := Proofs.NamedStoreRoots.derive_named_anchors_preceq S.E S.cfg D
  have hDraw : D.erase ∈ st.core.T := by
    rw [hcoh.1]; exact Finset.mem_image_of_mem NamedBlock.erase hD
  have hDheight : st.core.h_max - 1 ≤ (st.core.σ D.erase).h := by
    rw [hcoh.2.2.2.2 D hD]
    have hlt : st.core.h_j < (derive_named S.E S.cfg D).h := by
      rw [← hDhj]; exact hDorder.justified_below_height
    have hgate' : st.core.h_max = st.core.h_j + 1 := hgate
    rw [hgate', Nat.add_sub_cancel]
    exact hlt.le
  have hJD : Block.Preceq st.core.J D.erase := by rw [← hDJ]; exact hDanchors.2
  show st.core.J ∈ Protocol.viable_tree st.core.σ st.core.F st.core.h_max st.core.T
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_filter.mpr ⟨hroots.2, stateBeforeTime_F_preceq_J S rho t v⟩, ?_⟩
  simpa only [Protocol.viable, decide_eq_true_eq] using
    (⟨D.erase, hDraw, hJD, hDheight⟩ :
      ∃ W ∈ st.core.T, Block.Preceq st.core.J W ∧ st.core.h_max - 1 ≤ (st.core.σ W).h)

/-- **The justified-root cascade.** Under `h_max = h_j + 1`, the FG root
(`= Σ.J`) is a member of the reader's own filtered candidate tree. -/
theorem justifiedRoot_mem_filtered (S : Setup V) (rho : NamedRun V) (t : Time) (v : V)
    (hgate : (NamedRun.stateBeforeTime S rho t v).st.core.h_max =
      (NamedRun.stateBeforeTime S rho t v).st.core.h_j + 1) :
    Protocol.get_fg_root
        (NamedRun.stateBeforeTime S rho t v).st.core.toHealing.toFG ∈
      Protocol.get_filtered_block_tree
        (NamedRun.stateBeforeTime S rho t v).st.core.toHealing.toFG := by
  have hroot : Protocol.get_fg_root
      (NamedRun.stateBeforeTime S rho t v).st.core.toHealing.toFG =
      (NamedRun.stateBeforeTime S rho t v).st.core.J := by
    show (if (NamedRun.stateBeforeTime S rho t v).st.core.h_max =
        (NamedRun.stateBeforeTime S rho t v).st.core.h_j + 1 then
        (NamedRun.stateBeforeTime S rho t v).st.core.J else
        (NamedRun.stateBeforeTime S rho t v).st.core.F) =
      (NamedRun.stateBeforeTime S rho t v).st.core.J
    rw [if_pos hgate]
  exact Proofs.Records.mem_filtered_of_mem_V_tree
    (by rw [hroot]; exact justifiedRoot_viable_of_state S rho t v hgate)
    (Block.preceq_self _)

#print axioms justifiedRoot_mem_filtered

end DecoupledConsensusModel.Proofs.NamedOutageClosure

end
