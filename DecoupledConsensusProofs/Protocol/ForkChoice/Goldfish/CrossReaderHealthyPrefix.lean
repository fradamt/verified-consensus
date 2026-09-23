module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.RelativeCrossReader

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Healthy-prefix cross-reader finality and body open

The post-GST cross-reader producers in `RelativeCrossReaderRun` use an
`Admissible` witness and a GST cutoff. This additive surface keeps the same
conclusions but uses the named core and the unwindowed healthy-prefix delivery
contract. The stable round can therefore remain before GST when it is before
the healthy-prefix boundary.

The two source signatures are quoted before their healthy-prefix twins.

```lean
theorem finalized_preceq_of_evidence_delivered
    (S: Setup V) {rho: NamedRun V} (adm: Admissible S rho)
    (hsb: SlashableBound S rho) {source target: V}
    (hsource: source ∈ rho.honest) (htarget: target ∈ rho.honest)
    {read out: Time} (hpost: S.E.t_GST ≤ read)
    (hhop: read + S.E.Δ = out) (hhor: out ≤ rho.horizon):
    Block.Preceq
      (NamedRun.stateBeforeTime S rho read source).st.core.F
      (NamedRun.stateBeforeTime S rho out target).st.core.F

theorem crossReaderBodyReadyGuard_of_finalizedBelow
    (S: Setup V) {rho: NamedRun V} (core: NamedAdmissibleCore S rho)
    {r: Round} (hr: 0 < r)
    (hgst: S.E.t_GST ≤ early S.E S.hc r.g2)
    (horizon: domain S.E S.hc r.g0 ≤ rho.horizon)
    {source target: V} (hsource: source ∈ rho.honest)
    (htarget: target ∈ rho.honest) {B: Block V}
    (hbelow: CrossReaderFinalizedBelow S rho r source target B):
    CrossReaderBodyReadyGuard S rho r source target B
```

The healthy-prefix map is direct: `adm` becomes `core`, `hpost` becomes the
bound `out ≤ cut`, and the post-GST head-read constructor becomes
`NamedHealthyHeadReady.healthy_head_body_at_read` with source cut `read` and
target read `out`. The horizon hypothesis remains the same.
-/

namespace DecoupledConsensusModel.Proofs.HealingSurface

open Internal Execution Internal.HealingSurface
  Internal.NamedOutageEntry Internal.NamedStableChainOutage
open Internal.PhaseGrades
open DecoupledConsensusModel.Protocol DecoupledConsensusModel.Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-! The accepted-carrier finality step is private in the post-GST module. Keep
the same local step here so the new public producer can reuse the named-core
route without changing that module's declarations. -/

omit [Fintype V] in
private theorem healthy_named_trans {A B C : NamedBlock V}
    (hAB : NamedBlock.Preceq A B) (hBC : NamedBlock.Preceq B C) :
    NamedBlock.Preceq A C := by
  induction C with
  | genesis =>
      simp only [NamedBlock.Preceq, NamedBlock.preceq,
        decide_eq_true_eq] at hBC
      subst B
      exact hAB
  | node parent slot root votes support rows proposer ih =>
      simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hBC
      rcases hBC with rfl | hparent
      · exact hAB
      · exact Proofs.NamedAncestry.named_extend slot root votes support rows proposer
          (ih hparent)

private theorem healthy_finalized_justification_ancestor
    (E : Env V) (cfg : Protocol.HeightConfig) :
    ∀ C : NamedBlock V, ∃ D : NamedBlock V,
      NamedBlock.Preceq D C ∧
      (C = .genesis ∨ NamedBlock.Preceq D C.parent) ∧
      (Protocol.derive_named E cfg D).J =
        (Protocol.derive_named E cfg C).F ∧
      (Protocol.derive_named E cfg D).h_j =
        (Protocol.derive_named E cfg C).h_F := by
  intro C
  induction C with
  | genesis =>
      exact ⟨.genesis, Proofs.NamedAncestry.named_self _, Or.inl rfl, rfl, rfl⟩
  | node parent slot root votes support rows proposer ih =>
      let C : NamedBlock V :=
        .node parent slot root votes support rows proposer
      let folded := Protocol.fold_rows
        (Protocol.TimeoutBinding.targeted V)
        (Protocol.derive_named E cfg parent) C.erase C.attestations
      have hstate : Protocol.derive_named E cfg C =
          Protocol.process_height_events E cfg folded := rfl
      have hfields := NamedDerivationGeometry.fold_context_fields
        (Protocol.TimeoutBinding.targeted V) C.attestations
        { Protocol.derive_named E cfg parent with s := C.erase.slot }
      have hfoldJ : folded.J =
          (Protocol.derive_named E cfg parent).J := hfields.2.2.2.1
      have hfoldHj : folded.h_j =
          (Protocol.derive_named E cfg parent).h_j := hfields.2.2.2.2.1
      have hfoldF : folded.F =
          (Protocol.derive_named E cfg parent).F := hfields.2.2.2.2.2.1
      have hfoldHf : folded.h_F =
          (Protocol.derive_named E cfg parent).h_F :=
        hfields.2.2.2.2.2.2
      have hafter : ∃ D : NamedBlock V,
          NamedBlock.Preceq D C ∧ NamedBlock.Preceq D parent ∧
          (Protocol.derive_named E cfg D).J =
            (Protocol.afterFin E folded).F ∧
          (Protocol.derive_named E cfg D).h_j =
            (Protocol.afterFin E folded).h_F := by
        rw [Protocol.afterFin_F, Protocol.afterFin_h_F]
        split_ifs
        · refine ⟨parent, ?_, Proofs.NamedAncestry.named_self parent, ?_, ?_⟩
          · exact Proofs.NamedAncestry.named_extend slot root votes support rows proposer
              (Proofs.NamedAncestry.named_self parent)
          · exact hfoldJ.symm
          · exact hfoldHj.symm
        · obtain ⟨D, hDC, -, hDJ, hDh⟩ := ih
          refine ⟨D, healthy_named_trans hDC ?_, hDC, ?_, ?_⟩
          · exact Proofs.NamedAncestry.named_extend slot root votes support rows proposer
              (Proofs.NamedAncestry.named_self parent)
          · exact hDJ.trans hfoldF.symm
          · exact hDh.trans hfoldHf.symm
      rw [hstate, Protocol.process_height_events_eq]
      split_ifs <;>
        exact ⟨hafter.choose, hafter.choose_spec.1,
          Or.inr hafter.choose_spec.2.1, hafter.choose_spec.2.2.1,
          hafter.choose_spec.2.2.2⟩

private theorem healthy_gf_fields (E : Env V) (st : Protocol.Store V)
    (u : GoldfishVote V) :
    let next := Protocol.on_goldfish_vote_checked E st u
    next.T = st.T ∧ next.σ = st.σ ∧ next.F = st.F ∧
      next.J = st.J ∧ next.h_j = st.h_j ∧ next.h_max = st.h_max := by
  dsimp only [Protocol.on_goldfish_vote_checked, Protocol.on_goldfish_vote]
  split_ifs <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

private theorem healthy_gf_fold_fields (E : Env V) (st : Protocol.Store V)
    (votes : List (GoldfishVote V)) :
    let next := votes.foldl (Protocol.on_goldfish_vote_checked E) st
    next.T = st.T ∧ next.σ = st.σ ∧ next.F = st.F ∧
      next.J = st.J ∧ next.h_j = st.h_j ∧ next.h_max = st.h_max := by
  induction votes generalizing st with
  | nil => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | cons u votes ih =>
      have rest := ih (Protocol.on_goldfish_vote_checked E st u)
      have one := healthy_gf_fields E st u
      exact ⟨rest.1.trans one.1, rest.2.1.trans one.2.1,
        rest.2.2.1.trans one.2.2.1,
        rest.2.2.2.1.trans one.2.2.2.1,
        rest.2.2.2.2.1.trans one.2.2.2.2.1,
        rest.2.2.2.2.2.trans one.2.2.2.2.2⟩

private theorem healthy_absorb_finality_step (U afterJ : Protocol.Store V)
    (sigma : Protocol.ChainState V)
    (hF : afterJ.F = U.F) (hsigma : afterJ.σ = U.σ)
    (hT : afterJ.T = U.T)
    (hmax : afterJ.h_max = max U.h_max sigma.h)
    (hnot : ¬ Block.Preceq sigma.F U.F)
    (hviable : sigma.F ∈ Protocol.viable_tree U.σ U.F
      (max U.h_max sigma.h) U.T)
    (hJ : Block.Preceq sigma.F afterJ.J) :
    Block.Preceq sigma.F
      (if Block.prec afterJ.F sigma.F &&
          Block.preceq sigma.F afterJ.J &&
          decide (sigma.F ∈ Protocol.viable_tree afterJ.σ afterJ.F
            afterJ.h_max afterJ.T) then
        ({ afterJ with F := sigma.F } : Protocol.Store V)
      else afterJ).F := by
  have hUF : Block.Preceq U.F sigma.F :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp hviable).1).2
  have hne : U.F ≠ sigma.F := by
    intro heq
    apply hnot
    rw [← heq]
    exact Block.preceq_self _
  have hprec : Block.prec U.F sigma.F = true := by
    change (!decide (U.F = sigma.F) && Block.preceq U.F sigma.F) = true
    rw [show decide (U.F = sigma.F) = false by simp [hne]]
    simpa only [Bool.not_false, Bool.true_and] using hUF
  have hguard :
      (Block.prec afterJ.F sigma.F &&
        Block.preceq sigma.F afterJ.J &&
        decide (sigma.F ∈ Protocol.viable_tree afterJ.σ afterJ.F
          afterJ.h_max afterJ.T)) = true := by
    rw [hF, hsigma, hT, hmax]
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    exact ⟨⟨hprec, hJ⟩, hviable⟩
  rw [if_pos hguard]
  exact Block.preceq_self _

private theorem healthy_fresh_receipt_absorbs_finality
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    (hsb : Internal.NamedOutageEntry.SlashableBound S rho) {i : Nat} {target : V}
    (htarget : target ∈ rho.honest) (B : NamedBlock V)
    (hBscope : NamedRun.blockInRun S rho B)
    (before : Protocol.NamedStore V)
    (hcall : Execution.NamedReceiptCalls.blockCallAt
      S rho i target B before)
    (hnew : B.erase ∉ before.core.T)
    (hpost : B.erase ∈
      (Execution.NamedReceiptCalls.postCore S before B).core.T)
    (hfloor : Block.Preceq
      (NamedRun.stateBefore S rho i target).st.core.F
      (Protocol.derive_named S.E S.cfg B).F) :
    Block.Preceq (Protocol.derive_named S.E S.cfg B).F
      (Execution.NamedReceiptCalls.postCore S before B).core.F := by
  open Execution.NamedReceiptCalls in
  let sigma := Protocol.derive_named S.E S.cfg B
  rcases healthy_finalized_justification_ancestor S.E S.cfg B with
    ⟨A, hAB, hAcase, hAJ, hAh⟩
  rcases hAcase with hgen | hAparent
  · subst B
    change Block.Preceq Block.genesis _
    exact Protocol.preceq_genesis _
  · have hco : Proofs.NamedStore.Coherent S.E S.cfg before :=
      (Proofs.NamedReceiptCallsBase.block_call_before_invariant S rho hcall).1.1
    have hparent : B.parent ∈ before.bodies := by
      by_contra hn
      have hsame :
          (Execution.NamedReceiptCalls.postCore S before B).core =
            before.core := by
        simp only [Execution.NamedReceiptCalls.postCore,
          Protocol.NamedStore.process_block_core, if_pos hn]
      exact hnew (hsame ▸ hpost)
    have hAheld : A ∈ before.bodies :=
      NamedOutageHistory.ViabilityHistoryTime.ancestor_body_mem
        hco.2.2.1 hparent hAparent
    have hinputF : before.core.F =
        (NamedRun.stateBefore S rho i target).st.core.F := by
      rcases hcall with ⟨time, -, rfl⟩ | ⟨time, -, -, rfl⟩ <;> rfl
    have hfloorBefore : Block.Preceq before.core.F sigma.F := by
      rw [hinputF]
      exact hfloor
    have hfacts :
        (∀ D ∈ before.bodies, NamedRun.blockInRun S rho D) ∧
        Internal.NamedNoHighJustifications S.E S.cfg before ∧
        Proofs.Bridges.NamedProvenance S before ∧
        (∃ D ∈ before.bodies,
          (Protocol.derive_named S.E S.cfg D).h =
            before.core.h_max) := by
      rcases hcall with ⟨time, -, rfl⟩ | ⟨time, -, -, rfl⟩
      · refine ⟨?_, NamedJustificationBound.noHighJustifications_stateBefore
            S rho i target,
          Proofs.Bridges.namedProvenance_stateBefore S rho i target,
          Proofs.NamedStoreBridge.maximum_carrier_stateBefore S rho i target⟩
        intro D hD
        exact Proofs.Bridges.runBlock_of_stateBefore_mem S htarget hD
      · refine ⟨?_, ?_, ?_, ?_⟩
        · intro D hD
          exact Proofs.Bridges.runBlock_of_stateBefore_mem S htarget hD
        · simpa only [Protocol.NamedStore.setClock] using
            (NamedJustificationBound.noHighJustifications_stateBefore
              S rho i target)
        · simpa only [Protocol.NamedStore.setClock] using
            (Proofs.Bridges.namedProvenance_stateBefore S rho i target)
        · simpa only [Protocol.NamedStore.setClock] using
            (Proofs.NamedStoreBridge.maximum_carrier_stateBefore S rho i target)
    have hjust : Internal.NamedJustifiedAt S.E S.cfg A sigma.F sigma.h_F :=
      ⟨hAJ, hAh⟩
    have hfin : Statements.Instantiation.NamedFinalizedAt S.E S.cfg B sigma.F sigma.h_F :=
      ⟨rfl, rfl⟩
    let stored : Protocol.Store V := { before.core with
      σ := fun X => if X = B.erase then
        Protocol.named_transition S.E S.cfg
          (before.core.σ B.erase.parent) B
        else before.core.σ X
      T := insert B.erase before.core.T
      timestamp_block := fun X => if X = B.erase then
        some (before.core.t : Stamp) else before.core.timestamp_block X }
    let U := B.gf_votes.foldl
      (Protocol.on_goldfish_vote_checked S.E) stored
    let afterMax : Protocol.Store V :=
      { U with h_max := max U.h_max sigma.h }
    let afterJ : Protocol.Store V :=
      if Block.preceq afterMax.F sigma.J &&
          decide (Protocol.HeightId.mk afterMax.h_j afterMax.J.root <
            Protocol.HeightId.mk sigma.h_j sigma.J.root) then
        { afterMax with J := sigma.J, h_j := sigma.h_j }
      else afterMax
    have hderived :=
      NamedOutageHistory.GuardProofsTime.fresh_receipt_derived_and_admitted
        S before B hco hnew hpost
    change U.σ B.erase = sigma ∧ Block.Preceq U.F B.erase at hderived
    have hfields := healthy_gf_fold_fields S.E stored B.gf_votes
    have hUT : U.T = insert B.erase before.core.T := hfields.1
    have hUsigma : U.σ = stored.σ := hfields.2.1
    have hUFold : U.F = before.core.F := hfields.2.2.1
    have hUJ : U.J = before.core.J := hfields.2.2.2.1
    have hUhj : U.h_j = before.core.h_j := hfields.2.2.2.2.1
    have hUmax : U.h_max = before.core.h_max := hfields.2.2.2.2.2
    have hpostEq :
        (Execution.NamedReceiptCalls.postCore S before B).core =
          Protocol.update_finality U (U.σ B.erase) :=
      NamedReceiptCallsGF.post_core_stored S before B hnew hpost
    have htreeA : A.erase ∈ before.core.T := by
      rw [hco.1]
      exact Finset.mem_image_of_mem NamedBlock.erase hAheld
    have hFmemBefore : sigma.F ∈ before.core.T := by
      rw [← hAJ]
      exact NamedDerivationGeometry.core_ancestor_mem S.E S.cfg before hco
        htreeA
        (NamedDerivationGeometry.derive_named_anchors_preceq
          S.E S.cfg A).2
    have hFmemU : sigma.F ∈ U.T := by
      rw [hUT]
      exact Finset.mem_insert_of_mem hFmemBefore
    have hfloorU : Block.Preceq U.F sigma.F := by
      rw [hUFold]
      exact hfloorBefore
    have hupgrade : Block.Preceq sigma.F before.core.J :=
      StoreFinality.upgrade hfacts.2.1 hfacts.2.2.1 hAheld hjust hsb
        core.toNamedRootCollisionFree hBscope hfacts.1 hfin
    have hafterJ : Block.Preceq sigma.F afterJ.J := by
      by_cases hg :
          (Block.preceq afterMax.F sigma.J &&
            decide (Protocol.HeightId.mk afterMax.h_j afterMax.J.root <
              Protocol.HeightId.mk sigma.h_j sigma.J.root)) = true
      · have horder :=
          NamedDerivationGeometry.chainOrder_derive_named S.E S.cfg B
        have hFJ := horder.finalized_preceq_justified
        simpa only [afterJ, hg, if_true] using hFJ
      · have hgFalse :
            (Block.preceq afterMax.F sigma.J &&
              decide (Protocol.HeightId.mk afterMax.h_j afterMax.J.root <
                Protocol.HeightId.mk sigma.h_j sigma.J.root)) = false :=
          Bool.eq_false_of_not_eq_true hg
        have hafter : afterJ.J = afterMax.J := by
          simp only [afterJ, hgFalse, Bool.false_eq_true, if_false]
        rw [hafter]
        change Block.Preceq sigma.F U.J
        rw [hUJ]
        exact hupgrade
    have hviable : sigma.F ∈ Protocol.viable_tree U.σ U.F
        (max U.h_max sigma.h) U.T := by
      simp only [Protocol.viable_tree,
        Protocol.finalized_descendants, Protocol.viable,
        Finset.mem_filter, decide_eq_true_eq]
      refine ⟨⟨hFmemU, hfloorU⟩, ?_⟩
      by_cases hlow : max U.h_max sigma.h - 1 ≤ sigma.h
      · refine ⟨B.erase, ?_, ?_, ?_⟩
        · rw [hUT]
          exact Finset.mem_insert_self _ _
        · exact
            (NamedDerivationGeometry.derive_named_anchors_preceq
              S.E S.cfg B).1
        · rw [hderived.1]
          exact hlow
      · obtain ⟨M, hMheld, hMheight⟩ := hfacts.2.2.2
        have hMraw : M.erase ∈ before.core.T := by
          rw [hco.1]
          exact Finset.mem_image_of_mem NamedBlock.erase hMheld
        have hMne : M.erase ≠ B.erase := by
          intro heq
          exact hnew (heq ▸ hMraw)
        have hmaxEq : max U.h_max sigma.h = U.h_max := by
          by_cases hle : sigma.h ≤ U.h_max
          · exact Nat.max_eq_left hle
          · exfalso
            apply hlow
            rw [Nat.max_eq_right (Nat.le_of_not_ge hle)]
            exact Nat.sub_le _ _
        have hheight : sigma.h_F <
            (Protocol.derive_named S.E S.cfg M).h := by
          have hchain :=
            NamedDerivationGeometry.chainOrder_derive_named S.E S.cfg B
          have horder := hchain.finalized_below_height
          change sigma.h_F < sigma.h at horder
          have hs : sigma.h < max U.h_max sigma.h - 1 :=
            Nat.lt_of_not_ge hlow
          have hout : sigma.h_F < U.h_max := by
            rw [hmaxEq] at hs
            exact lt_of_lt_of_le (lt_trans horder hs) (Nat.sub_le _ _)
          rw [hMheight, ← hUmax]
          exact hout
        have hFM : Block.Preceq sigma.F M.erase :=
          NamedFinalizationBridge.finalized_preceq_of_height_lt
            S rho M B hsb core.toNamedRootCollisionFree
              (hfacts.1 M hMheld) hBscope hheight
        refine ⟨M.erase, ?_, hFM, ?_⟩
        · rw [hUT]
          exact Finset.mem_insert_of_mem hMraw
        · rw [hUsigma]
          change max U.h_max sigma.h - 1 ≤
            (if M.erase = B.erase then
              Protocol.named_transition S.E S.cfg
                (before.core.σ B.erase.parent) B
            else before.core.σ M.erase).h
          rw [if_neg hMne, hco.2.2.2.2 M hMheld, hMheight, ← hUmax,
            hmaxEq]
          exact Nat.sub_le _ _
    have hviableAfter : sigma.F ∈
        Protocol.viable_tree afterJ.σ afterJ.F
          afterJ.h_max afterJ.T := by
      dsimp only [afterJ, afterMax]
      split_ifs <;> exact hviable
    rw [hpostEq, hderived.1]
    change Block.Preceq sigma.F (Protocol.update_finality U sigma).F
    by_cases halready : Block.Preceq sigma.F U.F
    · exact Block.preceq_trans halready
        (update_finality_F U sigma)
    · change Block.Preceq sigma.F
          (if Block.prec afterJ.F sigma.F &&
              Block.preceq sigma.F afterJ.J &&
              decide (sigma.F ∈ Protocol.viable_tree afterJ.σ
                afterJ.F afterJ.h_max afterJ.T) then
            ({ afterJ with F := sigma.F } : Protocol.Store V)
          else afterJ).F
      exact healthy_absorb_finality_step U afterJ sigma (by
          dsimp only [afterJ, afterMax]
          split_ifs <;> rfl) (by
          dsimp only [afterJ, afterMax]
          split_ifs <;> rfl) (by
          dsimp only [afterJ, afterMax]
          split_ifs <;> rfl) (by
          dsimp only [afterJ, afterMax]
          split_ifs <;> rfl) halready hviable hafterJ

private theorem healthy_accepted_carrier_finality_preceq
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    (hsb : Internal.NamedOutageEntry.SlashableBound S rho) {target : V}
    (htarget : target ∈ rho.honest) {i : Nat} {B : NamedBlock V}
    {t : Time} (hBscope : NamedRun.blockInRun S rho B)
    (hacc : NamedRun.acceptsAt S rho i target (.block B) t)
    (hfloor : Block.Preceq
      (NamedRun.stateBefore S rho i target).st.core.F
      (Protocol.derive_named S.E S.cfg B).F) :
    Block.Preceq (Protocol.derive_named S.E S.cfg B).F
      (NamedRun.stateBefore S rho (i + 1) target).st.core.F := by
  obtain ⟨before, hcall, hnew, hpost, hbridge⟩ :=
    NamedOutageHistory.HeldSkipProducers.accepted_block_fresh_call
      S rho i target B t hacc
  exact Block.preceq_trans
    (healthy_fresh_receipt_absorbs_finality S rho core hsb htarget B hBscope
      before hcall hnew hpost hfloor) hbridge

/-- One healthy-prefix relay delay orders an earlier honest finalized root below
an honest target finalized root. The target read is at `read + Δ`, and that read
is required to be inside `cut`. -/
theorem finalized_preceq_of_evidence_delivered_healthyPrefix
    (S : Setup V) {rho : NamedRun V} (core : NamedAdmissibleCore S rho)
    (hsb : Internal.NamedOutageEntry.SlashableBound S rho) (cut : Time)
    (healthy : NamedHealthyPrefixDelivery S rho cut) {source target : V}
    (hsource : source ∈ rho.honest) (htarget : target ∈ rho.honest)
    {read out : Time} (hhop : read + S.E.Δ = out)
    (hcut : out ≤ cut) (hhor : out ≤ rho.horizon) :
    Block.Preceq
      (NamedRun.stateBeforeTime S rho read source).st.core.F
      (NamedRun.stateBeforeTime S rho out target).st.core.F := by
  have hsafe := NamedFinalityAgreement.stateBeforeTime_finalized_compatible
    S rho core.toNamedScheduleWellFormed hsb core.toNamedRootCollisionFree
      read out source target hsource htarget
  simp only [Block.compatible, Bool.or_eq_true] at hsafe
  rcases hsafe with hforward | hreverse
  · exact hforward
  · obtain ⟨D, hDread, hDF, -⟩ :=
      NamedFinalizationBridge.finalization_carrier_stateBeforeTime
        S rho read source
    obtain ⟨nSource, hnSource, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix
      S rho core.sorted read
    have hDsourcePrefix : D ∈
        (NamedRun.stateBefore S rho nSource source).st.bodies := by
      rw [← hnSource]
      exact hDread
    have hDscope : NamedRun.blockInRun S rho D :=
      Proofs.Bridges.runBlock_of_stateBefore_mem S hsource hDsourcePrefix
    have hDtargetFloor : Block.Preceq
        (NamedRun.stateBeforeTime S rho out target).st.core.F D.erase := by
      exact Block.preceq_trans hreverse (by
        rw [← hDF]
        exact (NamedDerivationGeometry.derive_named_anchors_preceq
          S.E S.cfg D).1)
    have hDtarget :=
      (NamedHealthyHeadReady.healthy_head_body_at_read S rho core cut healthy
        source hsource target htarget D read out out hDread
        (le_of_eq hhop) (le_refl _) hcut hDtargetFloor).1
    obtain ⟨n, hn, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix
      S rho core.sorted out
    rw [hn] at hDtarget
    rcases NamedOutageProvenance.held_block_origin
        S rho n target hDtarget with hgen | ⟨k, hk, t, hacc⟩
    · subst D
      rw [← hDF]
      change Block.Preceq Block.genesis _
      exact Protocol.preceq_genesis _
    · have hmono : Block.Preceq
          (NamedRun.stateBefore S rho k target).st.core.F
          (NamedRun.stateBefore S rho n target).st.core.F :=
        Proofs.NamedRuntime.stateBefore_F_mono S rho target (Nat.le_of_lt hk)
      rw [← hn] at hmono
      have hfloor : Block.Preceq
          (NamedRun.stateBefore S rho k target).st.core.F
          (Protocol.derive_named S.E S.cfg D).F :=
        Block.preceq_trans hmono (by
          rw [hDF]
          exact hreverse)
      have habsorb := healthy_accepted_carrier_finality_preceq
        S rho core hsb htarget hDscope hacc hfloor
      have hmonoAfter : Block.Preceq
          (NamedRun.stateBefore S rho (k + 1) target).st.core.F
          (NamedRun.stateBefore S rho n target).st.core.F :=
        Proofs.NamedRuntime.stateBefore_F_mono S rho target
          (Nat.succ_le_of_lt hk)
      rw [← hn] at hmonoAfter
      rw [← hDF]
      exact Block.preceq_trans habsorb hmonoAfter

#print axioms finalized_preceq_of_evidence_delivered_healthyPrefix

private theorem healthy_domain_g1_le_domain_g0 (S : Setup V) (r : Round) :
    domain S.E S.hc r .g1 ≤ domain S.E S.hc r .g0 := by
  simp only [domain, Phase.domainOffset]
  exact Int.add_le_add_left
    (Int.mul_le_mul_of_nonneg_right (by norm_num) S.E.Δ_pos.le) _

private theorem healthy_domain_g2_add_delta_eq_g1 (S : Setup V) (r : Round) :
    domain S.E S.hc r .g2 + S.E.Δ = domain S.E S.hc r .g1 := by
  unfold domain Phase.domainOffset
  ring

/-- The healthy-prefix twin of the cross-reader finalized-prefix cap. -/
theorem crossReaderFinalizedBelow_of_slashableBound_and_healthyPrefix
    (S : Setup V) {rho : NamedRun V} (core : NamedAdmissibleCore S rho)
    (hsb : Internal.NamedOutageEntry.SlashableBound S rho) {r : Round}
    (cut : Time) (healthy : NamedHealthyPrefixDelivery S rho cut)
    (hcut : domain S.E S.hc r .g0 ≤ cut)
    (horizon : domain S.E S.hc r .g0 ≤ rho.horizon)
    {source target : V} (hsource : source ∈ rho.honest)
    (htarget : target ∈ rho.honest) {B : Block V}
    (hforward : ∀ sender u root H,
      u ∈ DecoupledConsensusModel.Protocol.interpretedInputs
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) source).st.core.toHealing.gradeView
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) source).st.core.F
        S.hc.η_SG r (early S.E S.hc r .g2) sender →
      localCovers
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) source).st.core.toHealing.gradeView
        u.confirmed B = true →
      u.confirmed = some root →
      Block.find?
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) source).st.core.toHealing.gradeView.T root =
          some H →
      Block.Preceq
        (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1) target).st.core.F H) :
    CrossReaderFinalizedBelow S rho r source target B := by
  have hg1Cap : domain S.E S.hc r .g1 ≤ cut :=
    (healthy_domain_g1_le_domain_g0 S r).trans hcut
  have hg1Horizon : domain S.E S.hc r .g1 ≤ rho.horizon :=
    (healthy_domain_g1_le_domain_g0 S r).trans horizon
  have hForder := finalized_preceq_of_evidence_delivered_healthyPrefix
    S core hsb cut healthy hsource htarget
      (healthy_domain_g2_add_delta_eq_g1 S r) hg1Cap hg1Horizon
  refine ⟨hforward, ?_⟩
  intro sender u root H hu hconf hfind
  obtain ⟨-, hready⟩ := Finset.mem_filter.mp hu
  simp only [DecoupledConsensusModel.Protocol.bodyReady, hconf, hfind,
    Bool.and_eq_true] at hready
  have hcompat := hready.2
  simp only [Block.compatible, Bool.or_eq_true] at hcompat ⊢
  rcases hcompat with hHF | hFH
  · rcases Block.preceq_linear hForder hHF with hsourceH | hHsource
    · exact Or.inr hsourceH
    · exact Or.inl hHsource
  · exact Or.inr (Block.preceq_trans hForder hFH)

#print axioms crossReaderFinalizedBelow_of_slashableBound_and_healthyPrefix

private theorem healthy_held_find_at_strict
    (S : Setup V) (rho : NamedRun V) (core : NamedAdmissibleCore S rho)
    {reader : V} (hreader : reader ∈ rho.honest) (time : Time)
    (B : NamedBlock V)
    (hB : B ∈ (NamedRun.stateBeforeTime S rho time reader).st.bodies) :
    Block.find?
      (NamedRun.stateBeforeTime S rho time reader).st.core.T B.root =
        some B.erase := by
  have hco :=
    (Proofs.NamedRuntime.stateBeforeTime_invariants S rho time reader).1.1.1
  have hBraw : B.erase ∈
      (NamedRun.stateBeforeTime S rho time reader).st.core.T := by
    rw [hco.1]
    exact Finset.mem_image_of_mem NamedBlock.erase hB
  obtain ⟨n, hn, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix
    S rho core.sorted time
  have hBprefix : B ∈
      (NamedRun.stateBefore S rho n reader).st.bodies := by
    rw [← hn]
    exact hB
  have hBscope : NamedRun.blockInRun S rho B :=
    Proofs.Bridges.runBlock_of_stateBefore_mem S hreader hBprefix
  rw [← Proofs.NamedWire.erase_root B]
  apply Proofs.Optimistic.find?_eq_some_of_unique hBraw
  intro X hX hroot
  obtain ⟨C, hCheld, hCErase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime
      S rho time reader hX
  have hCprefix : C ∈
      (NamedRun.stateBefore S rho n reader).st.bodies := by
    rw [← hn]
    exact hCheld
  have hCscope : NamedRun.blockInRun S rho C :=
    Proofs.Bridges.runBlock_of_stateBefore_mem S hreader hCprefix
  have hCB : C = B := core.toNamedRootCollisionFree.root_injective
    C B hCscope hBscope C B
      (Or.inl (Proofs.NamedAncestry.named_self C))
      (Or.inr (Proofs.NamedAncestry.named_self B)) (by
        rw [← Proofs.NamedWire.erase_root C, ← Proofs.NamedWire.erase_root B,
          hCErase, hroot])
  rw [← hCErase, hCB]

private theorem healthy_early_g2_add_delta_eq_g1 (S : Setup V) (r : Round) :
    early S.E S.hc r .g2 + S.E.Δ = early S.E S.hc r .g1 :=
  NamedOutageHistory.GuardedHelpers.early_g2_add_delta S r

private theorem healthy_late_g1_add_delta_eq_g2 (S : Setup V) (r : Round) :
    late S.E S.hc r .g1 + S.E.Δ = late S.E S.hc r .g2 :=
  NamedOutageHistory.ReadyHeadReturnTime.late_g1_add_delta S r

/-- The healthy-prefix twin of the cross-reader body-open guard. -/
theorem crossReaderBodyReadyGuard_of_finalizedBelow_and_healthyPrefix
    (S : Setup V) {rho : NamedRun V} (core : NamedAdmissibleCore S rho)
    {r : Round} (hr : 0 < r)
    (cut : Time) (healthy : NamedHealthyPrefixDelivery S rho cut)
    (hcut : domain S.E S.hc r .g0 ≤ cut)
    (horizon : domain S.E S.hc r .g0 ≤ rho.horizon)
    {source target : V} (hsource : source ∈ rho.honest)
    (htarget : target ∈ rho.honest) {B : Block V}
    (hbelow : CrossReaderFinalizedBelow S rho r source target B) :
    CrossReaderBodyReadyGuard S rho r source target B := by
  have hearlyHorizon : early S.E S.hc r .g1 ≤ rho.horizon :=
    (NamedOutageHistory.GuardedHelpers.early_g1_le_domain_g1 S r).trans
      ((healthy_domain_g1_le_domain_g0 S r).trans horizon)
  have hlateHorizon : late S.E S.hc r .g2 ≤ rho.horizon := by
    rw [NamedOutageClosure.q10_late_g2_eq_domain_g2]
    exact (NamedOutageHistory.GuardedHelpers.domain_g2_le_domain_g1 S r).trans
      ((healthy_domain_g1_le_domain_g0 S r).trans horizon)
  have hearlyCut : early S.E S.hc r .g1 ≤ cut :=
    (NamedOutageHistory.GuardedHelpers.early_g1_le_domain_g1 S r).trans
      ((healthy_domain_g1_le_domain_g0 S r).trans hcut)
  have hlateCut : late S.E S.hc r .g2 ≤ cut := by
    rw [NamedOutageClosure.q10_late_g2_eq_domain_g2]
    exact (NamedOutageHistory.GuardedHelpers.domain_g2_le_domain_g1 S r).trans
      ((healthy_domain_g1_le_domain_g0 S r).trans hcut)
  refine ⟨?_, ?_⟩
  · intro sender u hu hcover
    obtain ⟨hraw, hready⟩ := Finset.mem_filter.mp hu
    cases hconf : u.confirmed with
    | none => simp [DecoupledConsensusModel.Protocol.bodyReady, hconf]
    | some root =>
      simp only [DecoupledConsensusModel.Protocol.bodyReady, hconf] at hready ⊢
      cases hfind : Block.find?
          (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) source).st.core.toHealing.gradeView.T root with
      | none => rw [hfind] at hready; exact absurd hready (by simp)
      | some H =>
        rw [hfind] at hready
        simp only [Bool.and_eq_true] at hready
        obtain ⟨hstamp, -⟩ := hready
        have hHtree : H ∈
            (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) source).st.core.T :=
          Proofs.HealingLemmas.find?_mem hfind
        have hcoh := (Proofs.NamedRuntime.stateBeforeTime_invariants S rho
          (domain S.E S.hc r .g2) source).1.1.1
        rw [hcoh.1] at hHtree
        obtain ⟨Hn, hHbody, hHnErase⟩ := Finset.mem_image.mp hHtree
        have hHearly : Hn ∈ (NamedRun.stateBeforeTime S rho
            (early S.E S.hc r .g2) source).st.bodies := by
          apply NamedPublicCutBody.body_mem_stateBeforeTime_of_public_stampedBefore
            S rho core.toNamedScheduleWellFormed
            (NamedOutageHistory.GuardedHelpers.early_g2_public S r hr)
            hHbody
          simpa only [hHnErase] using hstamp
        have hdeadline : early S.E S.hc r .g2 + S.E.Δ ≤
            early S.E S.hc r .g1 := by
          exact (healthy_early_g2_add_delta_eq_g1 S r).le
        have hFH : Block.Preceq
            (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1) target).st.core.F Hn.erase := by
          rw [hHnErase]
          exact hbelow.forward sender u root H hu hcover hconf hfind
        obtain ⟨-, hstampTarget, hfindTarget⟩ :=
          NamedHealthyHeadReady.healthy_head_body_at_read
            S rho core cut healthy source hsource target htarget Hn
            (early S.E S.hc r .g2) (early S.E S.hc r .g1)
            (domain S.E S.hc r .g1) hHearly hdeadline
            (NamedOutageHistory.GuardedHelpers.early_g1_le_domain_g1 S r)
            hearlyCut hFH
        have hroot : Hn.root = root := by
          rw [← Proofs.NamedWire.erase_root, hHnErase]
          exact Proofs.HealingLemmas.find?_root hfind
        have hfindTarget' : Block.find?
            (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1) target).st.core.T Hn.root =
              some Hn.erase := by
          simpa only [Proofs.NamedWire.erase_root] using hfindTarget
        change (match Block.find?
          (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1) target).st.core.T root with
          | none => false
          | some head => stampedBefore
              (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1) target).st.core.timestamp_block
              (early S.E S.hc r .g1) head &&
            Block.compatible head
              (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1) target).st.core.F) = true
        rw [← hroot, hfindTarget', Bool.and_eq_true]
        refine ⟨hstampTarget, ?_⟩
        simp only [Block.compatible, Bool.or_eq_true]
        exact Or.inr hFH
  · intro sender u hu
    obtain ⟨hraw, hready⟩ := Finset.mem_filter.mp hu
    cases hconf : u.confirmed with
    | none => simp [DecoupledConsensusModel.Protocol.bodyReady, hconf]
    | some root =>
      simp only [DecoupledConsensusModel.Protocol.bodyReady, hconf] at hready ⊢
      cases hfind : Block.find?
          (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1) target).st.core.toHealing.gradeView.T root with
      | none => rw [hfind] at hready; exact absurd hready (by simp)
      | some H =>
        rw [hfind] at hready
        simp only [Bool.and_eq_true] at hready
        obtain ⟨hstamp, -⟩ := hready
        have hHtree : H ∈
            (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g1) target).st.core.T :=
          Proofs.HealingLemmas.find?_mem hfind
        have hcoh := (Proofs.NamedRuntime.stateBeforeTime_invariants S rho
          (domain S.E S.hc r .g1) target).1.1.1
        rw [hcoh.1] at hHtree
        obtain ⟨Hn, hHbody, hHnErase⟩ := Finset.mem_image.mp hHtree
        have hHlate : Hn ∈ (NamedRun.stateBeforeTime S rho
            (late S.E S.hc r .g1) target).st.bodies := by
          apply NamedPublicCutBody.body_mem_stateBeforeTime_of_public_stampedBefore
            S rho core.toNamedScheduleWellFormed
            (NamedOutageClosure.q10_late_g1_public S r hr) hHbody
          simpa only [hHnErase] using hstamp
        have hdeadline : late S.E S.hc r .g1 + S.E.Δ ≤
            late S.E S.hc r .g2 := by
          exact (healthy_late_g1_add_delta_eq_g2 S r).le
        have hcompatSource : Block.compatible Hn.erase
            (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) source).st.core.F = true := by
          rw [hHnErase]
          exact hbelow.backward sender u root H hu hconf hfind
        obtain ⟨hHsource, hstampSource, hfindSource⟩ :
            Hn ∈ (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) source).st.bodies ∧
            stampedBefore
              (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) source).st.core.timestamp_block
              (late S.E S.hc r .g2) Hn.erase = true ∧
            Block.find? (NamedRun.stateBeforeTime S rho
              (domain S.E S.hc r .g2) source).st.core.T
              Hn.root = some Hn.erase := by
          simp only [Block.compatible, Bool.or_eq_true] at hcompatSource
          rcases hcompatSource with hHF | hFH
          · have hFmem := Proofs.NamedStoreBridge.finalizedInTree_stateBeforeTime
              S rho (domain S.E S.hc r .g2) source
            have hpc := Proofs.NamedStoreBridge.parentClosed_stateBeforeTime
              S rho (domain S.E S.hc r .g2) source
            have hHraw : Hn.erase ∈
                (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) source).st.core.T :=
              Proofs.Records.mem_of_preceq ((parentClosed_iff _).mp hpc).2
                Hn.erase _ hFmem hHF
            obtain ⟨K, hKheld, hKErase⟩ :=
              Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime
                S rho (domain S.E S.hc r .g2) source hHraw
            obtain ⟨ns, hns, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix
              S rho core.sorted (domain S.E S.hc r .g2)
            have hKprefix : K ∈
                (NamedRun.stateBefore S rho ns source).st.bodies := by
              rw [← hns]
              exact hKheld
            have hKscope : NamedRun.blockInRun S rho K :=
              Proofs.Bridges.runBlock_of_stateBefore_mem S hsource hKprefix
            obtain ⟨nt, hnt, -⟩ := Proofs.NamedRuntime.stateBeforeTime_eq_prefix
              S rho core.sorted (domain S.E S.hc r .g1)
            have hHprefix : Hn ∈
                (NamedRun.stateBefore S rho nt target).st.bodies := by
              rw [← hnt]
              exact hHbody
            have hHscope : NamedRun.blockInRun S rho Hn :=
              Proofs.Bridges.runBlock_of_stateBefore_mem S htarget hHprefix
            have hKH : K = Hn := core.toNamedRootCollisionFree.root_injective
              K Hn hKscope hHscope K Hn
                (Or.inl (Proofs.NamedAncestry.named_self K))
                (Or.inr (Proofs.NamedAncestry.named_self Hn)) (by
                  rw [← Proofs.NamedWire.erase_root K, ← Proofs.NamedWire.erase_root Hn,
                    hKErase])
            subst K
            have hstamp :=
              NamedBlockStamp.held_body_stampedBefore_stateBeforeTime
                S rho core.toNamedScheduleWellFormed source
                  (domain S.E S.hc r .g2) Hn hKheld
            refine ⟨hKheld, ?_, ?_⟩
            · simpa only [NamedOutageClosure.q10_late_g2_eq_domain_g2] using hstamp
            · exact healthy_held_find_at_strict S rho core hsource
                (domain S.E S.hc r .g2) Hn hKheld
          · simpa only [Proofs.NamedWire.erase_root] using
              (NamedHealthyHeadReady.healthy_head_body_at_read
                S rho core cut healthy target htarget source hsource Hn
                (late S.E S.hc r .g1) (late S.E S.hc r .g2)
              (domain S.E S.hc r .g2) hHlate hdeadline
                (NamedOutageClosure.q10_late_g2_eq_domain_g2 S r).le hlateCut hFH)
        have hroot : Hn.root = root := by
          rw [← Proofs.NamedWire.erase_root, hHnErase]
          exact Proofs.HealingLemmas.find?_root hfind
        have hfindSource' : Block.find?
            (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) source).st.core.T Hn.root =
              some Hn.erase := by
          simpa only [Proofs.NamedWire.erase_root] using hfindSource
        change (match Block.find?
          (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) source).st.core.T root with
          | none => false
          | some head => stampedBefore
              (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) source).st.core.timestamp_block
              (late S.E S.hc r .g2) head &&
            Block.compatible head
              (NamedRun.stateBeforeTime S rho (domain S.E S.hc r .g2) source).st.core.F) = true
        rw [← hroot, hfindSource', Bool.and_eq_true]
        refine ⟨hstampSource, ?_⟩
        exact hcompatSource

#print axioms crossReaderBodyReadyGuard_of_finalizedBelow_and_healthyPrefix

end DecoupledConsensusModel.Proofs.HealingSurface

end
