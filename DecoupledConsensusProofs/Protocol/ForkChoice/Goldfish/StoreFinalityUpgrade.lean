module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Handlers.Bridges
public import DecoupledConsensusProofs.Protocol.ValidatorClient.RecordClean
public import DecoupledConsensusProofs.Protocol.ChainState.Main
public import DecoupledConsensusInternal.Execution.Assumptions
public import DecoupledConsensusProofs.Protocol.Handlers.StoreFinality
public import DecoupledConsensusProofs.Protocol.ChainState.FinalityComparison
public import DecoupledConsensusProofs.Protocol.ChainState.CheckpointHeights
public import DecoupledConsensusProofs.Protocol.ChainState.JustificationCertificates
public import DecoupledConsensusProofs.Protocol.Evidence.ProvenanceBridge
public import DecoupledConsensusProofs.Protocol.Handlers.JustificationBound

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# B8 justification upgrade and B9 persistent viability

This file proves the current-store core of doc1's upgrade property. The store's
justification height must already be at least the finalized height. B13 supplies
that premise when the store contains a processed justification witness. It then
uses directed earlier safety and the maximum-height witness to prove the rewrite's
persistent B9 form: the viable tree contains a descendant of historical `F`.

proof note. `RunBlock` is `NamedRun.blockInRun` over
`NamedBlock V` and `SlashableBound` already quantifies named run blocks, so the
external finalizer is a named body and its finalization is
`Statements.Instantiation.NamedFinalizedAt`, over `derive_named`. Directed earlier safety is
`Proofs.NamedFinalizationBridge.finalized_preceq_of_height_lt`
(`Protocol.finalized_preceq_of_height_lt` is archived under ). The
store is the named store, so the derived-state agreement the prior proof took as
`DerivedStateAgrees` is the coherence clause `NamedStore.DerivedView`.
-/



namespace DecoupledConsensusModel
namespace Proofs
namespace StoreFinality

open Protocol (HeightConfig derive_named)
open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]


/-- Corrected B9 while the current finalized block is at or below historical
`F`. If `h_max` has passed `h_f`, its processed height witness descends from
`F` by directed earlier safety. Otherwise, the finalizing carrier `BF` itself is
the viability witness.

Statement change (ledger row C): the store is a
`Protocol.NamedStore`, the external finalizer is a named body, the run-scope
premises are the named ones, and the `h_max` witness is the named carrier
(`Proofs.NamedStoreBridge.maximum_carrier_*` has exactly this shape). -/
theorem finalized_mem_viable_of_current_preceq {S : Setup V} {ρ : Run V}
    {st : Protocol.NamedStore V} {BF : NamedBlock V} {F : Block V} {h_f : Height}
    (hsb : SlashableBound S ρ)
    (hcf : RootCollisionFree S ρ)
    (hBF : RunBlock S ρ BF)
    (hRun : ∀ D ∈ st.bodies, RunBlock S ρ D)
    (hBFT : BF ∈ st.bodies)
    (hFT : F ∈ st.core.T)
    (hcoh : Proofs.NamedStore.Coherent S.E S.cfg st)
    (hmax : ∃ D ∈ st.bodies, (derive_named S.E S.cfg D).h = st.core.h_max)
    (hfin : Statements.Instantiation.NamedFinalizedAt S.E S.cfg BF F h_f)
    (hcur : Block.preceq st.core.F F = true) :
    F ∈ Protocol.viable_tree st.core.σ st.core.F st.core.h_max st.core.T := by
  simp only [Protocol.viable_tree, Protocol.finalized_descendants,
    Protocol.viable, Finset.mem_filter, decide_eq_true_eq]
  refine ⟨⟨hFT, hcur⟩, ?_⟩
  by_cases hhigh : h_f < st.core.h_max
  · obtain ⟨W, hWb, hmaxW⟩ := hmax
    have hheight : (derive_named S.E S.cfg BF).h_F < (derive_named S.E S.cfg W).h := by
      rw [hfin.2, hmaxW]
      exact hhigh
    have hFW : Block.Preceq F W.erase := by
      have h := NamedFinalizationBridge.finalized_preceq_of_height_lt S ρ W BF hsb hcf
        (hRun W hWb) hBF hheight
      rwa [hfin.1] at h
    refine ⟨W.erase, ?_, hFW, ?_⟩
    · rw [hcoh.1]
      exact Finset.mem_image_of_mem NamedBlock.erase hWb
    · rw [hcoh.2.2.2.2 W hWb, hmaxW]
      exact Nat.sub_le _ _
  · have hmaxhf : st.core.h_max ≤ h_f := Nat.le_of_not_gt hhigh
    have hhf : h_f < (derive_named S.E S.cfg BF).h := by
      rw [← hfin.2]
      exact (NamedDerivationGeometry.chainOrder_derive_named S.E S.cfg BF).finalized_below_height
    have hFBF : Block.preceq F BF.erase = true := by
      rw [← hfin.1]
      exact (NamedDerivationGeometry.derive_named_anchors_preceq S.E S.cfg BF).1
    refine ⟨BF.erase, ?_, hFBF, ?_⟩
    · rw [hcoh.1]
      exact Finset.mem_image_of_mem NamedBlock.erase hBFT
    · rw [hcoh.2.2.2.2 BF hBFT]
      exact Nat.le_trans (Nat.sub_le _ _)
        (Nat.le_trans hmaxhf (Nat.le_of_lt hhf))

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
    · exact Proofs.NamedAncestry.named_extend s root votes support rows proposer (ih hparent)

omit [Fintype V] in
/-- A height-pair vote and a finality pair at the same height on different
targets are an E1 pair. Local copy of the private helper of
`NamedFinalityComparison`. -/
private theorem matching_finality_e1 (a b : NamedAttestation V)
    (h : Height) (entry finalized : BlockId)
    (hv : a.val_index = b.val_index)
    (hm : a.height_pair.matchesEntry h entry = true)
    (hf : b.finality_pair = some ⟨h, finalized⟩) (hne : entry ≠ finalized) :
    Protocol.Slashable a.erase b.erase := by
  cases hp : a.height_pair with
  | empty => simp [hp, NamedHeightPair.matchesEntry] at hm
  | vote height root timeout =>
    have heq : height = h ∧ root = entry := by
      simpa only [hp, NamedHeightPair.matchesEntry, decide_eq_true_eq] using hm
    rcases heq with ⟨rfl, rfl⟩
    cases timeout <;>
      simp [Protocol.Slashable, Protocol.slashable,
        Protocol.e1Slashable, Protocol.e1Fields,
        Protocol.conflictsWithFinality, Protocol.sameValidator,
        NamedAttestation.erase, NamedHeightPair.erase, hp, hf, hv, hne]


/-- **B8 after the B13 height floor**, over the named runtime. A current store
justification at or above the finalized height descends from `F`.

Statement change (ledger row C,): the store is a
`Protocol.NamedStore`, the finalizer is a named body, `RootInjectiveBelow` is
the run-wide `RootCollisionFree`, and the retired `Proofs.Bridges.Provenance` is
`Proofs.Bridges.NamedProvenance`, which `Proofs.Bridges.namedProvenance_*` delivers at every
named read with no premise.

The strict-height branch is directed earlier safety plus the checkpoint heights of
`NamedCheckpointHeights`: were the store justification a proper ancestor of
`F`, its own named height would sit at `h_j` and below `h_f`. The equal-height
branch intersects the named justification quorum of the provenance carrier with
the named finality quorum of the finalizer and rejects the E1 clash; both
certificates are over `derive_named`, and `Proofs.Bridges.erase_mem_chain_attestations`
places their rows on the two chains the accountable bound reads. -/
theorem upgrade_of_height_le {S : Setup V} {ρ : Run V}
    {st : Protocol.NamedStore V} {BF : NamedBlock V} {F : Block V} {h_f : Height}
    (hsb : SlashableBound S ρ)
    (hcf : RootCollisionFree S ρ)
    (hBF : RunBlock S ρ BF)
    (hRun : ∀ D ∈ st.bodies, RunBlock S ρ D)
    (hprov : Proofs.Bridges.NamedProvenance S st)
    (hfin : Statements.Instantiation.NamedFinalizedAt S.E S.cfg BF F h_f)
    (hle : h_f ≤ st.core.h_j) :
    Block.preceq F st.core.J = true := by
  obtain ⟨C, hC, hCJ, hCh⟩ := hprov.2
  have hCrun : RunBlock S ρ C := hRun C hC
  by_cases hz : h_f = 0
  · have hFg : F = Block.genesis := by
      rw [← hfin.1]
      exact NamedFinalityCertificates.finalized_zero_is_genesis S.E S.cfg BF
        (by rw [hfin.2]; exact hz)
    rw [hFg]
    exact Protocol.preceq_genesis st.core.J
  have hFnz : (derive_named S.E S.cfg BF).h_F ≠ 0 := by
    rw [hfin.2]
    exact hz
  have hjnz : (derive_named S.E S.cfg C).h_j ≠ 0 := by
    rw [hCh]
    intro h0
    rw [h0] at hle
    exact hz (Nat.le_zero.mp hle)
  rcases lt_or_eq_of_le hle with hlt | heq
  · have hCbelow : h_f < (derive_named S.E S.cfg C).h := by
      have hjh :=
        (NamedDerivationGeometry.chainOrder_derive_named S.E S.cfg C).justified_below_height
      rw [hCh] at hjh
      exact lt_trans hlt hjh
    have hFC : Block.Preceq F C.erase := by
      have h := NamedFinalizationBridge.finalized_preceq_of_height_lt S ρ C BF hsb hcf
        hCrun hBF (by rw [hfin.2]; exact hCbelow)
      rwa [hfin.1] at h
    have hJC : Block.Preceq st.core.J C.erase := by
      rw [← hCJ]
      exact (Proofs.NamedStoreRoots.derive_named_anchors_preceq S.E S.cfg C).2
    rcases Block.preceq_linear hFC hJC with hFJ | hJF
    · exact hFJ
    · exfalso
      obtain ⟨Jn, hJnC, hJnE, hJnh⟩ :=
        (NamedCheckpointHeights.justified_ancestor_height S.E S.cfg C).resolve_left hjnz
      obtain ⟨Fn, hFnBF, hFnE, hFnh⟩ :=
        (NamedCheckpointHeights.finalized_ancestor_height S.E S.cfg BF).resolve_left hFnz
      have hlift : Block.Preceq Jn.erase Fn.erase := by
        rw [hJnE, hCJ, hFnE, hfin.1]
        exact hJF
      obtain ⟨J', hJ'Fn, hJ'E⟩ := Proofs.NamedAncestry.erased_ancestor_lift Fn hlift
      have hroots : Jn.root = J'.root := by
        rw [← Proofs.NamedWire.erase_root Jn, ← Proofs.NamedWire.erase_root J', hJ'E]
      have hEq : Jn = J' :=
        NamedRootCollisionFree.root_injective hcf C BF hCrun hBF Jn J' (Or.inl hJnC)
          (Or.inr (named_trans hJ'Fn hFnBF)) hroots
      have hmono : (derive_named S.E S.cfg Jn).h ≤ (derive_named S.E S.cfg Fn).h := by
        rw [hEq]
        exact Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hJ'Fn
      rw [hJnh, hCh, hFnh, hfin.2] at hmono
      exact absurd hmono (Nat.not_le_of_gt hlt)
  · obtain ⟨Jn, hJnC, hJnE, Qj, hQj, hwj⟩ :=
      NamedJustificationCertificates.justification_certificate S.E S.cfg C hjnz
    obtain ⟨Fn, hFnBF, hFnE, Qf, hQf, hwf⟩ :=
      NamedFinalityCertificates.finality_certificate S.E S.cfg BF hFnz
    have hJnroot : Jn.root = st.core.J.root := by
      rw [← Proofs.NamedWire.erase_root Jn, hJnE, hCJ]
    have hFnroot : Fn.root = F.root := by
      rw [← Proofs.NamedWire.erase_root Fn, hFnE, hfin.1]
    by_cases hr : st.core.J.root = F.root
    · have hinj : Execution.RootInjectiveOnAncestors C.erase BF.erase :=
        NamedFinalizationBridge.rootInjectiveOnAncestors_of_collisionFree S ρ hcf C BF
          hCrun hBF
      have hJF : st.core.J = F :=
        hinj st.core.J F
          ⟨C.erase, by simp, by
            rw [← hCJ]
            exact (Proofs.NamedStoreRoots.derive_named_anchors_preceq S.E S.cfg C).2⟩
          ⟨BF.erase, by simp, by
            rw [← hfin.1]
            exact (Proofs.NamedStoreRoots.derive_named_anchors_preceq S.E S.cfg BF).1⟩
          hr
      rw [hJF]
      exact Block.preceq_self _
    · exfalso
      apply hsb C BF hCrun hBF
      refine ⟨Qj ∩ Qf, quorum_intersection S.E hQj hQf, fun i hi => ?_⟩
      obtain ⟨hij, hif⟩ := Finset.mem_inter.mp hi
      obtain ⟨ca, a, hca, ha, hav, hap⟩ := hwj i hij
      obtain ⟨cb, b, hcb, hb, hbv, hbp⟩ := hwf i hif
      refine ⟨a.erase, Proofs.Bridges.erase_mem_chain_attestations C ca hca a ha,
        b.erase, Proofs.Bridges.erase_mem_chain_attestations BF cb hcb b hb, hav, hbv, ?_⟩
      refine matching_finality_e1 a b h_f Jn.root Fn.root (hav.trans hbv.symm) ?_ ?_ ?_
      · rw [hap]
        simp only [NamedHeightPair.matchesEntry, decide_eq_true_eq, and_true]
        rw [hCh, ← heq]
      · rw [hbp, hfin.2]
      · rw [hJnroot, hFnroot]
        exact hr


/-- **B8 (upgrade)**, over the named runtime. If a held body carries the
justification of an externally finalized `F` at the height where `BF`
finalized it, every current store justification descends from `F`.

Statement change (ledger row C,): earlier takes one
`DepReachableStore` premise and spends it on exactly two store facts, B13 and
provenance, through two conversions  forbids resurrecting. Both facts now
have premise-free named producers at every read —
`NamedJustificationBound.noHighJustifications_*` and
`Proofs.Bridges.namedProvenance_*` — so they are taken directly, the way
`finalized_mem_viable_of_current_preceq` above takes its own. -/
theorem upgrade {S : Setup V} {ρ : Run V} {st : Protocol.NamedStore V}
    {BF B : NamedBlock V} {F : Block V} {h_f : Height}
    (hnhj : Internal.NamedNoHighJustifications S.E S.cfg st)
    (hprov : Proofs.Bridges.NamedProvenance S st)
    (hB : B ∈ st.bodies)
    (hjust : Internal.NamedJustifiedAt S.E S.cfg B F h_f)
    (hsb : SlashableBound S ρ)
    (hcf : RootCollisionFree S ρ)
    (hBF : RunBlock S ρ BF)
    (hRun : ∀ D ∈ st.bodies, RunBlock S ρ D)
    (hfin : Statements.Instantiation.NamedFinalizedAt S.E S.cfg BF F h_f) :
    Block.preceq F st.core.J = true := by
  have hfloor : h_f ≤ st.core.h_j := by
    rw [← hjust.2]
    exact hnhj B hB
  exact upgrade_of_height_le hsb hcf hBF hRun hprov hfin hfloor


/-- **B9 (persistent finalized viability)**, over the named runtime. If a held
body carries the justification of an externally finalized `F`, the current
viable tree contains a descendant of `F`.

Statement change (ledger row C,): earlier's one
`DepReachableStore` premise is replaced by the state facts it delivered, each
of which now has a premise-free named producer at every read — coherence and
`F ⪯ J` from `NamedStoreBridge`, B13 and the justification bound from
`NamedJustificationBound`, provenance from `Bridges`, the height carrier from
`Proofs.NamedStoreBridge.maximum_carrier_*`, and `FinalizedViable` from
`NamedFinalizedViable`.

When store finalization is still at or below `F`, the maximum-height carrier
descends from `F` by directed earlier safety and makes `F` itself viable; the
justification bound is what puts the carrier's height above `h_f`. When store
finalization has passed `F`, the current finalized block is the descendant, and
it is viable on its own. -/
theorem viableFinalized_external {S : Setup V} {ρ : Run V}
    {st : Protocol.NamedStore V} {BF B : NamedBlock V} {F : Block V} {h_f : Height}
    (hco : Proofs.NamedStore.Coherent S.E S.cfg st)
    (hnhj : Internal.NamedNoHighJustifications S.E S.cfg st)
    (hprov : Proofs.Bridges.NamedProvenance S st)
    (hbelow : Internal.JustificationBelowMax st.core)
    (hviable : FinalizedViable st.core)
    (horder : Block.preceq st.core.F st.core.J = true)
    (hmax : ∃ D ∈ st.bodies, (derive_named S.E S.cfg D).h = st.core.h_max)
    (hB : B ∈ st.bodies)
    (hjust : Internal.NamedJustifiedAt S.E S.cfg B F h_f)
    (hsb : SlashableBound S ρ)
    (hcf : RootCollisionFree S ρ)
    (hBF : RunBlock S ρ BF)
    (hRun : ∀ D ∈ st.bodies, RunBlock S ρ D)
    (hfin : Statements.Instantiation.NamedFinalizedAt S.E S.cfg BF F h_f) :
    Internal.HasViableDescendant st.core F := by
  have hFT : F ∈ st.core.T := by
    rw [← hjust.1]
    refine NamedDerivationGeometry.core_ancestor_mem S.E S.cfg st hco ?_
      (Proofs.NamedStoreRoots.derive_named_anchors_preceq S.E S.cfg B).2
    rw [hco.1]
    exact Finset.mem_image_of_mem NamedBlock.erase hB
  have hfloor : h_f ≤ st.core.h_j := by
    rw [← hjust.2]
    exact hnhj B hB
  have hhigh : h_f < st.core.h_max := lt_of_le_of_lt hfloor hbelow
  have hupgrade : Block.Preceq F st.core.J :=
    upgrade hnhj hprov hB hjust hsb hcf hBF hRun hfin
  rcases Block.preceq_linear horder hupgrade with hcur | hpast
  · obtain ⟨W, hWb, hmaxW⟩ := hmax
    have hheight : (derive_named S.E S.cfg BF).h_F < (derive_named S.E S.cfg W).h := by
      rw [hfin.2, hmaxW]
      exact hhigh
    have hFW : Block.Preceq F W.erase := by
      have hd := NamedFinalizationBridge.finalized_preceq_of_height_lt S ρ W BF hsb hcf
        (hRun W hWb) hBF hheight
      rwa [hfin.1] at hd
    refine ⟨F, ?_, Block.preceq_self F⟩
    simp only [Protocol.V_tree, Protocol.viable_tree,
      Protocol.finalized_descendants, Protocol.viable, Finset.mem_filter,
      decide_eq_true_eq, Protocol.Store.toHealing]
    refine ⟨⟨hFT, hcur⟩, W.erase, ?_, hFW, ?_⟩
    · rw [hco.1]
      exact Finset.mem_image_of_mem NamedBlock.erase hWb
    · rw [hco.2.2.2.2 W hWb, hmaxW]
      exact Nat.sub_le _ _
  · exact ⟨st.core.F, hviable, hpast⟩



end StoreFinality
end Proofs
end DecoupledConsensusModel

end
