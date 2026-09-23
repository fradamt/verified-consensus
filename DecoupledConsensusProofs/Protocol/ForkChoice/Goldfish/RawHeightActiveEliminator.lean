module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.RawHeightActiveLifecycle
public import DecoupledConsensusProofs.Objects.FixedHeightRootCore
public import DecoupledConsensusProofs.Protocol.ChainState.CheckpointHeights
public import DecoupledConsensusProofs.Protocol.ChainState.FinalityCertificates
public import DecoupledConsensusProofs.Protocol.ChainState.JustificationCertificates
public import DecoupledConsensusProofs.Protocol.Evidence.ProvenanceBridge

@[expose] public section

open DecoupledConsensusModel.Statements.Instantiation

/-!
# Eliminate the strict same-height proposal-root carrier

The declarations are restated over the named carrier. The selected-root
eliminator derives its strict height bound from named store provenance.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
private theorem activeEliminator_ancestor_mem
    {st : Protocol.NamedStore V} (hpc : NamedStore.NamedParentClosed st)
    {A B : NamedBlock V} (hB : B ∈ st.bodies)
    (hAB : NamedBlock.Preceq A B) : A ∈ st.bodies := by
  induction B with
  | genesis =>
      simp only [NamedBlock.Preceq, NamedBlock.preceq,
        decide_eq_true_eq] at hAB
      exact hAB ▸ hB
  | node parent slot root votes support rows proposer ih =>
      simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hAB
      rcases hAB with rfl | hparent
      · exact hB
      · exact ih (hpc.2 _ hB) hparent

omit [DecidableEq V] [Fintype V] in
private theorem activeEliminator_namedGenesis_of_erase
    {B : NamedBlock V} (hB : B.erase = Block.genesis) :
    B = NamedBlock.genesis := by
  cases B with
  | genesis => rfl
  | node parent slot root votes support rows proposer =>
      simp only [NamedBlock.erase] at hB
      exact absurd hB (by simp)

/-- A non-genesis named body selected as an FG root is strictly below the
local maximum height. -/
private theorem selectedFGRoot_deriveHeight_lt_hMax
    (S : Setup V) (rho : Run V) (w : V) (read : Time)
    {R : NamedBlock V}
    (hRmem : R ∈ (rho.storeBeforeTime S w read).bodies)
    (hroot : R.erase = Protocol.get_fg_root
      (rho.storeBeforeTime S w read).core.toHealing.toFG)
    (hne : R ≠ NamedBlock.genesis) :
    (Protocol.derive_named S.E S.cfg R).h <
      (rho.storeBeforeTime S w read).core.h_max := by
  let st := rho.storeBeforeTime S w read
  have hRmem' : R ∈ st.bodies := by simpa only [st] using hRmem
  have hroot' : R.erase = Protocol.get_fg_root st.core.toHealing.toFG := by
    simpa only [st] using hroot
  have hco : Proofs.NamedStore.Coherent S.E S.cfg st :=
    (Proofs.NamedRuntime.stateBeforeTime_invariants S rho read w).1.1.1
  have hbelow : st.core.h_j < st.core.h_max := by
    simpa only [st] using
      NamedJustificationBound.justificationBelowMax_stateBeforeTime
        S rho read w
  by_cases hgate : st.core.h_max = st.core.h_j + 1
  · have hRJ : R.erase = st.core.J := by
      simpa only [Protocol.get_fg_root, Protocol.Store.toHealing,
        if_pos hgate] using hroot'
    obtain ⟨C, hCmem, hCJ, hChj⟩ :=
      Proofs.Bridges.storeJustificationOnChain_stateBeforeTime S rho read w
    have hCmem' : C ∈ st.bodies := by simpa only [st] using hCmem
    have hCJ' : (Protocol.derive_named S.E S.cfg C).J = st.core.J := by
      simpa only [st] using hCJ
    have hChj' :
        (Protocol.derive_named S.E S.cfg C).h_j = st.core.h_j := by
      simpa only [st] using hChj
    rcases NamedCheckpointHeights.justified_ancestor_height
        S.E S.cfg C with hz | ⟨J, hJC, hJerase, hJheight⟩
    · have hJgen : st.core.J = Block.genesis := by
        rw [← hCJ']
        exact NamedJustificationCertificates.justified_zero_is_genesis
          S.E S.cfg C hz
      have hRgen : R = NamedBlock.genesis :=
        activeEliminator_namedGenesis_of_erase (hRJ.trans hJgen)
      exact (hne hRgen).elim
    · have hJmem : J ∈ st.bodies :=
        activeEliminator_ancestor_mem hco.2.2.1 hCmem' hJC
      have hRJerase : R.erase = J.erase :=
        hRJ.trans (hJerase.trans hCJ').symm
      have hRJnamed : R = J :=
        hco.2.1 R hRmem' J hJmem hRJerase
      calc
        (Protocol.derive_named S.E S.cfg R).h =
            (Protocol.derive_named S.E S.cfg J).h := by rw [hRJnamed]
        _ = (Protocol.derive_named S.E S.cfg C).h_j := hJheight
        _ = st.core.h_j := hChj'
        _ < st.core.h_max := hbelow
  · have hRF : R.erase = st.core.F := by
      simpa only [Protocol.get_fg_root, Protocol.Store.toHealing,
        if_neg hgate] using hroot'
    obtain ⟨C, hCmem, hCF, hCFbelow⟩ :=
      Proofs.Bridges.storeFinalizationOnChain_stateBeforeTime S rho read w
    have hCmem' : C ∈ st.bodies := by simpa only [st] using hCmem
    have hCF' : (Protocol.derive_named S.E S.cfg C).F = st.core.F := by
      simpa only [st] using hCF
    have hCFbelow' :
        (Protocol.derive_named S.E S.cfg C).h_F < st.core.h_max := by
      simpa only [st] using hCFbelow
    rcases NamedCheckpointHeights.finalized_ancestor_height
        S.E S.cfg C with hz | ⟨F, hFC, hFerase, hFheight⟩
    · have hFgen : st.core.F = Block.genesis := by
        rw [← hCF']
        exact NamedFinalityCertificates.finalized_zero_is_genesis
          S.E S.cfg C hz
      have hRgen : R = NamedBlock.genesis :=
        activeEliminator_namedGenesis_of_erase (hRF.trans hFgen)
      exact (hne hRgen).elim
    · have hFmem : F ∈ st.bodies :=
        activeEliminator_ancestor_mem hco.2.2.1 hCmem' hFC
      have hRFerase : R.erase = F.erase :=
        hRF.trans (hFerase.trans hCF').symm
      have hRFnamed : R = F :=
        hco.2.1 R hRmem' F hFmem hRFerase
      calc
        (Protocol.derive_named S.E S.cfg R).h =
            (Protocol.derive_named S.E S.cfg F).h := by rw [hRFnamed]
        _ = (Protocol.derive_named S.E S.cfg C).h_F := hFheight
        _ < st.core.h_max := hCFbelow'

/-- The strict same-height proposal-root carrier is impossible. -/
theorem activeExactHeightProposalRootCarrierAt_false
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {H : Height} {q : Round} {endpoint : Time}
    {source root : NamedBlock V}
    (h : ActiveExactHeightProposalRootCarrierAt
      S rho H q endpoint source root) :
    False := by
  let s := S.hc.opening_slot q
  let proposer := S.E.proposer s
  let read := Protocol.proposal_time S.E s
  let pre := rho.storeBeforeTime S proposer read
  have hrootNe : root ≠ NamedBlock.genesis := by
    intro hroot
    subst root
    have hstrict := h.sourceStrictRoot
    change (!decide (source.erase = Block.genesis) &&
      Block.preceq source.erase Block.genesis) = true at hstrict
    rw [Bool.and_eq_true] at hstrict
    have hsourceNe : source.erase ≠ Block.genesis := by
      simpa using hstrict.1
    have hsourceGen : source.erase = Block.genesis :=
      Block.preceq_antisymm hstrict.2 (Protocol.preceq_genesis source.erase)
    exact hsourceNe hsourceGen
  have hrootEq : root.erase =
      Protocol.get_fg_root pre.core.toHealing.toFG := by
    simpa only [pre, proposer, read, s, proposerReadAt,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock] using h.root_eq
  have hrootBelow :
      (Protocol.derive_named S.E S.cfg root).h < pre.core.h_max :=
    selectedFGRoot_deriveHeight_lt_hMax
      S rho proposer read (by simpa only [pre, proposer, read, s] using
        h.rootProcessed) hrootEq hrootNe
  have hpreCap : pre.core.h_max ≤ H := by
    exact (storeBeforeTime_hMax_le_storeAt
      S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed proposer read).trans
      ((stateAt_h_max_mono
        S adm.toNamedAdmissibleCore.toNamedScheduleWellFormed proposer
          (h.proposalRead_le_action.trans h.action_le_endpoint)).trans
        ((localHMax_le_honestHMaxAt S rho endpoint h.proposerHonest).trans
          h.endpointCap))
  have hlt : H < H := by
    calc
      H = (Protocol.derive_named S.E S.cfg root).h :=
        h.rootExactHeight.symm
      _ < pre.core.h_max := hrootBelow
      _ ≤ H := hpreCap
  exact (lt_irrefl H hlt)

#print axioms activeExactHeightProposalRootCarrierAt_false

/-- The named active exact-height lifecycle has only public progress or fixed
interference after the strict selected-root carrier is eliminated. -/
theorem activeExactHeightOpening_fixedInterference_or_hMaxRise
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {H : Height} {q : Round} {source : NamedBlock V} {endpoint : Time}
    (hq : 0 < q)
    (hcarrier : ProposerCarrierAt S rho q)
    (hformsPrev : NamedGradeFormsAt S rho (q - 1) source.erase)
    (hwindowPrev : ∀ w ∈ rho.honest,
      FinalityFilterRetainedAtRead S rho w (S.a (q - 1)) source.erase)
    (hdomainWindow : ∀ w ∈ rho.honest,
      FinalityFilterRetainedAtRead S rho w
        (DecoupledConsensusModel.Protocol.domain S.E S.hc q .g2) source.erase)
    (hsourceRun : RunBlock S rho source)
    (hsourceHeight :
      (Protocol.derive_named S.E S.cfg source).h = H)
    (hpostPrev : S.E.t_GST ≤ S.a (q - 1))
    (hmature : ProposalTimeoutMatureAt
      S rho (S.hc.opening_slot q))
    (hactiveAtAction : ∀ w ∈ rho.honest,
      source.erase ∈ Protocol.get_filtered_block_tree
        (healStoreAt S rho w q).toFG)
    (hactionEnd : S.a q ≤ endpoint)
    (hendHor : endpoint ≤ rho.horizon) :
    H < honestHMaxAt S rho endpoint ∨
      (FixedHeightRootInterferenceAtRead S rho H
          (S.E.proposer (S.hc.opening_slot q))
          (Protocol.proposal_time S.E (S.hc.opening_slot q))
          source.erase ∧
        Protocol.proposal_time S.E (S.hc.opening_slot q) ≤ S.a q ∧
        S.a q ≤ endpoint ∧ endpoint ≤ rho.horizon) := by
  rcases activeExactHeightOpeningLifecycle_or_hMaxRise
      S adm hfb hq hcarrier hformsPrev hwindowPrev hdomainWindow
        hsourceRun hsourceHeight hpostPrev hmature hactiveAtAction
        hactionEnd hendHor with
    hrise | hfixed | ⟨root, hroot⟩
  · exact Or.inl hrise
  · exact Or.inr hfixed
  · exact False.elim
      (activeExactHeightProposalRootCarrierAt_false S adm hroot)

#print axioms activeExactHeightOpening_fixedInterference_or_hMaxRise



/-
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.RawHeightActiveLifecycle
public import DecoupledConsensusProofs.Objects.FixedHeightRootCore

/-!
# Eliminate the strict same-height proposal-root carrier

The final arm of the active exact-height lifecycle classification is internally
inconsistent: a non-genesis selected FG root is strictly below the local
frontier, while the carrier's endpoint cap places that frontier at or below
the root's exact height.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol
open Proofs.HealingLemmas

variable {V: Type} [DecidableEq V] [Fintype V]

/-- The strict same-height proposal-root carrier is impossible. -/
theorem activeExactHeightProposalRootCarrierAt_false
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    {H: Height} {q: Round} {endpoint: Time} {source root: Block V}
    (h: ActiveExactHeightProposalRootCarrierAt S rho H q endpoint source root):
    False:= by
  let s:= S.hc.opening_slot q
  let proposer:= S.E.proposer s
  let read:= Protocol.proposal_time S.E s
  let pre:= rho.storeBeforeTime S proposer read
  let duty:= Protocol.proposerDutyStore S rho s
  have hdep: DepReachableStore S.E S.hc S.cfg (S.node proposer) pre:= by
    simpa only [pre, proposer, read, Run.storeBeforeTime] using
      (Proofs.Bridges.depReachable_stateBeforeTime S adm.toScheduleWellFormed
        adm.toDeliveryWellFormed read proposer)
  have hrootNe: root ≠ Block.genesis:= by
    intro hroot
    subst root
    have hstrict:= h.sourceStrictRoot
    cases source <;> simp [Block.Prec, Block.prec, Block.preceq] at hstrict
  have hrootBelow: (derived_state S.E S.cfg root).h < duty.h_max:= by
    have hpreBelow:= FixedHeightRootCore.getFGRoot_derivedHeight_lt_hMax_depReachable
      S.E S.hc S.cfg (S.node proposer) hdep (by
        simpa only [duty, Protocol.proposerDutyStore, Proofs.Optimistic.tickStore,
          pre, proposer, read, s, h.root_eq] using hrootNe)
    simpa only [duty, Protocol.proposerDutyStore, Proofs.Optimistic.tickStore,
      pre, proposer, read, s, h.root_eq] using hpreBelow
  have hdutyCap: duty.h_max ≤ H:= by
    have hpreCap: pre.h_max ≤ H:= by
      exact (storeBeforeTime_hMax_le_storeAt
        S adm.toScheduleWellFormed proposer read).trans
        ((stateAt_h_max_mono S adm.toScheduleWellFormed proposer
          (h.proposalRead_le_action.trans h.action_le_endpoint)).trans
          ((localHMax_le_honestHMaxAt S rho endpoint h.proposerHonest).trans
            h.endpointCap))
    simpa only [duty, Protocol.proposerDutyStore, Proofs.Optimistic.tickStore,
      pre] using hpreCap
  have hlt: H < H:= by
    calc
      H = (derived_state S.E S.cfg root).h:= h.rootExactHeight.symm
      _ < duty.h_max:= hrootBelow
      _ ≤ H:= hdutyCap
  exact (lt_irrefl H hlt)

/-- The active exact-height opening lifecycle has only the public progress or
fixed-interference alternatives. -/
theorem activeExactHeightOpening_fixedInterference_or_hMaxRise
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hfb: BelowOneThird S rho.honest)
    {H: Height} {q: Round} {source: Block V} {endpoint: Time}
    (hq: 0 < q)
    (hcarrier: ProposerCarrierAt S rho q)
    (hformsPrev: GradeFormsAt S rho (q - 1) source)
    (hsourceHeight: (derived_state S.E S.cfg source).h = H)
    (hpostPrev: S.E.t_GST ≤ S.a (q - 1))
    (hmature: ProposalTimeoutMatureAt
      S rho (S.hc.opening_slot q))
    (hactiveAtAction: ∀ w ∈ rho.honest,
      source ∈ Protocol.get_filtered_block_tree
        (healStoreAt S rho w q).toFG)
    (hactionEnd: S.a q ≤ endpoint)
    (hendHor: endpoint ≤ rho.horizon):
    H < honestHMaxAt S rho endpoint ∨
      (FixedHeightRootInterferenceAtRead S rho H
          (S.E.proposer (S.hc.opening_slot q))
          (Protocol.proposal_time S.E (S.hc.opening_slot q)) source ∧
        Protocol.proposal_time S.E (S.hc.opening_slot q) ≤ S.a q ∧
        S.a q ≤ endpoint ∧ endpoint ≤ rho.horizon):= by
  rcases activeExactHeightOpeningLifecycle_or_hMaxRise S adm hfb hq hcarrier
    hformsPrev hsourceHeight hpostPrev hmature hactiveAtAction hactionEnd
      hendHor with
    hrise | hfixed | hroot
  · exact Or.inl hrise
  · exact Or.inr hfixed
  · obtain ⟨root, hroot⟩:= hroot
    exact False.elim
      (activeExactHeightProposalRootCarrierAt_false S adm hroot)

end HealingSurface
end Proofs
end DecoupledConsensusModel
-/

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
