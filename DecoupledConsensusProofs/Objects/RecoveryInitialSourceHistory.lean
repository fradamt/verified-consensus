module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.GoldfishCone
public import DecoupledConsensusProofs.Protocol.Grades.RecoveryCapturedSlotInterval
public import DecoupledConsensusProofs.Protocol.Grades.RecoveryFGSelectorPrefixSeed
public import DecoupledConsensusProofs.Protocol.ForkChoice.Head.RecoveryFGAnchor
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.RecoveryFGSourceFrame
public import DecoupledConsensusProofs.Protocol.Schedule.SeedBoundaryConeLead
public import DecoupledConsensusProofs.Protocol.Grades.SeedFinalizedCanonical
public import DecoupledConsensusProofs.Execution.SeedGradeExistence
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge
public import DecoupledConsensusProofs.Execution.Wire
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SGCompatibleHistory
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.SGCompatibleBootstrap
public import DecoupledConsensusProofs.Protocol.Schedule.RecoveryHandoffCore
public import DecoupledConsensusProofs.Protocol.Schedule.WeakGoldfishCone
public import DecoupledConsensusProofs.Protocol.Grades.RecoveryGenuineClearNextVote
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.WeakConfirmationSupport
public import DecoupledConsensusProofs.Protocol.Grades.WeakBootstrapSG
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.WeakBootstrapGradePersistence
public import DecoupledConsensusProofs.Protocol.Grades.WeakBootstrapAction
public import DecoupledConsensusProofs.Protocol.Store.WeakSGHistory
public import DecoupledConsensusProofs.Protocol.Grades.Q31_actionSGBlock_tiers
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.HeightRegimeFrameBase

@[expose] public section



namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol
open Proofs.Optimistic
open Proofs.HealingLemmas

variable {V : Type} [DecidableEq V] [Fintype V]











/-! ## Named frame-side history assembly

The action-read invariant and the vote-duty wrapper use different prepared
reads. Keep that distinction explicit at this boundary. The two callbacks
below are the audited pre-building interfaces for the missing read transport
and same-round SG successor. They do not identify an action read with a vote
duty read.
-/

theorem PrefixFGSelectorConeAt.checkpointProtection_and_actionHistory_of_frameN
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hbelow : BelowOneThird S rho.honest)
    {start first : Nat} {blocked : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg : NamedBlock V} {T : Block V}
    (hseed : PrefixFGSelectorConeAt S rho start first blocked i a ta Cfg T)
    (hfirst : HeightWindowAt S rho (blocked + 1) first)
    {Tprev : NamedBlock V} {c0 : Round}
    (hframe : HeightRegimeFrameN S rho blocked (first - 1) Tprev c0)
    (hc0 : c0 ≤ a.round)
    (ready : GradeRoundReady S rho a.round)
    (hpostPrev : S.E.t_GST ≤ S.a (a.round - 1))
    (hK6Q2 : PhaseGrades.nodeQ2
      S (actionReadAt S rho a.val_index a.round) a.round = some Cfg.erase →
      VoterAnchorSourceQ2Inputs S rho a.round a.val_index Cfg.erase)
    (hK6Clear : PhaseGrades.nodeQ2
      S (actionReadAt S rho a.val_index a.round) a.round ≠ some Cfg.erase →
      VoterAnchorSourceClearInputs S rho a.round a.val_index Cfg.erase)
    (_hminimal : ∀ (b : NamedAttestation V) (tb : Time),
      b.val_index ∈ rho.honest →
      NamedRun.emits S rho b.val_index (Object.attest b) tb →
      b.height_pair.erase.height? = some (blocked + 1) → a.round ≤ b.round)
    {c : Round} (hc : a.round + 1 ≤ c)
    (hwindow : RecoverySGWindowInvariant S rho (c - 1) T)
    (hopening :
      (∀ w ∈ rho.honest,
        Block.Preceq T
          (voterHeadAt S rho w (S.hc.opening_slot c))) ∧
      NamedHonestVotesCone S rho (S.hc.opening_slot c)
        (fun X => Block.Preceq T X))
    (hsg_of_frameN : HonestSGEmissionsCompatibleAtRound S rho c T)
    (hread_of_delivery : ∀ w ∈ rho.honest,
      PreviousSGReadSideAt S rho w (c + 1) T)
    (hfgWitness_of_frameN : ∀ w ∈ rho.honest, ∀ W,
      fgConfirmationWitness S (actionStoreAt S rho w c) = some W →
        Block.compatible W T = true)
    (hhistory_of_invariant : ∀ {d : Slot},
      S.hc.opening_slot c ≤ d → d < S.hc.opening_slot (c + 1) →
      ∀ w ∈ rho.honest,
        previousSGWindowHistory S rho w
          (Internal.NamedRecoveryRead.voteDutyRead S rho w (d + 1))
          (S.hc.round_of (d + 1)) T)
    (hgoldfish_of_previousSGHistory_of_frameN : ∀ {d : Slot},
      S.hc.opening_slot c ≤ d → d < S.hc.opening_slot (c + 1) →
      Protocol.vote_time S.E d + S.E.Δ ≤ rho.horizon →
      (∀ w ∈ rho.honest,
        Block.Preceq T (voterHeadAt S rho w d)) ∧
      NamedHonestVotesCone S rho d (fun X => Block.Preceq T X) →
      (∀ w ∈ rho.honest,
        previousSGWindowHistory S rho w
          (Internal.NamedRecoveryRead.voteDutyRead S rho w (d + 1))
          (S.hc.round_of (d + 1)) T) →
      (∀ w ∈ rho.honest,
        Block.Preceq T (voterHeadAt S rho w (d + 1))) ∧
      NamedHonestVotesCone S rho (d + 1) (fun X => Block.Preceq T X)) :
    (∀ s, S.hc.round_of s = c →
      Protocol.vote_time S.E s + S.E.Δ ≤ rho.horizon →
      (∀ w ∈ rho.honest, Block.Preceq T (voterHeadAt S rho w s)) ∧
        NamedHonestVotesCone S rho s (fun X => Block.Preceq T X)) ∧
    (S.a c ≤ rho.horizon →
      RecoverySGWindowInvariant S rho c T ∧
      ∀ w ∈ rho.honest, ∀ W,
        fgConfirmationWitness S (actionStoreAt S rho w c) = some W →
          Block.compatible W T = true) := by
  have hcpos : 1 ≤ c :=
    (Nat.succ_le_succ (Nat.zero_le a.round)).trans hc
  have hcpred : c - 1 + 1 = c := Nat.sub_add_cancel hcpos
  have hopen : 0 < S.hc.opening_slot c := by
    exact Nat.mul_pos (Nat.zero_lt_of_lt hcpos)
      (Nat.zero_lt_of_lt S.hc.R_ge_two)
  have hslots : ∀ s, S.hc.round_of s = c →
      Protocol.vote_time S.E s + S.E.Δ ≤ rho.horizon →
      (∀ w ∈ rho.honest, Block.Preceq T (voterHeadAt S rho w s)) ∧
        NamedHonestVotesCone S rho s (fun X => Block.Preceq T X) := by
    intro s hround hhor
    have hslo : S.hc.opening_slot c ≤ s := by
      rw [← hround]
      exact Nat.div_mul_le_self s S.hc.R
    have hshi : s < S.hc.opening_slot (c + 1) := by
      apply (Nat.div_lt_iff_lt_mul (Nat.zero_lt_of_lt S.hc.R_ge_two)).mp
      change S.hc.round_of s < c + 1
      rw [hround]
      exact Nat.lt_succ_self _
    have hfold : ∀ d, S.hc.opening_slot c ≤ d → d ≤ s →
        (∀ w ∈ rho.honest,
          Block.Preceq T (voterHeadAt S rho w d)) ∧
          NamedHonestVotesCone S rho d (fun X => Block.Preceq T X) := by
      intro d hdlo
      induction d, hdlo using Nat.le_induction with
      | base =>
          intro _
          exact hopening
      | succ d hd ih =>
          intro hds
          have hprev := ih (Nat.le_of_succ_le hds)
          have htime := vote_time_mono_slots S.E
            ((Nat.le_succ d).trans hds)
          have hnextHor : Protocol.vote_time S.E d + S.E.Δ ≤ rho.horizon := by
            exact (add_le_add htime (le_refl S.E.Δ)).trans hhor
          have hdhi : d < S.hc.opening_slot (c + 1) :=
            Nat.lt_trans (Nat.lt_succ_self d) (hds.trans_lt hshi)
          exact hgoldfish_of_previousSGHistory_of_frameN
            hd hdhi hnextHor hprev
            (hhistory_of_invariant hd hdhi)
    exact hfold s hslo (le_refl s)
  refine ⟨hslots, ?_⟩
  intro hhor
  have hsg : HonestSGEmissionsCompatibleAtRound S rho c T := hsg_of_frameN
  have hinv : RecoverySGWindowInvariant S rho c T := by
    refine ⟨?_, ?_⟩
    · intro k hk
      by_cases hkc : k = c
      · simpa only [hkc] using hsg
      · have hlt : k < c := Nat.lt_of_le_of_ne hk hkc
        exact hwindow.1 k (Nat.le_sub_one_of_lt hlt)
    · intro r hr w hw
      by_cases hrc : r ≤ c
      · exact hwindow.2 r (by simpa only [hcpred] using hrc) w hw
      · have hrc' : r = c + 1 := by
          apply Nat.le_antisymm hr
          exact Nat.succ_le_of_lt (Nat.lt_of_not_ge hrc)
        simpa only [hrc'] using hread_of_delivery w hw
  exact ⟨hinv, hfgWitness_of_frameN⟩

#print axioms PrefixFGSelectorConeAt.checkpointProtection_and_actionHistory_of_frameN

theorem PrefixFGSelectorConeAt.laterFGWitness_eq_or_extends_checkpoint_of_frameN
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    (_hcom : HonestCommittees S rho.honest)
    (_hbelow : BelowOneThird S rho.honest)
    {start first : Nat} {blocked : Height}
    {i : Nat} {a : NamedAttestation V} {ta : Time}
    {Cfg0 : NamedBlock V} {T0 : Block V}
    (hseed : PrefixFGSelectorConeAt S rho start first blocked i a ta Cfg0 T0)
    (_hfirst : HeightWindowAt S rho (blocked + 1) first)
    {Tprev : NamedBlock V} {c0 : Round}
    (_hframe : NamedHeightRegimeFrame S rho blocked (first - 1) Tprev c0)
    (_hc0 : c0 ≤ a.round)
    (_ready : GradeRoundReady S rho a.round)
    (_hpostPrev : S.E.t_GST ≤ S.a (a.round - 1))
    (_hminimal : ∀ (b : NamedAttestation V) (tb : Time),
      b.val_index ∈ rho.honest →
      NamedRun.emits S rho b.val_index (Object.attest b) tb →
      b.height_pair.erase.height? = some (blocked + 1) → a.round ≤ b.round)
    {Tnext : NamedBlock V}
    (hTnextCfg : NamedBlock.Preceq Tnext Cfg0)
    (hTnextRun : RunBlock S rho Tnext)
    (hTnextErase : Tnext.erase =
      (Protocol.derive_named S.E S.cfg Cfg0).T_h)
    (hTnextHeight :
      (Protocol.derive_named S.E S.cfg Tnext).h = blocked + 1)
    {r : Round} (_hr : a.round + 1 ≤ r) (_hhor : S.a r ≤ rho.horizon)
    {w : V} (hw : w ∈ rho.honest) {Cfg : NamedBlock V}
    (hCfgMem : Cfg ∈ (actionStoreAt S rho w r).st.bodies)
    (_hW : fgConfirmationWitness S (actionStoreAt S rho w r) =
      some (Protocol.derive_named S.E S.cfg Cfg).T_h)
    (hcompat : Block.compatible
      (Protocol.derive_named S.E S.cfg Cfg).T_h Tnext.erase = true) :
    ((Protocol.derive_named S.E S.cfg Cfg).h = blocked + 1 →
      (Protocol.derive_named S.E S.cfg Cfg).T_h = Tnext.erase) ∧
    (blocked + 1 ≤ (Protocol.derive_named S.E S.cfg Cfg).h →
      Block.Preceq Tnext.erase
        (Protocol.derive_named S.E S.cfg Cfg).T_h) := by
  obtain ⟨K, _hKmem, hKerase, hKheight, hKCfg, hKrun⟩ :=
    action_named_checkpoint S adm hw hCfgMem
  have hKfixed : (Protocol.derive_named S.E S.cfg K).T_h = K.erase := by
    exact (Proofs.NamedEntryHeight.entry_eq_on_plateau S.E S.cfg hKCfg hKheight).trans
      hKerase.symm
  have hTnextFixed :
      (Protocol.derive_named S.E S.cfg Tnext).T_h = Tnext.erase := by
    have hplateau := Proofs.NamedEntryHeight.entry_eq_on_plateau S.E S.cfg hTnextCfg
      (hTnextHeight.trans hseed.sourceDerivedHeight.symm)
    exact hplateau.trans hTnextErase.symm
  have hnamed : NamedBlock.Preceq K Tnext ∨ NamedBlock.Preceq Tnext K := by
    have hraw : Block.Preceq K.erase Tnext.erase ∨
        Block.Preceq Tnext.erase K.erase := by
      rw [hKerase]
      simpa only [Block.compatible, Bool.or_eq_true] using hcompat
    rcases hraw with hKT | hTK
    · exact Or.inl (Protocol.namedPreceq_of_runBlock_erase_preceq
        adm hKrun hTnextRun hKT)
    · exact Or.inr (Protocol.namedPreceq_of_runBlock_erase_preceq
        adm hTnextRun hKrun hTK)
  have heq : (Protocol.derive_named S.E S.cfg Cfg).h = blocked + 1 →
      (Protocol.derive_named S.E S.cfg Cfg).T_h = Tnext.erase := by
    intro hh
    have hheights : (Protocol.derive_named S.E S.cfg K).h =
        (Protocol.derive_named S.E S.cfg Tnext).h :=
      hKheight.trans (hh.trans hTnextHeight.symm)
    rcases hnamed with hKT | hTK
    · calc
        (Protocol.derive_named S.E S.cfg Cfg).T_h = K.erase := hKerase.symm
        _ = (Protocol.derive_named S.E S.cfg K).T_h := hKfixed.symm
        _ = (Protocol.derive_named S.E S.cfg Tnext).T_h :=
          Proofs.NamedEntryHeight.entry_eq_on_plateau S.E S.cfg hKT hheights
        _ = Tnext.erase := hTnextFixed
    · calc
        (Protocol.derive_named S.E S.cfg Cfg).T_h = K.erase := hKerase.symm
        _ = (Protocol.derive_named S.E S.cfg K).T_h := hKfixed.symm
        _ = (Protocol.derive_named S.E S.cfg Tnext).T_h :=
          (Proofs.NamedEntryHeight.entry_eq_on_plateau S.E S.cfg hTK hheights.symm).symm
        _ = Tnext.erase := hTnextFixed
  refine ⟨heq, ?_⟩
  intro hheight
  rcases hnamed with hKT | hTK
  · have hupper := Proofs.NamedEntryHeight.derive_height_mono S.E S.cfg hKT
    have hh : (Protocol.derive_named S.E S.cfg Cfg).h = blocked + 1 := by
      apply Nat.le_antisymm
      · exact hKheight.symm.le.trans (hupper.trans hTnextHeight.le)
      · exact hheight
    rw [heq hh]
    exact Block.preceq_self Tnext.erase
  · rw [← hKerase]
    exact Proofs.NamedWire.erase_preceq hTK

#print axioms PrefixFGSelectorConeAt.laterFGWitness_eq_or_extends_checkpoint_of_frameN

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
