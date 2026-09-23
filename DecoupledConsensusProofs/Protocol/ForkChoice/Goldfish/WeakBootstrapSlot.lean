module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.WeakBootstrapJoin
public import DecoupledConsensusProofs.Protocol.Grades.WeakBootstrapSG
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.WeakBootstrapGradePersistence
public import DecoupledConsensusProofs.Protocol.Grades.SafetySlotInduction
public import DecoupledConsensusProofs.Protocol.Grades.RelativeSupporter
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.PreparedVoteDutyPackage
public import DecoupledConsensusProofs.Protocol.ForkChoice.Views.WeakConfirmationHead

@[expose] public section

/-! # Common safety slot induction with an independent history cutoff
The finite bootstrap and protected seed start the fold. Each successor step
preserves previous confirmations and adopts new ones. SG and FG source safety
comes from the inner action induction. The previous-frontier input keeps timeout
witnesses and does not require a common height frontier.
The bootstrap inputs still require an export and transfer proof. They are
not extra assumptions accepted by the final healing theorem.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace WeakJoint

open Internal Execution Protocol Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]






/-- Compatible semantic SG history supplies the prepared batch at a vote-duty
read. open is separate because this statement only controls inputs that
the reader has already interpreted. -/
theorem batchCompatibleAt_of_historyCutEmissions
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {d : Slot} {w : V} (hw : w ∈ rho.honest) {B : Block V}
    (hhistory : ∀ k ∈ Protocol.latest_window S.hc.η_SG (S.hc.round_of d),
      HonestSGEmissionsCompatibleAtRound S rho k B) :
    Internal.PhaseGrades.BatchCompatibleAt S.hc
      (Internal.NamedRecoveryRead.voteDutyRead S rho w d).st.core.toHealing.gradeView
      (Internal.NamedRecoveryRead.voteDutyRead S rho w d).st.core.F
      rho.honest (S.hc.round_of d)
      (DecoupledConsensusModel.Protocol.late S.E S.hc (S.hc.round_of d) .g1) B := by
  intro v hv u hu head hconfirmed hfind
  have hraw := (Finset.mem_filter.mp hu).1
  simp only [DecoupledConsensusModel.Protocol.rawInputs, Finset.mem_filter] at hraw
  obtain ⟨k, hk, huk⟩ := Finset.mem_biUnion.mp hraw.1
  have hk' : k ∈ Protocol.latest_window S.hc.η_SG (S.hc.round_of d) :=
    List.mem_toFinset.mp hk
  have hroot := WeakSG.rootCompatible_of_emittedSGHistory_at_read S adm hw
    (hhistory k hk') (by
      simpa only [Internal.NamedRecoveryRead.voteDutyRead,
        NamedActionReads.confirmationReadAt,
        NamedActionReads.confirmationReadFrom,
        Protocol.NamedStore.setClock] using huk) (hraw.2.1 ▸ hv)
  have hfind' : Block.find?
      (rho.storeBeforeTime S w (Protocol.vote_time S.E d)).T head.root = some head := by
    simpa only [Internal.NamedRecoveryRead.voteDutyRead,
      NamedActionReads.confirmationReadAt,
      NamedActionReads.confirmationReadFrom,
      Protocol.NamedStore.setClock] using hfind
  simp only [Proofs.HealingLemmas.rootCompatible, hconfirmed, hfind'] at hroot
  simpa only [Block.compatible, Bool.or_comm] using hroot

#print axioms batchCompatibleAt_of_historyCutEmissions






/-
/-- Relevant old height rows have compatible witnesses, including timeouts. -/
abbrev NoOldFrontierAtCut (S: Setup V) (rho: Run V) (cut: Round)
    (start last: Slot) (P: Block V): Prop:=
  ∀ e: Slot, start < e → e ≤ last + 1 →
  ∀ B: Block V, Block.Preceq P B →
  ∀ w ∈ rho.honest,
  (derived_state S.E S.cfg B).h < (voteDutyStore S rho w e).h_max - 1 →
  ∀ (a: NamedAttestation V) (ta: Time) (T: Block V),
  a.val_index ∈ rho.honest → NamedRun.emits S rho a.val_index (Object.attest a) ta →
  ta < Protocol.vote_time S.E e →
  a.height_pair.erase.height? = some ((voteDutyStore S rho w e).h_max - 1) →
  a.round < cut →
  fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) = some T →
    Block.compatible B T = true
-/

/-- Relevant old height rows have compatible named witnesses, including timeouts. -/
abbrev NoOldFrontierAtCut (S : Setup V) (rho : Run V) (cut : Round)
    (start last : Slot) (P : Block V) : Prop :=
  ∀ e : Slot, start < e → e ≤ last + 1 →
  ∀ (C : NamedBlock V), Block.Preceq P C.erase →
  ∀ w ∈ rho.honest,
  (Protocol.derive_named S.E S.cfg C).h <
      (Proofs.Optimistic.voteDutyStore S rho w e).h_max - 1 →
  ∀ (a : NamedAttestation V) (ta : Time) (K : NamedBlock V),
  a.val_index ∈ rho.honest → NamedRun.emits S rho a.val_index (Object.attest a) ta →
  ta < Protocol.vote_time S.E e →
  a.height_pair.erase.height? = some
    ((Proofs.Optimistic.voteDutyStore S rho w e).h_max - 1) →
  a.round < cut →
  fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) =
    some (Protocol.derive_named S.E S.cfg K).T_h →
  NamedBlock.compatible C K = true

/- The prepared successor has exactly the two fields of ProtectedVoteSlot. -/


















theorem protectedVoteSlots_of_historyCut_of_delivery_v2
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {cap : Time} (hdelivery : NamedHealthyPrefixDelivery S rho cap)
    (hcapHor : cap ≤ rho.horizon)
    (hcom : HonestCommittees S rho.honest)
    (hmajority : HonestWeightMajority S rho.honest)
    {base cut : Round} {start last : Slot} {P : Block V}
    (hspan : base ≤ cut - S.hc.η_SG)
    (hstartpos : 0 < start)
    (hsettled : S.hc.opening_slot cut ≤ start)
    (hcap : Protocol.confirmation_time S.E last ≤ cap)
    (hhor : Protocol.confirmation_time S.E last ≤ rho.horizon)
    (hseed : ProtectedVoteSlot S rho start P)
    (hnoOldFrontier : NoOldFrontierAtCut S rho cut start last P)
    (hsgBoot : ∀ r, base ≤ r → r < cut → ∀ w ∈ rho.honest,
      NamedRun.emits S rho w
        (Object.attest (actionAttestationAt S rho w r)) (S.a r) →
      Block.Preceq (actionSGBlockAt S rho w r) P)
    (hconfBoot : ∀ q, S.hc.opening_slot cut ≤ q → q < start →
      ∀ w ∈ rho.honest, ∀ B,
      GenuineConfirmationWith
        (NamedProfile.gradeContract
          (Internal.NamedRecoveryRead.confirmationInputRead S rho w q).cache)
        S.E S.hc (confStore S rho w q) q B →
      Block.Preceq B P)
    (hlegacyActionRoots : ∀ r, cut ≤ r →
      S.a r < Protocol.vote_time S.E (last + 1) → ∀ w ∈ rho.honest,
      ∀ (C : NamedBlock V) (a : NamedAttestation V),
      let R := Protocol.get_fg_root
        (actionStoreAt S rho w r).st.core.toHealing.toFG
      C ∈ (actionStoreAt S rho w r).st.bodies →
      (Protocol.derive_named S.E S.cfg C).J = R →
      a.val_index ∈ rho.honest →
      NamedRun.emits S rho a.val_index (Object.attest a) (S.a a.round) →
      a.round < cut →
      a.height_pair.erase = HeightPair.target
        (Protocol.derive_named S.E S.cfg C).h_j
        (Protocol.derive_named S.E S.cfg C).J.root →
      fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) =
        some R →
      Block.Preceq R P)
    (hlegacyReadRoots : ∀ d, start < d → d ≤ last + 1 →
      ∀ w ∈ rho.honest,
      ∀ (C : NamedBlock V) (a : NamedAttestation V) (ta : Time),
      let R := Protocol.get_fg_root
        (voteDutyStore S rho w d).toHealing.toFG
      C ∈ (rho.storeBeforeTime S w (Protocol.vote_time S.E d)).bodies →
      (Protocol.derive_named S.E S.cfg C).J = R →
      a.val_index ∈ rho.honest →
      NamedRun.emits S rho a.val_index (Object.attest a) ta →
      ta < Protocol.vote_time S.E d →
      a.round < cut →
      a.height_pair.erase = HeightPair.target
        (Protocol.derive_named S.E S.cfg C).h_j
        (Protocol.derive_named S.E S.cfg C).J.root →
      fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) =
        some R →
      Block.Preceq R P)
    (hwindow : ∀ r, cut ≤ r → 0 < r →
      S.a r < Protocol.vote_time S.E (last + 1) →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hreadWindowV2 : ∀ d, start < d → d ≤ last + 1 →
      0 < S.hc.round_of d →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG (S.hc.round_of d))
    (hcapDomainV2 : ∀ r, cut ≤ r → 0 < r →
      S.a r < Protocol.vote_time S.E (last + 1) → ∀ p,
      DecoupledConsensusModel.Protocol.domain S.E S.hc r p ≤ cap) :
    ∀ d, start ≤ d → d ≤ last + 1 →
      ProtectedVoteSlot S rho d P ∧
      (∀ q, S.hc.opening_slot cut ≤ q → q < d →
        ∀ w ∈ rho.honest, ∀ B,
        GenuineConfirmationWith
          (NamedProfile.gradeContract
            (Internal.NamedRecoveryRead.confirmationInputRead S rho w q).cache)
          S.E S.hc (confStore S rho w q) q B →
          ProtectedVoteSlot S rho d B) := by
  have hRpos : 0 < S.hc.R :=
    lt_of_lt_of_le (by decide : 0 < 2) S.hc.R_ge_two
  have hconfHor : ∀ k, k ≤ last →
      Protocol.confirmation_time S.E k ≤ rho.horizon := by
    intro k hk
    apply le_trans ?_ hhor
    rw [Protocol.confirmation_time_eq_support_cutoff_succ,
      Protocol.confirmation_time_eq_support_cutoff_succ]
    exact support_cutoff_mono S.E (Nat.add_le_add_right hk 1)
  have hconfCap : ∀ k, k ≤ last →
      Protocol.confirmation_time S.E k ≤ cap := by
    intro k hk
    apply le_trans ?_ hcap
    rw [Protocol.confirmation_time_eq_support_cutoff_succ,
      Protocol.confirmation_time_eq_support_cutoff_succ]
    exact support_cutoff_mono S.E (Nat.add_le_add_right hk 1)
  intro d hd
  induction d, hd using Nat.le_induction with
  | base =>
      intro hupper
      exact ⟨hseed, fun q hq hqd w hw B hB =>
        hseed.of_ancestor (hconfBoot q hq hqd w hw B hB)⟩
  | succ d hd ih =>
      intro hupper
      have hdlast : d ≤ last := Nat.le_of_succ_le_succ hupper
      have hprev := ih (hdlast.trans (Nat.le_succ last))
      have hdpos : 0 < d := hstartpos.trans_le hd
      have hnext : start < d + 1 := Nat.lt_succ_of_le hd
      have hgap : cut ≤ S.hc.round_of (d + 1) := by
        change cut ≤ (d + 1) / S.hc.R
        exact (Nat.le_div_iff_mul_le hRpos).2
          (hsettled.trans (hd.trans (Nat.le_succ d)))
      have htimeMax := vote_time_mono_slots S.E (Nat.add_le_add_right hdlast 1)
      have htimeLift : ∀ {t : Time}, t < Protocol.vote_time S.E (d + 1) →
          t < Protocol.vote_time S.E (last + 1) :=
        fun ht => ht.trans_le htimeMax
      have hnonempty : 0 < ((S.E.committee d) ∩ rho.honest).card := by
        have hm := hcom d
        rcases Nat.eq_zero_or_pos ((S.E.committee d) ∩ rho.honest).card with hz | hp
        · rw [hz, Nat.mul_zero] at hm
          exact absurd hm (Nat.not_lt_zero _)
        · exact hp
      obtain ⟨x, hxmem⟩ := Finset.card_pos.mp hnonempty
      have hx : x ∈ rho.honest := (Finset.mem_inter.mp hxmem).2
      have hxCommittee : x ∈ S.E.committee d := (Finset.mem_inter.mp hxmem).1
      have hpreserve (B : Block V) (hPB : Block.Preceq P B)
          (hB : ProtectedVoteSlot S rho d B) :
          ProtectedVoteSlot S rho (d + 1) B := by
        let D := voterHeadAt S rho x d
        have hbootstrapD : ∀ r, base ≤ r → r < cut →
            S.a r < Protocol.vote_time S.E (d + 1) → ∀ w ∈ rho.honest,
            NamedRun.emits S rho w
              (Object.attest (actionAttestationAt S rho w r)) (S.a r) →
            Block.Preceq (actionSGBlockAt S rho w r) D := by
          intro r hrlo hrhi ht w hw hemit
          exact Block.preceq_trans (hsgBoot r hrlo hrhi w hw hemit)
            (hprev.1.heads x hx)
        have hpriorD : ∀ q, S.hc.opening_slot cut ≤ q → q < d →
            ∀ w ∈ rho.honest, ∀ C,
            GenuineConfirmationWith
              (NamedProfile.gradeContract
                (Internal.NamedRecoveryRead.confirmationInputRead S rho w q).cache)
              S.E S.hc (confStore S rho w q) q C →
            Block.Preceq C D := by
          intro q hq hqd w hw C hC
          exact (hprev.2 q hq hqd w hw C hC).heads x hx
        have hlegacyActionRootsD : ∀ r, cut ≤ r →
            S.a r < Protocol.vote_time S.E (d + 1) → ∀ w ∈ rho.honest,
            ∀ (C : NamedBlock V) (a : NamedAttestation V),
            let R := Protocol.get_fg_root
              (actionStoreAt S rho w r).st.core.toHealing.toFG
            C ∈ (actionStoreAt S rho w r).st.bodies →
            (Protocol.derive_named S.E S.cfg C).J = R →
            a.val_index ∈ rho.honest →
            NamedRun.emits S rho a.val_index (Object.attest a) (S.a a.round) →
            a.round < cut →
            a.height_pair.erase = HeightPair.target
              (Protocol.derive_named S.E S.cfg C).h_j
              (Protocol.derive_named S.E S.cfg C).J.root →
            fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) =
              some R →
            Block.Preceq R D := by
          intro r hr ht w hw C a
          dsimp only
          intro hC hJ ha hemit hold hpair hT
          exact Block.preceq_trans
            (hlegacyActionRoots r hr (htimeLift ht) w hw C a hC hJ ha hemit
              hold hpair hT)
            (hprev.1.heads x hx)
        have hrootCompat : ∀ w ∈ rho.honest, ∀ (C : NamedBlock V)
            (a : NamedAttestation V) (ta : Time),
            let R := Protocol.get_fg_root
              (rho.storeBeforeTime S w (Protocol.vote_time S.E (d + 1))).toHealing.toFG
            C ∈ (rho.storeBeforeTime S w
              (Protocol.vote_time S.E (d + 1))).bodies →
            (Protocol.derive_named S.E S.cfg C).J = R →
            a.val_index ∈ rho.honest →
            NamedRun.emits S rho a.val_index (Object.attest a) ta →
            ta < Protocol.vote_time S.E (d + 1) →
            a.round < cut →
            a.height_pair.erase = HeightPair.target
              (Protocol.derive_named S.E S.cfg C).h_j
              (Protocol.derive_named S.E S.cfg C).J.root →
            fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) =
              some R →
            Block.compatible B R = true := by
          intro w hw C a ta
          dsimp only
          intro hC hJ ha hemit hta hold hpair hT
          have hRP := hlegacyReadRoots (d + 1) hnext hupper w hw C a ta
            hC hJ ha hemit hta hold hpair hT
          have hRP' : Block.Preceq
              (Protocol.get_fg_root
                (rho.storeBeforeTime S w
                  (Protocol.vote_time S.E (d + 1))).toHealing.toFG) P := by
            simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
              Proofs.Optimistic.tickStore, Protocol.NamedStore.setClock] using hRP
          simp only [Block.compatible, Bool.or_eq_true]
          exact Or.inr (Block.preceq_trans hRP' hPB)
        have hlegacyD : ∀ w ∈ rho.honest, ∀ {C : NamedBlock V},
            C.erase = B →
            (Protocol.derive_named S.E S.cfg C).h <
              (Internal.NamedRecoveryRead.voteDutyRead S rho w (d + 1)).st.core.h_max - 1 →
            ∀ (a : NamedAttestation V) (ta : Time) (K : NamedBlock V),
              a.val_index ∈ rho.honest →
              NamedRun.emits S rho a.val_index (Object.attest a) ta →
              ta < Protocol.vote_time S.E (d + 1) →
              a.height_pair.erase.height? =
                some ((Proofs.Optimistic.voteDutyStore S rho w (d + 1)).h_max - 1) →
              a.round < cut →
              fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) =
                some (Protocol.derive_named S.E S.cfg K).T_h →
              NamedBlock.compatible C K = true := by
          intro w hw C hCB hCheight a ta K ha hemit hta hrow hold hT
          exact hnoOldFrontier (d + 1) hnext hupper C
            (by simpa only [hCB] using hPB) w hw hCheight a ta K ha hemit hta
            hrow hold hT
        have hsourcesD :=
          actionSources_preceq_of_priorConfirmations_and_historyCut_of_delivery
            S adm hdelivery hcapHor hmajority (base := base) (cut := cut)
            (s := d) (D := D) hspan hbootstrapD hpriorD hlegacyActionRootsD
            (fun r hr hrpos ht => hwindow r hr hrpos (htimeLift ht))
            (fun r hr hrpos ht p => hcapDomainV2 r hr hrpos (htimeLift ht) p)
        have hfgB : ∀ r, cut ≤ r →
            S.a r < Protocol.vote_time S.E (d + 1) →
            ∀ z ∈ rho.honest, ∀ T,
            fgConfirmationWitness S (actionStoreAt S rho z r) = some T →
            Block.compatible B T = true := by
          intro r hr ht z hz T hT
          exact Block.compatible_of_preceq_common (hB.heads x hx)
            (((hsourcesD r ((hspan.trans (Nat.sub_le _ _)).trans hr) ht).2
              hr z hz).2 T hT)
        have hrootB : ∀ z ∈ rho.honest, Block.compatible
            (Protocol.get_fg_root
              (Internal.NamedRecoveryRead.voteDutyRead S rho z
                (d + 1)).st.core.toHealing.toFG) B = true := by
          intro z hz
          have hroot := WeakFG.fgRoot_compatible_of_bootstrap_and_recentActions_at_read
            S adm hmajority hz (time := Protocol.vote_time S.E (d + 1))
            (cut := cut) (B := B) hfgB (hrootCompat z hz)
          simpa only [Internal.NamedRecoveryRead.voteDutyRead,
            NamedActionReads.confirmationReadAt,
            NamedActionReads.confirmationReadFrom,
            Protocol.NamedStore.setClock] using hroot
        have hfrontierB : ∀ z ∈ rho.honest, ∀ {C : NamedBlock V}, C.erase = B →
            (Protocol.derive_named S.E S.cfg C).h <
              (Internal.NamedRecoveryRead.voteDutyRead S rho z
                (d + 1)).st.core.h_max - 1 →
            RunBlock S rho C →
            ∀ (a : NamedAttestation V) (ta : Time) (K : NamedBlock V),
              a.val_index ∈ rho.honest →
              NamedRun.emits S rho a.val_index (Object.attest a) ta →
              ta < Protocol.vote_time S.E (d + 1) →
              a.height_pair.erase.height? =
                some ((Proofs.Optimistic.voteDutyStore S rho z (d + 1)).h_max - 1) →
              fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) =
                some (Protocol.derive_named S.E S.cfg K).T_h →
              RunBlock S rho K →
              Block.compatible C.erase
                (Protocol.derive_named S.E S.cfg K).T_h = true := by
          intro z hz C hCB hCheight hCrun a ta K ha hemit hta hrow hselected hKrun
          by_cases haold : a.round < cut
          · have hnamed := hlegacyD z hz hCB hCheight a ta K ha hemit hta hrow
              haold hselected
            have htarget := Proofs.Optimistic.derive_named_T_h_preceq S.E S.cfg K
            have hcases : NamedBlock.Preceq C K ∨ NamedBlock.Preceq K C := by
              simpa only [NamedBlock.compatible, Bool.or_eq_true] using hnamed
            rcases hcases with hCK | hKC
            · exact Block.compatible_of_preceq_common
                (Proofs.NamedWire.erase_preceq hCK) htarget
            · simp only [Block.compatible, Bool.or_eq_true]
              exact Or.inr (Block.preceq_trans htarget
                (Proofs.NamedWire.erase_preceq hKC))
          · have harecent : cut ≤ a.round := Nat.le_of_not_gt haold
            have htime : S.a a.round < Protocol.vote_time S.E (d + 1) := by
              simpa only [(Proofs.Optimistic.emits_attest_shape S hemit).2] using hta
            simpa only [hCB] using
              hfgB a.round harecent htime a.val_index ha
                (Protocol.derive_named S.E S.cfg K).T_h hselected
        have hanchorB : ∀ z ∈ rho.honest,
            Block.compatible (voterAnchorAt S rho z (d + 1)) B = true := by
          intro z hz
          by_cases hrzero : S.hc.round_of (d + 1) = 0
          · rw [WeakGenesis.voterAnchorAt_eq_fgRoot_of_round_zero
              S adm z (d + 1) hrzero]
            exact hrootB z hz
          · have hrpos : 0 < S.hc.round_of (d + 1) :=
              Nat.pos_of_ne_zero hrzero
            have hBD : Block.Preceq B D := hB.heads x hx
            have hcarriersD : ∀ k, base ≤ k → k < S.hc.round_of (d + 1) →
                ∀ u ∈ rho.honest,
                NamedRun.emits S rho u
                  (Object.attest (actionAttestationAt S rho u k)) (S.a k) →
                Block.Preceq (actionSGBlockAt S rho u k) D := by
              intro k hk hklt u hu hemit
              exact (hsourcesD k hk (action_before_vote_of_round_lt S hklt)).1
                u hu hemit
            have hfgD : ∀ r, cut ≤ r →
                S.a r < Protocol.vote_time S.E (d + 1) →
                ∀ u ∈ rho.honest, ∀ T,
                fgConfirmationWitness S (actionStoreAt S rho u r) = some T →
                Block.compatible D T = true := by
              intro r hr ht u hu T hT
              simp only [Block.compatible, Bool.or_eq_true]
              exact Or.inr (((hsourcesD r
                ((hspan.trans (Nat.sub_le _ _)).trans hr) ht).2 hr u hu).2 T hT)
            have hrootCompatD : ∀ u ∈ rho.honest, ∀ (C : NamedBlock V)
                (a : NamedAttestation V) (ta : Time),
                let R := Protocol.get_fg_root
                  (rho.storeBeforeTime S u
                    (Protocol.vote_time S.E (d + 1))).toHealing.toFG
                C ∈ (rho.storeBeforeTime S u
                  (Protocol.vote_time S.E (d + 1))).bodies →
                (Protocol.derive_named S.E S.cfg C).J = R →
                a.val_index ∈ rho.honest →
                NamedRun.emits S rho a.val_index (Object.attest a) ta →
                ta < Protocol.vote_time S.E (d + 1) →
                a.round < cut →
                a.height_pair.erase = HeightPair.target
                  (Protocol.derive_named S.E S.cfg C).h_j
                  (Protocol.derive_named S.E S.cfg C).J.root →
                fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) =
                  some R →
                Block.compatible D R = true := by
              intro u hu C a ta
              dsimp only
              intro hC hJ ha hemit hta hold hpair hT
              have hRP := hlegacyReadRoots (d + 1) hnext hupper u hu C a ta
                hC hJ ha hemit hta hold hpair hT
              have hRP' : Block.Preceq
                  (Protocol.get_fg_root
                    (rho.storeBeforeTime S u
                      (Protocol.vote_time S.E (d + 1))).toHealing.toFG) P := by
                simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
                  Proofs.Optimistic.tickStore, Protocol.NamedStore.setClock] using hRP
              simp only [Block.compatible, Bool.or_eq_true]
              exact Or.inr (Block.preceq_trans hRP' (hprev.1.heads x hx))
            have hrootD : ∀ u ∈ rho.honest, Block.compatible
                (Protocol.get_fg_root
                  (Internal.NamedRecoveryRead.voteDutyRead S rho u
                    (d + 1)).st.core.toHealing.toFG) D = true := by
              intro u hu
              have hroot := WeakFG.fgRoot_compatible_of_bootstrap_and_recentActions_at_read
                S adm hmajority hu (time := Protocol.vote_time S.E (d + 1))
                (cut := cut) (B := D) hfgD (hrootCompatD u hu)
              simpa only [Internal.NamedRecoveryRead.voteDutyRead,
                NamedActionReads.confirmationReadAt,
                NamedActionReads.confirmationReadFrom,
                Protocol.NamedStore.setClock] using hroot
            have hvoteCap : Protocol.vote_time S.E (d + 1) ≤ cap := by
              apply le_trans ?_ (hconfCap d hdlast)
              rw [← vote_time_succ_add_delta_eq_confirmation_time S.E d]
              exact Int.le_add_of_nonneg_right S.E.Δ_pos.le
            have hvoteHor : Protocol.vote_time S.E (d + 1) ≤ rho.horizon := by
              apply le_trans ?_ (hconfHor d hdlast)
              rw [← vote_time_succ_add_delta_eq_confirmation_time S.E d]
              exact Int.le_add_of_nonneg_right S.E.Δ_pos.le
            have hwindowStart : base ≤ S.hc.round_of (d + 1) - S.hc.η_SG :=
              hspan.trans (Nat.sub_le_sub_right hgap _)
            have hcapEarly : DecoupledConsensusModel.Protocol.early S.E S.hc
                (S.hc.round_of (d + 1)) .g1 ≤ cap := by
              have hdomainCapG1 : DecoupledConsensusModel.Protocol.domain S.E S.hc
                  (S.hc.round_of (d + 1)) .g1 ≤ cap := by
                rw [NamedOutageClosure.domain_g1_eq_opening]
                exact ((proposal_time_mono S.E
                  (Nat.div_mul_le_self (d + 1) S.hc.R)).trans
                    (proposal_time_lt_vote_time S.E (d + 1)).le).trans hvoteCap
              exact (NamedOutageHistory.GuardedHelpers.early_g1_le_domain_g1
                S (S.hc.round_of (d + 1))).trans hdomainCapG1
            have hinterpreted := interpretedInputs_at_voteDuty_of_delivery
              S adm hdelivery (base := base) (r := S.hc.round_of (d + 1))
              (d := d + 1) (B := D) rfl hrpos hwindowStart hcarriersD hrootD
              hcapEarly hvoteHor
            have hwindowB : Internal.PhaseGrades.WindowMajorityAt S.E S.hc
                (Internal.NamedRecoveryRead.voteDutyRead S rho z
                  (d + 1)).st.core.toHealing.gradeView
                (Internal.NamedRecoveryRead.voteDutyRead S rho z (d + 1)).st.core.F
                rho.honest (S.hc.round_of (d + 1))
                (DecoupledConsensusModel.Protocol.late S.E S.hc
                  (S.hc.round_of (d + 1)) .g1) := by
              apply WeakSG.windowMajorityAt_of_awakeWindowMajority S
                (hreadWindowV2 (d + 1) hnext hupper hrpos)
              intro v hv
              obtain ⟨hvHon, k, hk, huk⟩ := WeakSG.mem_honestAwakeWindow_iff.mp hv
              obtain ⟨input, hinput, hround, hconfirmed, hfind⟩ :=
                hinterpreted z hz v hvHon k hk huk
              refine ⟨input, ?_⟩
              exact GradeCutoffMono.interpretedInputs_mono
                (Internal.NamedRecoveryRead.voteDutyRead S rho z
                  (d + 1)).st.core.toHealing.gradeView
                (Internal.NamedRecoveryRead.voteDutyRead S rho z (d + 1)).st.core.F
                S.hc.η_SG (S.hc.round_of (d + 1))
                (NamedOutageClosure.q10_early_le_late S
                  (S.hc.round_of (d + 1)) .g1) v hinput
            have hhistoryB : ∀ k ∈ Protocol.latest_window S.hc.η_SG
                (S.hc.round_of (d + 1)),
                HonestSGEmissionsCompatibleAtRound S rho k B := by
              intro k hk u hu hemit
              have hcarrierD := hcarriersD k
                (hwindowStart.trans (WeakSG.mem_latestWindow_lower_bound hk))
                (mem_latestWindow_lt hk) u hu hemit
              exact Block.compatible_of_preceq_common hcarrierD hBD
            have hbatchB := batchCompatibleAt_of_historyCutEmissions
              S adm hz hhistoryB
            let read := Internal.NamedRecoveryRead.voteDutyRead S rho z (d + 1)
            have hslot : read.st.core.s = d + 1 :=
              Proofs.Optimistic.voteDutyRead_slot S rho z (d + 1)
            rcases voterAnchorAt_cases S rho z (d + 1) with hroot |
                ⟨raw, A, hframe, hactive, hA⟩
            · rw [hroot]
              exact hrootB z hz
            · have hframeRead :
                  (DecoupledConsensusModel.Protocol.readFrame read.cache read.st.core.toHealing
                    (S.hc.round_of (d + 1))).g1 = some (some raw) := by
                simpa only [read, hslot] using hframe
              have hgrade := preparedVoteDutyG1FrameGrade_of_activePrefix
                S adm rfl hrpos hvoteHor z hz raw hframeRead A hactive
              have hanchor := WeakSG.getSgRoot_compatible_of_windowHistory_at_read
                S read (S.hc.round_of (d + 1)) B hbatchB hwindowB
                (fun raw' hframe' => by
                  have heq : raw' = raw := by
                    exact Option.some.inj (Option.some.inj
                      (hframe'.symm.trans hframeRead))
                  simpa only [heq] using hgrade)
                (hrootB z hz)
              simpa only [voterAnchorAt, Internal.PhaseGrades.nodeAnchor,
                Internal.PhaseGrades.nodeRead, Protocol.get_sg_root_with, read, hslot, hA]
                using hanchor
        have hstep := WeakGoldfish.goldfishCone_succ_of_runFrontierWitnesses_of_delivery
          S adm hdelivery hcom hmajority hdpos (hconfCap d hdlast)
            (hconfHor d hdlast) hB.cone hfrontierB hrootB hanchorB
        exact ⟨hstep.1, hstep.2⟩
      have hPnext := hpreserve P (Block.preceq_self P) hprev.1
      refine ⟨hPnext, ?_⟩
      intro q hq hqd w hw B hB
      by_cases hqd' : q < d
      · have hBold := hprev.2 q hq hqd' w hw B hB
        have hordered : Block.Preceq P B ∨ Block.Preceq B P := by
          simpa only [Block.compatible, Bool.or_eq_true] using
            Block.compatible_of_preceq_common (hprev.1.heads x hx)
              (hBold.heads x hx)
        rcases hordered with hPB | hBP
        · exact hpreserve B hPB hBold
        · exact hPnext.of_ancestor hBP
      · have hqe : q = d :=
          Nat.le_antisymm (Nat.le_of_lt_succ hqd) (Nat.le_of_not_gt hqd')
        subst q
        obtain ⟨y, hy, hBhead⟩ :=
          WeakGoldfish.genuineConfirmation_exists_honestVoteSupporter_of_delivery
            S adm hdelivery hcom (v := w) hw hdpos (hconfCap d hdlast)
              (hconfHor d hdlast) hB
        obtain ⟨hyCommittee, hBhead⟩ := hBhead
        have hordered : Block.Preceq P B ∨ Block.Preceq B P := by
          simpa only [Block.compatible, Bool.or_eq_true] using
            Block.compatible_of_preceq_common (hprev.1.heads y hy) hBhead
        rcases hordered with hPB | hBP
        · let D := voterHeadAt S rho y d
          have hbootstrapD : ∀ r, base ≤ r → r < cut →
              S.a r < Protocol.vote_time S.E (d + 1) → ∀ z ∈ rho.honest,
              NamedRun.emits S rho z
                (Object.attest (actionAttestationAt S rho z r)) (S.a r) →
              Block.Preceq (actionSGBlockAt S rho z r) D := by
            intro r hrlo hrhi ht z hz hemit
            exact Block.preceq_trans (hsgBoot r hrlo hrhi z hz hemit)
              (hprev.1.heads y hy)
          have hpriorD : ∀ q, S.hc.opening_slot cut ≤ q → q < d →
              ∀ z ∈ rho.honest, ∀ C,
              GenuineConfirmationWith
                (NamedProfile.gradeContract
                  (Internal.NamedRecoveryRead.confirmationInputRead S rho z q).cache)
                S.E S.hc (confStore S rho z q) q C →
              Block.Preceq C D := by
            intro q hq hqd z hz C hC
            exact (hprev.2 q hq hqd z hz C hC).heads y hy
          have hlegacyActionRootsD : ∀ r, cut ≤ r →
              S.a r < Protocol.vote_time S.E (d + 1) → ∀ z ∈ rho.honest,
              ∀ (C : NamedBlock V) (a : NamedAttestation V),
              let R := Protocol.get_fg_root
                (actionStoreAt S rho z r).st.core.toHealing.toFG
              C ∈ (actionStoreAt S rho z r).st.bodies →
              (Protocol.derive_named S.E S.cfg C).J = R →
              a.val_index ∈ rho.honest →
              NamedRun.emits S rho a.val_index (Object.attest a) (S.a a.round) →
              a.round < cut →
              a.height_pair.erase = HeightPair.target
                (Protocol.derive_named S.E S.cfg C).h_j
                (Protocol.derive_named S.E S.cfg C).J.root →
              fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) =
                some R →
              Block.Preceq R D := by
            intro r hr ht z hz C a
            dsimp only
            intro hC hJ ha hemit hold hpair hT
            exact Block.preceq_trans
              (hlegacyActionRoots r hr (htimeLift ht) z hz C a hC hJ ha hemit
                hold hpair hT)
              (hprev.1.heads y hy)
          have hsources :=
            actionSources_preceq_of_priorConfirmations_and_historyCut_of_delivery
              S adm hdelivery hcapHor hmajority (base := base) (cut := cut)
              (s := d) (D := D) hspan hbootstrapD hpriorD hlegacyActionRootsD
              (fun r hr hrpos ht => hwindow r hr hrpos (htimeLift ht))
              (fun r hr hrpos ht p => hcapDomainV2 r hr hrpos (htimeLift ht) p)
          have hfg : ∀ r, cut ≤ r →
              S.a r < Protocol.vote_time S.E (d + 1) →
              ∀ z ∈ rho.honest, ∀ T,
              fgConfirmationWitness S (actionStoreAt S rho z r) = some T →
              Block.compatible B T = true := by
            intro r hr ht z hz T hT
            exact Block.compatible_of_preceq_common hBhead
              (((hsources r ((hspan.trans (Nat.sub_le _ _)).trans hr) ht).2
                hr z hz).2 T hT)
          have hrootCompatB : ∀ z ∈ rho.honest, ∀ (C : NamedBlock V)
              (a : NamedAttestation V) (ta : Time),
              let R := Protocol.get_fg_root
                (rho.storeBeforeTime S z (Protocol.vote_time S.E (d + 1))).toHealing.toFG
              C ∈ (rho.storeBeforeTime S z
                (Protocol.vote_time S.E (d + 1))).bodies →
              (Protocol.derive_named S.E S.cfg C).J = R →
              a.val_index ∈ rho.honest →
              NamedRun.emits S rho a.val_index (Object.attest a) ta →
              ta < Protocol.vote_time S.E (d + 1) →
              a.round < cut →
              a.height_pair.erase = HeightPair.target
                (Protocol.derive_named S.E S.cfg C).h_j
                (Protocol.derive_named S.E S.cfg C).J.root →
              fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) =
                some R →
              Block.compatible B R = true := by
            intro z hz C a ta
            dsimp only
            intro hC hJ ha hemit hta hold hpair hT
            have hRP := hlegacyReadRoots (d + 1) hnext hupper z hz C a ta
              hC hJ ha hemit hta hold hpair hT
            have hRP' : Block.Preceq
                (Protocol.get_fg_root
                  (rho.storeBeforeTime S z
                    (Protocol.vote_time S.E (d + 1))).toHealing.toFG) P := by
              simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
                Proofs.Optimistic.tickStore, Protocol.NamedStore.setClock] using hRP
            simp only [Block.compatible, Bool.or_eq_true]
            exact Or.inr (Block.preceq_trans hRP' hPB)
          have hrootB : ∀ z ∈ rho.honest, Block.compatible
              (Protocol.get_fg_root
                (Internal.NamedRecoveryRead.voteDutyRead S rho z (d + 1)).st.core.toHealing.toFG)
              B = true := by
            intro z hz
            have hroot := WeakFG.fgRoot_compatible_of_bootstrap_and_recentActions_at_read
              S adm hmajority hz (time := Protocol.vote_time S.E (d + 1)) (cut := cut)
              (B := B) hfg (hrootCompatB z hz)
            simpa only [Internal.NamedRecoveryRead.voteDutyRead,
              NamedActionReads.confirmationReadAt, NamedActionReads.confirmationReadFrom,
              Protocol.NamedStore.setClock] using hroot
          have hanchorB : ∀ z ∈ rho.honest,
              Block.compatible (voterAnchorAt S rho z (d + 1)) B = true := by
            intro z hz
            by_cases hrzero : S.hc.round_of (d + 1) = 0
            · rw [WeakGenesis.voterAnchorAt_eq_fgRoot_of_round_zero
                S adm z (d + 1) hrzero]
              exact hrootB z hz
            · have hrpos : 0 < S.hc.round_of (d + 1) :=
                Nat.pos_of_ne_zero hrzero
              have hcarriersD : ∀ k, base ≤ k → k < S.hc.round_of (d + 1) →
                  ∀ u ∈ rho.honest,
                  NamedRun.emits S rho u
                    (Object.attest (actionAttestationAt S rho u k)) (S.a k) →
                  Block.Preceq (actionSGBlockAt S rho u k) D := by
                intro k hk hklt u hu hemit
                exact (hsources k hk (action_before_vote_of_round_lt S hklt)).1
                  u hu hemit
              have hfgD : ∀ r, cut ≤ r →
                  S.a r < Protocol.vote_time S.E (d + 1) →
                  ∀ u ∈ rho.honest, ∀ T,
                  fgConfirmationWitness S (actionStoreAt S rho u r) = some T →
                  Block.compatible D T = true := by
                intro r hr ht u hu T hT
                simp only [Block.compatible, Bool.or_eq_true]
                exact Or.inr (((hsources r
                  ((hspan.trans (Nat.sub_le _ _)).trans hr) ht).2 hr u hu).2 T hT)
              have hrootCompatD : ∀ u ∈ rho.honest, ∀ (C : NamedBlock V)
                  (a : NamedAttestation V) (ta : Time),
                  let R := Protocol.get_fg_root
                    (rho.storeBeforeTime S u
                      (Protocol.vote_time S.E (d + 1))).toHealing.toFG
                  C ∈ (rho.storeBeforeTime S u
                    (Protocol.vote_time S.E (d + 1))).bodies →
                  (Protocol.derive_named S.E S.cfg C).J = R →
                  a.val_index ∈ rho.honest →
                  NamedRun.emits S rho a.val_index (Object.attest a) ta →
                  ta < Protocol.vote_time S.E (d + 1) →
                  a.round < cut →
                  a.height_pair.erase = HeightPair.target
                    (Protocol.derive_named S.E S.cfg C).h_j
                    (Protocol.derive_named S.E S.cfg C).J.root →
                  fgConfirmationWitness S
                    (actionStoreAt S rho a.val_index a.round) = some R →
                  Block.compatible D R = true := by
                intro u hu C a ta
                dsimp only
                intro hC hJ ha hemit hta hold hpair hT
                have hRP := hlegacyReadRoots (d + 1) hnext hupper u hu C a ta
                  hC hJ ha hemit hta hold hpair hT
                have hRP' : Block.Preceq
                    (Protocol.get_fg_root
                      (rho.storeBeforeTime S u
                        (Protocol.vote_time S.E (d + 1))).toHealing.toFG) P := by
                  simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
                    Proofs.Optimistic.tickStore, Protocol.NamedStore.setClock] using hRP
                simp only [Block.compatible, Bool.or_eq_true]
                exact Or.inr (Block.preceq_trans hRP' (hprev.1.heads y hy))
              have hrootD : ∀ u ∈ rho.honest, Block.compatible
                  (Protocol.get_fg_root
                    (Internal.NamedRecoveryRead.voteDutyRead S rho u
                      (d + 1)).st.core.toHealing.toFG) D = true := by
                intro u hu
                have hroot := WeakFG.fgRoot_compatible_of_bootstrap_and_recentActions_at_read
                  S adm hmajority hu (time := Protocol.vote_time S.E (d + 1))
                  (cut := cut) (B := D) hfgD (hrootCompatD u hu)
                simpa only [Internal.NamedRecoveryRead.voteDutyRead,
                  NamedActionReads.confirmationReadAt,
                  NamedActionReads.confirmationReadFrom,
                  Protocol.NamedStore.setClock] using hroot
              have hvoteCap : Protocol.vote_time S.E (d + 1) ≤ cap := by
                apply le_trans ?_ (hconfCap d hdlast)
                rw [← vote_time_succ_add_delta_eq_confirmation_time S.E d]
                exact Int.le_add_of_nonneg_right S.E.Δ_pos.le
              have hvoteHor : Protocol.vote_time S.E (d + 1) ≤ rho.horizon := by
                apply le_trans ?_ (hconfHor d hdlast)
                rw [← vote_time_succ_add_delta_eq_confirmation_time S.E d]
                exact Int.le_add_of_nonneg_right S.E.Δ_pos.le
              have hwindowStart : base ≤ S.hc.round_of (d + 1) - S.hc.η_SG :=
                hspan.trans (Nat.sub_le_sub_right hgap _)
              have hcapEarly : DecoupledConsensusModel.Protocol.early S.E S.hc
                  (S.hc.round_of (d + 1)) .g1 ≤ cap := by
                have hdomainCapG1 : DecoupledConsensusModel.Protocol.domain S.E S.hc
                    (S.hc.round_of (d + 1)) .g1 ≤ cap := by
                  rw [NamedOutageClosure.domain_g1_eq_opening]
                  exact ((proposal_time_mono S.E
                    (Nat.div_mul_le_self (d + 1) S.hc.R)).trans
                      (proposal_time_lt_vote_time S.E (d + 1)).le).trans hvoteCap
                exact (NamedOutageHistory.GuardedHelpers.early_g1_le_domain_g1
                  S (S.hc.round_of (d + 1))).trans hdomainCapG1
              have hinterpreted := interpretedInputs_at_voteDuty_of_delivery
                S adm hdelivery (base := base) (r := S.hc.round_of (d + 1))
                (d := d + 1) (B := D) rfl hrpos hwindowStart hcarriersD hrootD
                hcapEarly hvoteHor
              have hwindowB : Internal.PhaseGrades.WindowMajorityAt S.E S.hc
                  (Internal.NamedRecoveryRead.voteDutyRead S rho z
                    (d + 1)).st.core.toHealing.gradeView
                  (Internal.NamedRecoveryRead.voteDutyRead S rho z (d + 1)).st.core.F
                  rho.honest (S.hc.round_of (d + 1))
                  (DecoupledConsensusModel.Protocol.late S.E S.hc
                    (S.hc.round_of (d + 1)) .g1) := by
                apply WeakSG.windowMajorityAt_of_awakeWindowMajority S
                  (hreadWindowV2 (d + 1) hnext hupper hrpos)
                intro v hv
                obtain ⟨hvHon, k, hk, huk⟩ := WeakSG.mem_honestAwakeWindow_iff.mp hv
                obtain ⟨input, hinput, hround, hconfirmed, hfind⟩ :=
                  hinterpreted z hz v hvHon k hk huk
                refine ⟨input, ?_⟩
                exact GradeCutoffMono.interpretedInputs_mono
                  (Internal.NamedRecoveryRead.voteDutyRead S rho z
                    (d + 1)).st.core.toHealing.gradeView
                  (Internal.NamedRecoveryRead.voteDutyRead S rho z (d + 1)).st.core.F
                  S.hc.η_SG (S.hc.round_of (d + 1))
                  (NamedOutageClosure.q10_early_le_late S
                    (S.hc.round_of (d + 1)) .g1) v hinput
              have hhistoryB : ∀ k ∈ Protocol.latest_window S.hc.η_SG
                  (S.hc.round_of (d + 1)),
                  HonestSGEmissionsCompatibleAtRound S rho k B := by
                intro k hk u hu hemit
                have hcarrierD := hcarriersD k
                  (hwindowStart.trans (WeakSG.mem_latestWindow_lower_bound hk))
                  (mem_latestWindow_lt hk) u hu hemit
                exact Block.compatible_of_preceq_common hcarrierD hBhead
              have hbatchB := batchCompatibleAt_of_historyCutEmissions
                S adm hz hhistoryB
              let read := Internal.NamedRecoveryRead.voteDutyRead S rho z (d + 1)
              have hslot : read.st.core.s = d + 1 :=
                Proofs.Optimistic.voteDutyRead_slot S rho z (d + 1)
              rcases voterAnchorAt_cases S rho z (d + 1) with hroot |
                  ⟨raw, A, hframe, hactive, hA⟩
              · rw [hroot]
                exact hrootB z hz
              · have hframeRead :
                    (DecoupledConsensusModel.Protocol.readFrame read.cache read.st.core.toHealing
                      (S.hc.round_of (d + 1))).g1 = some (some raw) := by
                  simpa only [read, hslot] using hframe
                have hgrade := preparedVoteDutyG1FrameGrade_of_activePrefix
                  S adm rfl hrpos hvoteHor z hz raw hframeRead A hactive
                have hanchor := WeakSG.getSgRoot_compatible_of_windowHistory_at_read
                  S read (S.hc.round_of (d + 1)) B hbatchB hwindowB
                  (fun raw' hframe' => by
                    have heq : raw' = raw := by
                      exact Option.some.inj (Option.some.inj
                        (hframe'.symm.trans hframeRead))
                    simpa only [heq] using hgrade)
                  (hrootB z hz)
                simpa only [voterAnchorAt, Internal.PhaseGrades.nodeAnchor,
                  Internal.PhaseGrades.nodeRead, Protocol.get_sg_root_with,
                  read, hslot, hA] using hanchor
          have hfrontierB : ∀ z ∈ rho.honest, ∀ {C : NamedBlock V}, C.erase = B →
              (Protocol.derive_named S.E S.cfg C).h <
                (Internal.NamedRecoveryRead.voteDutyRead S rho z (d + 1)).st.core.h_max - 1 →
              RunBlock S rho C →
              ∀ (a : NamedAttestation V) (ta : Time) (K : NamedBlock V),
                a.val_index ∈ rho.honest →
                NamedRun.emits S rho a.val_index (Object.attest a) ta →
                ta < Protocol.vote_time S.E (d + 1) →
                a.height_pair.erase.height? =
                  some ((Proofs.Optimistic.voteDutyStore S rho z (d + 1)).h_max - 1) →
                fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) =
                  some (Protocol.derive_named S.E S.cfg K).T_h →
                RunBlock S rho K →
                Block.compatible C.erase
                  (Protocol.derive_named S.E S.cfg K).T_h = true := by
            intro z hz C hCB hCheight hCrun a ta K ha hemit hta hrow hselected hKrun
            by_cases haold : a.round < cut
            · have hnamed := hnoOldFrontier (d + 1) hnext hupper C
                (by simpa only [hCB] using hPB) z hz hCheight a ta K ha hemit hta
                hrow haold hselected
              have htarget := Proofs.Optimistic.derive_named_T_h_preceq S.E S.cfg K
              have hcases : NamedBlock.Preceq C K ∨ NamedBlock.Preceq K C := by
                simpa only [NamedBlock.compatible, Bool.or_eq_true] using hnamed
              rcases hcases with hCK | hKC
              · exact Block.compatible_of_preceq_common
                  (Proofs.NamedWire.erase_preceq hCK) htarget
              · simp only [Block.compatible, Bool.or_eq_true]
                exact Or.inr (Block.preceq_trans htarget
                  (Proofs.NamedWire.erase_preceq hKC))
            · have harecent : cut ≤ a.round := Nat.le_of_not_gt haold
              have htime : S.a a.round < Protocol.vote_time S.E (d + 1) := by
                simpa only [(Proofs.Optimistic.emits_attest_shape S hemit).2] using hta
              simpa only [hCB] using
                hfg a.round harecent htime a.val_index ha
                  (Protocol.derive_named S.E S.cfg K).T_h hselected
          exact WeakGoldfish.protectedVoteSlot_succ_of_genuineConfirmationWith_of_delivery
            S adm hdelivery hcom hmajority (v := w) hw hdpos
            (hconfCap d hdlast) (hconfHor d hdlast) hB hfrontierB hrootB hanchorB
        · exact hPnext.of_ancestor hBP


#print axioms protectedVoteSlots_of_historyCut_of_delivery_v2
theorem protectedVoteSlots_of_historyCut_v2_w
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {lo cap : Time} (hdelivery : NamedHealthyWindowDelivery S rho lo cap)
    (hgstLo : S.E.t_GST ≤ lo)
    (hcapHor : cap ≤ rho.horizon)
    (hcom : HonestCommittees S rho.honest)
    (hmajority : HonestWeightMajority S rho.honest)
    {base cut : Round} {start last : Slot} {P : Block V}
    (hspan : base ≤ cut - S.hc.η_SG)
    (hsendLo : ∀ k, base ≤ k → lo ≤ S.a k)
    (hstartpos : 0 < start)
    (hsettled : S.hc.opening_slot cut ≤ start)
    (hpost : S.E.t_GST ≤ Protocol.proposal_time S.E start)
    (hcap : Protocol.confirmation_time S.E last ≤ cap)
    (hhor : Protocol.confirmation_time S.E last ≤ rho.horizon)
    (hseed : ProtectedVoteSlot S rho start P)
    (hnoOldFrontier : NoOldFrontierAtCut S rho cut start last P)
    (hsgBoot : ∀ r, base ≤ r → r < cut → ∀ w ∈ rho.honest,
      NamedRun.emits S rho w
        (Object.attest (actionAttestationAt S rho w r)) (S.a r) →
      Block.Preceq (actionSGBlockAt S rho w r) P)
    (hconfBoot : ∀ q, S.hc.opening_slot cut ≤ q → q < start →
      ∀ w ∈ rho.honest, ∀ B,
      GenuineConfirmationWith
        (NamedProfile.gradeContract
          (Internal.NamedRecoveryRead.confirmationInputRead S rho w q).cache)
        S.E S.hc (confStore S rho w q) q B →
      Block.Preceq B P)
    (hlegacyActionRoots : ∀ r, cut ≤ r →
      S.a r < Protocol.vote_time S.E (last + 1) → ∀ w ∈ rho.honest,
      ∀ (C : NamedBlock V) (a : NamedAttestation V),
      let R := Protocol.get_fg_root
        (actionStoreAt S rho w r).st.core.toHealing.toFG
      C ∈ (actionStoreAt S rho w r).st.bodies →
      (Protocol.derive_named S.E S.cfg C).J = R →
      a.val_index ∈ rho.honest →
      NamedRun.emits S rho a.val_index (Object.attest a) (S.a a.round) →
      a.round < cut →
      a.height_pair.erase = HeightPair.target
        (Protocol.derive_named S.E S.cfg C).h_j
        (Protocol.derive_named S.E S.cfg C).J.root →
      fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) =
        some R →
      Block.Preceq R P)
    (hlegacyReadRoots : ∀ d, start < d → d ≤ last + 1 →
      ∀ w ∈ rho.honest,
      ∀ (C : NamedBlock V) (a : NamedAttestation V) (ta : Time),
      let R := Protocol.get_fg_root
        (voteDutyStore S rho w d).toHealing.toFG
      C ∈ (rho.storeBeforeTime S w (Protocol.vote_time S.E d)).bodies →
      (Protocol.derive_named S.E S.cfg C).J = R →
      a.val_index ∈ rho.honest →
      NamedRun.emits S rho a.val_index (Object.attest a) ta →
      ta < Protocol.vote_time S.E d →
      a.round < cut →
      a.height_pair.erase = HeightPair.target
        (Protocol.derive_named S.E S.cfg C).h_j
        (Protocol.derive_named S.E S.cfg C).J.root →
      fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) =
        some R →
      Block.Preceq R P)
    (hwindow : ∀ r, cut ≤ r → 0 < r →
      S.a r < Protocol.vote_time S.E (last + 1) →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hreadWindowV2 : ∀ d, start < d → d ≤ last + 1 →
      0 < S.hc.round_of d →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG (S.hc.round_of d))
    (hcapDomainV2 : ∀ r, cut ≤ r → 0 < r →
      S.a r < Protocol.vote_time S.E (last + 1) → ∀ p,
      DecoupledConsensusModel.Protocol.domain S.E S.hc r p ≤ cap) :
    ∀ d, start ≤ d → d ≤ last + 1 →
      ProtectedVoteSlot S rho d P ∧
      (∀ q, S.hc.opening_slot cut ≤ q → q < d →
        ∀ w ∈ rho.honest, ∀ B,
        GenuineConfirmationWith
          (NamedProfile.gradeContract
            (Internal.NamedRecoveryRead.confirmationInputRead S rho w q).cache)
          S.E S.hc (confStore S rho w q) q B →
          ProtectedVoteSlot S rho d B) := by
  have hRpos : 0 < S.hc.R :=
    lt_of_lt_of_le (by decide : 0 < 2) S.hc.R_ge_two
  have hconfHor : ∀ k, k ≤ last →
      Protocol.confirmation_time S.E k ≤ rho.horizon := by
    intro k hk
    apply le_trans ?_ hhor
    rw [Protocol.confirmation_time_eq_support_cutoff_succ,
      Protocol.confirmation_time_eq_support_cutoff_succ]
    exact support_cutoff_mono S.E (Nat.add_le_add_right hk 1)
  have hconfCap : ∀ k, k ≤ last →
      Protocol.confirmation_time S.E k ≤ cap := by
    intro k hk
    apply le_trans ?_ hcap
    rw [Protocol.confirmation_time_eq_support_cutoff_succ,
      Protocol.confirmation_time_eq_support_cutoff_succ]
    exact support_cutoff_mono S.E (Nat.add_le_add_right hk 1)
  intro d hd
  induction d, hd using Nat.le_induction with
  | base =>
      intro hupper
      exact ⟨hseed, fun q hq hqd w hw B hB =>
        hseed.of_ancestor (hconfBoot q hq hqd w hw B hB)⟩
  | succ d hd ih =>
      intro hupper
      have hdlast : d ≤ last := Nat.le_of_succ_le_succ hupper
      have hprev := ih (hdlast.trans (Nat.le_succ last))
      have hdpos : 0 < d := hstartpos.trans_le hd
      have hnext : start < d + 1 := Nat.lt_succ_of_le hd
      have hpostD := hpost.trans (proposal_time_mono S.E hd)
      have hpostVote := hpostD.trans (proposal_time_lt_vote_time S.E d).le
      have hgap : cut ≤ S.hc.round_of (d + 1) := by
        change cut ≤ (d + 1) / S.hc.R
        exact (Nat.le_div_iff_mul_le hRpos).2
          (hsettled.trans (hd.trans (Nat.le_succ d)))
      have htimeMax := vote_time_mono_slots S.E (Nat.add_le_add_right hdlast 1)
      have htimeLift : ∀ {t : Time}, t < Protocol.vote_time S.E (d + 1) →
          t < Protocol.vote_time S.E (last + 1) :=
        fun ht => ht.trans_le htimeMax
      have hnonempty : 0 < ((S.E.committee d) ∩ rho.honest).card := by
        have hm := hcom d
        rcases Nat.eq_zero_or_pos ((S.E.committee d) ∩ rho.honest).card with hz | hp
        · rw [hz, Nat.mul_zero] at hm
          exact absurd hm (Nat.not_lt_zero _)
        · exact hp
      obtain ⟨x, hxmem⟩ := Finset.card_pos.mp hnonempty
      have hx : x ∈ rho.honest := (Finset.mem_inter.mp hxmem).2
      have hxCommittee : x ∈ S.E.committee d := (Finset.mem_inter.mp hxmem).1
      have hpreserve (B : Block V) (hPB : Block.Preceq P B)
          (hB : ProtectedVoteSlot S rho d B) :
          ProtectedVoteSlot S rho (d + 1) B := by
        let D := voterHeadAt S rho x d
        have hbootstrapD : ∀ r, base ≤ r → r < cut →
            S.a r < Protocol.vote_time S.E (d + 1) → ∀ w ∈ rho.honest,
            NamedRun.emits S rho w
              (Object.attest (actionAttestationAt S rho w r)) (S.a r) →
            Block.Preceq (actionSGBlockAt S rho w r) D := by
          intro r hrlo hrhi ht w hw hemit
          exact Block.preceq_trans (hsgBoot r hrlo hrhi w hw hemit)
            (hprev.1.heads x hx)
        have hpriorD : ∀ q, S.hc.opening_slot cut ≤ q → q < d →
            ∀ w ∈ rho.honest, ∀ C,
            GenuineConfirmationWith
              (NamedProfile.gradeContract
                (Internal.NamedRecoveryRead.confirmationInputRead S rho w q).cache)
              S.E S.hc (confStore S rho w q) q C →
            Block.Preceq C D := by
          intro q hq hqd w hw C hC
          exact (hprev.2 q hq hqd w hw C hC).heads x hx
        have hlegacyActionRootsD : ∀ r, cut ≤ r →
            S.a r < Protocol.vote_time S.E (d + 1) → ∀ w ∈ rho.honest,
            ∀ (C : NamedBlock V) (a : NamedAttestation V),
            let R := Protocol.get_fg_root
              (actionStoreAt S rho w r).st.core.toHealing.toFG
            C ∈ (actionStoreAt S rho w r).st.bodies →
            (Protocol.derive_named S.E S.cfg C).J = R →
            a.val_index ∈ rho.honest →
            NamedRun.emits S rho a.val_index (Object.attest a) (S.a a.round) →
            a.round < cut →
            a.height_pair.erase = HeightPair.target
              (Protocol.derive_named S.E S.cfg C).h_j
              (Protocol.derive_named S.E S.cfg C).J.root →
            fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) =
              some R →
            Block.Preceq R D := by
          intro r hr ht w hw C a
          dsimp only
          intro hC hJ ha hemit hold hpair hT
          exact Block.preceq_trans
            (hlegacyActionRoots r hr (htimeLift ht) w hw C a hC hJ ha hemit
              hold hpair hT)
            (hprev.1.heads x hx)
        have hrootCompat : ∀ w ∈ rho.honest, ∀ (C : NamedBlock V)
            (a : NamedAttestation V) (ta : Time),
            let R := Protocol.get_fg_root
              (rho.storeBeforeTime S w (Protocol.vote_time S.E (d + 1))).toHealing.toFG
            C ∈ (rho.storeBeforeTime S w
              (Protocol.vote_time S.E (d + 1))).bodies →
            (Protocol.derive_named S.E S.cfg C).J = R →
            a.val_index ∈ rho.honest →
            NamedRun.emits S rho a.val_index (Object.attest a) ta →
            ta < Protocol.vote_time S.E (d + 1) →
            a.round < cut →
            a.height_pair.erase = HeightPair.target
              (Protocol.derive_named S.E S.cfg C).h_j
              (Protocol.derive_named S.E S.cfg C).J.root →
            fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) =
              some R →
            Block.compatible B R = true := by
          intro w hw C a ta
          dsimp only
          intro hC hJ ha hemit hta hold hpair hT
          have hRP := hlegacyReadRoots (d + 1) hnext hupper w hw C a ta
            hC hJ ha hemit hta hold hpair hT
          have hRP' : Block.Preceq
              (Protocol.get_fg_root
                (rho.storeBeforeTime S w
                  (Protocol.vote_time S.E (d + 1))).toHealing.toFG) P := by
            simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
              Proofs.Optimistic.tickStore, Protocol.NamedStore.setClock] using hRP
          simp only [Block.compatible, Bool.or_eq_true]
          exact Or.inr (Block.preceq_trans hRP' hPB)
        have hlegacyD : ∀ w ∈ rho.honest, ∀ {C : NamedBlock V},
            C.erase = B →
            (Protocol.derive_named S.E S.cfg C).h <
              (Internal.NamedRecoveryRead.voteDutyRead S rho w (d + 1)).st.core.h_max - 1 →
            ∀ (a : NamedAttestation V) (ta : Time) (K : NamedBlock V),
              a.val_index ∈ rho.honest →
              NamedRun.emits S rho a.val_index (Object.attest a) ta →
              ta < Protocol.vote_time S.E (d + 1) →
              a.height_pair.erase.height? =
                some ((Proofs.Optimistic.voteDutyStore S rho w (d + 1)).h_max - 1) →
              a.round < cut →
              fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) =
                some (Protocol.derive_named S.E S.cfg K).T_h →
              NamedBlock.compatible C K = true := by
          intro w hw C hCB hCheight a ta K ha hemit hta hrow hold hT
          exact hnoOldFrontier (d + 1) hnext hupper C
            (by simpa only [hCB] using hPB) w hw hCheight a ta K ha hemit hta
            hrow hold hT
        have hsourcesD :=
          actionSources_preceq_of_priorConfirmations_and_historyCut_w
            S adm hdelivery hgstLo hcapHor hmajority (base := base) (cut := cut)
            (s := d) (D := D) hspan hsendLo hbootstrapD hpriorD hlegacyActionRootsD
            (fun r hr hrpos ht => hwindow r hr hrpos (htimeLift ht))
            (fun r hr hrpos ht p => hcapDomainV2 r hr hrpos (htimeLift ht) p)
        have hfgB : ∀ r, cut ≤ r →
            S.a r < Protocol.vote_time S.E (d + 1) →
            ∀ z ∈ rho.honest, ∀ T,
            fgConfirmationWitness S (actionStoreAt S rho z r) = some T →
            Block.compatible B T = true := by
          intro r hr ht z hz T hT
          exact Block.compatible_of_preceq_common (hB.heads x hx)
            (((hsourcesD r ((hspan.trans (Nat.sub_le _ _)).trans hr) ht).2
              hr z hz).2 T hT)
        have hrootB : ∀ z ∈ rho.honest, Block.compatible
            (Protocol.get_fg_root
              (Internal.NamedRecoveryRead.voteDutyRead S rho z
                (d + 1)).st.core.toHealing.toFG) B = true := by
          intro z hz
          have hroot := WeakFG.fgRoot_compatible_of_bootstrap_and_recentActions_at_read
            S adm hmajority hz (time := Protocol.vote_time S.E (d + 1))
            (cut := cut) (B := B) hfgB (hrootCompat z hz)
          simpa only [Internal.NamedRecoveryRead.voteDutyRead,
            NamedActionReads.confirmationReadAt,
            NamedActionReads.confirmationReadFrom,
            Protocol.NamedStore.setClock] using hroot
        have hfrontierB : ∀ z ∈ rho.honest, ∀ {C : NamedBlock V}, C.erase = B →
            (Protocol.derive_named S.E S.cfg C).h <
              (Internal.NamedRecoveryRead.voteDutyRead S rho z
                (d + 1)).st.core.h_max - 1 →
            RunBlock S rho C →
            ∀ (a : NamedAttestation V) (ta : Time) (K : NamedBlock V),
              a.val_index ∈ rho.honest →
              NamedRun.emits S rho a.val_index (Object.attest a) ta →
              ta < Protocol.vote_time S.E (d + 1) →
              a.height_pair.erase.height? =
                some ((Proofs.Optimistic.voteDutyStore S rho z (d + 1)).h_max - 1) →
              fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) =
                some (Protocol.derive_named S.E S.cfg K).T_h →
              RunBlock S rho K →
              Block.compatible C.erase
                (Protocol.derive_named S.E S.cfg K).T_h = true := by
          intro z hz C hCB hCheight hCrun a ta K ha hemit hta hrow hselected hKrun
          by_cases haold : a.round < cut
          · have hnamed := hlegacyD z hz hCB hCheight a ta K ha hemit hta hrow
              haold hselected
            have htarget := Proofs.Optimistic.derive_named_T_h_preceq S.E S.cfg K
            have hcases : NamedBlock.Preceq C K ∨ NamedBlock.Preceq K C := by
              simpa only [NamedBlock.compatible, Bool.or_eq_true] using hnamed
            rcases hcases with hCK | hKC
            · exact Block.compatible_of_preceq_common
                (Proofs.NamedWire.erase_preceq hCK) htarget
            · simp only [Block.compatible, Bool.or_eq_true]
              exact Or.inr (Block.preceq_trans htarget
                (Proofs.NamedWire.erase_preceq hKC))
          · have harecent : cut ≤ a.round := Nat.le_of_not_gt haold
            have htime : S.a a.round < Protocol.vote_time S.E (d + 1) := by
              simpa only [(Proofs.Optimistic.emits_attest_shape S hemit).2] using hta
            simpa only [hCB] using
              hfgB a.round harecent htime a.val_index ha
                (Protocol.derive_named S.E S.cfg K).T_h hselected
        have hanchorB : ∀ z ∈ rho.honest,
            Block.compatible (voterAnchorAt S rho z (d + 1)) B = true := by
          intro z hz
          by_cases hrzero : S.hc.round_of (d + 1) = 0
          · rw [WeakGenesis.voterAnchorAt_eq_fgRoot_of_round_zero
              S adm z (d + 1) hrzero]
            exact hrootB z hz
          · have hrpos : 0 < S.hc.round_of (d + 1) :=
              Nat.pos_of_ne_zero hrzero
            have hBD : Block.Preceq B D := hB.heads x hx
            have hcarriersD : ∀ k, base ≤ k → k < S.hc.round_of (d + 1) →
                ∀ u ∈ rho.honest,
                NamedRun.emits S rho u
                  (Object.attest (actionAttestationAt S rho u k)) (S.a k) →
                Block.Preceq (actionSGBlockAt S rho u k) D := by
              intro k hk hklt u hu hemit
              exact (hsourcesD k hk (action_before_vote_of_round_lt S hklt)).1
                u hu hemit
            have hfgD : ∀ r, cut ≤ r →
                S.a r < Protocol.vote_time S.E (d + 1) →
                ∀ u ∈ rho.honest, ∀ T,
                fgConfirmationWitness S (actionStoreAt S rho u r) = some T →
                Block.compatible D T = true := by
              intro r hr ht u hu T hT
              simp only [Block.compatible, Bool.or_eq_true]
              exact Or.inr (((hsourcesD r
                ((hspan.trans (Nat.sub_le _ _)).trans hr) ht).2 hr u hu).2 T hT)
            have hrootCompatD : ∀ u ∈ rho.honest, ∀ (C : NamedBlock V)
                (a : NamedAttestation V) (ta : Time),
                let R := Protocol.get_fg_root
                  (rho.storeBeforeTime S u
                    (Protocol.vote_time S.E (d + 1))).toHealing.toFG
                C ∈ (rho.storeBeforeTime S u
                  (Protocol.vote_time S.E (d + 1))).bodies →
                (Protocol.derive_named S.E S.cfg C).J = R →
                a.val_index ∈ rho.honest →
                NamedRun.emits S rho a.val_index (Object.attest a) ta →
                ta < Protocol.vote_time S.E (d + 1) →
                a.round < cut →
                a.height_pair.erase = HeightPair.target
                  (Protocol.derive_named S.E S.cfg C).h_j
                  (Protocol.derive_named S.E S.cfg C).J.root →
                fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) =
                  some R →
                Block.compatible D R = true := by
              intro u hu C a ta
              dsimp only
              intro hC hJ ha hemit hta hold hpair hT
              have hRP := hlegacyReadRoots (d + 1) hnext hupper u hu C a ta
                hC hJ ha hemit hta hold hpair hT
              have hRP' : Block.Preceq
                  (Protocol.get_fg_root
                    (rho.storeBeforeTime S u
                      (Protocol.vote_time S.E (d + 1))).toHealing.toFG) P := by
                simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
                  Proofs.Optimistic.tickStore, Protocol.NamedStore.setClock] using hRP
              simp only [Block.compatible, Bool.or_eq_true]
              exact Or.inr (Block.preceq_trans hRP' (hprev.1.heads x hx))
            have hrootD : ∀ u ∈ rho.honest, Block.compatible
                (Protocol.get_fg_root
                  (Internal.NamedRecoveryRead.voteDutyRead S rho u
                    (d + 1)).st.core.toHealing.toFG) D = true := by
              intro u hu
              have hroot := WeakFG.fgRoot_compatible_of_bootstrap_and_recentActions_at_read
                S adm hmajority hu (time := Protocol.vote_time S.E (d + 1))
                (cut := cut) (B := D) hfgD (hrootCompatD u hu)
              simpa only [Internal.NamedRecoveryRead.voteDutyRead,
                NamedActionReads.confirmationReadAt,
                NamedActionReads.confirmationReadFrom,
                Protocol.NamedStore.setClock] using hroot
            have hvoteCap : Protocol.vote_time S.E (d + 1) ≤ cap := by
              apply le_trans ?_ (hconfCap d hdlast)
              rw [← vote_time_succ_add_delta_eq_confirmation_time S.E d]
              exact Int.le_add_of_nonneg_right S.E.Δ_pos.le
            have hvoteHor : Protocol.vote_time S.E (d + 1) ≤ rho.horizon := by
              apply le_trans ?_ (hconfHor d hdlast)
              rw [← vote_time_succ_add_delta_eq_confirmation_time S.E d]
              exact Int.le_add_of_nonneg_right S.E.Δ_pos.le
            have hwindowStart : base ≤ S.hc.round_of (d + 1) - S.hc.η_SG :=
              hspan.trans (Nat.sub_le_sub_right hgap _)
            have hcapEarly : DecoupledConsensusModel.Protocol.early S.E S.hc
                (S.hc.round_of (d + 1)) .g1 ≤ cap := by
              have hdomainCapG1 : DecoupledConsensusModel.Protocol.domain S.E S.hc
                  (S.hc.round_of (d + 1)) .g1 ≤ cap := by
                rw [NamedOutageClosure.domain_g1_eq_opening]
                exact ((proposal_time_mono S.E
                  (Nat.div_mul_le_self (d + 1) S.hc.R)).trans
                    (proposal_time_lt_vote_time S.E (d + 1)).le).trans hvoteCap
              exact (NamedOutageHistory.GuardedHelpers.early_g1_le_domain_g1
                S (S.hc.round_of (d + 1))).trans hdomainCapG1
            have hinterpreted := interpretedInputs_at_voteDuty_w
              S adm hdelivery hgstLo (base := base) (r := S.hc.round_of (d + 1))
              (d := d + 1) (B := D) rfl hrpos hwindowStart (fun k hk _ => hsendLo k hk) hcarriersD hrootD
              hcapEarly hvoteHor
            have hwindowB : Internal.PhaseGrades.WindowMajorityAt S.E S.hc
                (Internal.NamedRecoveryRead.voteDutyRead S rho z
                  (d + 1)).st.core.toHealing.gradeView
                (Internal.NamedRecoveryRead.voteDutyRead S rho z (d + 1)).st.core.F
                rho.honest (S.hc.round_of (d + 1))
                (DecoupledConsensusModel.Protocol.late S.E S.hc
                  (S.hc.round_of (d + 1)) .g1) := by
              apply WeakSG.windowMajorityAt_of_awakeWindowMajority S
                (hreadWindowV2 (d + 1) hnext hupper hrpos)
              intro v hv
              obtain ⟨hvHon, k, hk, huk⟩ := WeakSG.mem_honestAwakeWindow_iff.mp hv
              obtain ⟨input, hinput, hround, hconfirmed, hfind⟩ :=
                hinterpreted z hz v hvHon k hk huk
              refine ⟨input, ?_⟩
              exact GradeCutoffMono.interpretedInputs_mono
                (Internal.NamedRecoveryRead.voteDutyRead S rho z
                  (d + 1)).st.core.toHealing.gradeView
                (Internal.NamedRecoveryRead.voteDutyRead S rho z (d + 1)).st.core.F
                S.hc.η_SG (S.hc.round_of (d + 1))
                (NamedOutageClosure.q10_early_le_late S
                  (S.hc.round_of (d + 1)) .g1) v hinput
            have hhistoryB : ∀ k ∈ Protocol.latest_window S.hc.η_SG
                (S.hc.round_of (d + 1)),
                HonestSGEmissionsCompatibleAtRound S rho k B := by
              intro k hk u hu hemit
              have hcarrierD := hcarriersD k
                (hwindowStart.trans (WeakSG.mem_latestWindow_lower_bound hk))
                (mem_latestWindow_lt hk) u hu hemit
              exact Block.compatible_of_preceq_common hcarrierD hBD
            have hbatchB := batchCompatibleAt_of_historyCutEmissions
              S adm hz hhistoryB
            let read := Internal.NamedRecoveryRead.voteDutyRead S rho z (d + 1)
            have hslot : read.st.core.s = d + 1 :=
              Proofs.Optimistic.voteDutyRead_slot S rho z (d + 1)
            rcases voterAnchorAt_cases S rho z (d + 1) with hroot |
                ⟨raw, A, hframe, hactive, hA⟩
            · rw [hroot]
              exact hrootB z hz
            · have hframeRead :
                  (DecoupledConsensusModel.Protocol.readFrame read.cache read.st.core.toHealing
                    (S.hc.round_of (d + 1))).g1 = some (some raw) := by
                simpa only [read, hslot] using hframe
              have hgrade := preparedVoteDutyG1FrameGrade_of_activePrefix
                S adm rfl hrpos hvoteHor z hz raw hframeRead A hactive
              have hanchor := WeakSG.getSgRoot_compatible_of_windowHistory_at_read
                S read (S.hc.round_of (d + 1)) B hbatchB hwindowB
                (fun raw' hframe' => by
                  have heq : raw' = raw := by
                    exact Option.some.inj (Option.some.inj
                      (hframe'.symm.trans hframeRead))
                  simpa only [heq] using hgrade)
                (hrootB z hz)
              simpa only [voterAnchorAt, Internal.PhaseGrades.nodeAnchor,
                Internal.PhaseGrades.nodeRead, Protocol.get_sg_root_with, read, hslot, hA]
                using hanchor
        have hstep := WeakGoldfish.goldfishCone_succ_of_runFrontierWitnesses
          S adm hcom hmajority hdpos hpostVote (hconfHor d hdlast) hB.cone hfrontierB hrootB hanchorB
        exact ⟨hstep.1, hstep.2⟩
      have hPnext := hpreserve P (Block.preceq_self P) hprev.1
      refine ⟨hPnext, ?_⟩
      intro q hq hqd w hw B hB
      by_cases hqd' : q < d
      · have hBold := hprev.2 q hq hqd' w hw B hB
        have hordered : Block.Preceq P B ∨ Block.Preceq B P := by
          simpa only [Block.compatible, Bool.or_eq_true] using
            Block.compatible_of_preceq_common (hprev.1.heads x hx)
              (hBold.heads x hx)
        rcases hordered with hPB | hBP
        · exact hpreserve B hPB hBold
        · exact hPnext.of_ancestor hBP
      · have hqe : q = d :=
          Nat.le_antisymm (Nat.le_of_lt_succ hqd) (Nat.le_of_not_gt hqd')
        subst q
        obtain ⟨y, hy, hBhead⟩ :=
          WeakGoldfish.genuineConfirmation_exists_honestVoteSupporter_after_gst
            S adm hcom (v := w) hw hdpos hpostVote (hconfHor d hdlast) hB
        obtain ⟨hyCommittee, hBhead⟩ := hBhead
        have hordered : Block.Preceq P B ∨ Block.Preceq B P := by
          simpa only [Block.compatible, Bool.or_eq_true] using
            Block.compatible_of_preceq_common (hprev.1.heads y hy) hBhead
        rcases hordered with hPB | hBP
        · let D := voterHeadAt S rho y d
          have hbootstrapD : ∀ r, base ≤ r → r < cut →
              S.a r < Protocol.vote_time S.E (d + 1) → ∀ z ∈ rho.honest,
              NamedRun.emits S rho z
                (Object.attest (actionAttestationAt S rho z r)) (S.a r) →
              Block.Preceq (actionSGBlockAt S rho z r) D := by
            intro r hrlo hrhi ht z hz hemit
            exact Block.preceq_trans (hsgBoot r hrlo hrhi z hz hemit)
              (hprev.1.heads y hy)
          have hpriorD : ∀ q, S.hc.opening_slot cut ≤ q → q < d →
              ∀ z ∈ rho.honest, ∀ C,
              GenuineConfirmationWith
                (NamedProfile.gradeContract
                  (Internal.NamedRecoveryRead.confirmationInputRead S rho z q).cache)
                S.E S.hc (confStore S rho z q) q C →
              Block.Preceq C D := by
            intro q hq hqd z hz C hC
            exact (hprev.2 q hq hqd z hz C hC).heads y hy
          have hlegacyActionRootsD : ∀ r, cut ≤ r →
              S.a r < Protocol.vote_time S.E (d + 1) → ∀ z ∈ rho.honest,
              ∀ (C : NamedBlock V) (a : NamedAttestation V),
              let R := Protocol.get_fg_root
                (actionStoreAt S rho z r).st.core.toHealing.toFG
              C ∈ (actionStoreAt S rho z r).st.bodies →
              (Protocol.derive_named S.E S.cfg C).J = R →
              a.val_index ∈ rho.honest →
              NamedRun.emits S rho a.val_index (Object.attest a) (S.a a.round) →
              a.round < cut →
              a.height_pair.erase = HeightPair.target
                (Protocol.derive_named S.E S.cfg C).h_j
                (Protocol.derive_named S.E S.cfg C).J.root →
              fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) =
                some R →
              Block.Preceq R D := by
            intro r hr ht z hz C a
            dsimp only
            intro hC hJ ha hemit hold hpair hT
            exact Block.preceq_trans
              (hlegacyActionRoots r hr (htimeLift ht) z hz C a hC hJ ha hemit
                hold hpair hT)
              (hprev.1.heads y hy)
          have hsources :=
            actionSources_preceq_of_priorConfirmations_and_historyCut_w
              S adm hdelivery hgstLo hcapHor hmajority (base := base) (cut := cut)
              (s := d) (D := D) hspan hsendLo hbootstrapD hpriorD hlegacyActionRootsD
              (fun r hr hrpos ht => hwindow r hr hrpos (htimeLift ht))
              (fun r hr hrpos ht p => hcapDomainV2 r hr hrpos (htimeLift ht) p)
          have hfg : ∀ r, cut ≤ r →
              S.a r < Protocol.vote_time S.E (d + 1) →
              ∀ z ∈ rho.honest, ∀ T,
              fgConfirmationWitness S (actionStoreAt S rho z r) = some T →
              Block.compatible B T = true := by
            intro r hr ht z hz T hT
            exact Block.compatible_of_preceq_common hBhead
              (((hsources r ((hspan.trans (Nat.sub_le _ _)).trans hr) ht).2
                hr z hz).2 T hT)
          have hrootCompatB : ∀ z ∈ rho.honest, ∀ (C : NamedBlock V)
              (a : NamedAttestation V) (ta : Time),
              let R := Protocol.get_fg_root
                (rho.storeBeforeTime S z (Protocol.vote_time S.E (d + 1))).toHealing.toFG
              C ∈ (rho.storeBeforeTime S z
                (Protocol.vote_time S.E (d + 1))).bodies →
              (Protocol.derive_named S.E S.cfg C).J = R →
              a.val_index ∈ rho.honest →
              NamedRun.emits S rho a.val_index (Object.attest a) ta →
              ta < Protocol.vote_time S.E (d + 1) →
              a.round < cut →
              a.height_pair.erase = HeightPair.target
                (Protocol.derive_named S.E S.cfg C).h_j
                (Protocol.derive_named S.E S.cfg C).J.root →
              fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) =
                some R →
              Block.compatible B R = true := by
            intro z hz C a ta
            dsimp only
            intro hC hJ ha hemit hta hold hpair hT
            have hRP := hlegacyReadRoots (d + 1) hnext hupper z hz C a ta
              hC hJ ha hemit hta hold hpair hT
            have hRP' : Block.Preceq
                (Protocol.get_fg_root
                  (rho.storeBeforeTime S z
                    (Protocol.vote_time S.E (d + 1))).toHealing.toFG) P := by
              simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
                Proofs.Optimistic.tickStore, Protocol.NamedStore.setClock] using hRP
            simp only [Block.compatible, Bool.or_eq_true]
            exact Or.inr (Block.preceq_trans hRP' hPB)
          have hrootB : ∀ z ∈ rho.honest, Block.compatible
              (Protocol.get_fg_root
                (Internal.NamedRecoveryRead.voteDutyRead S rho z (d + 1)).st.core.toHealing.toFG)
              B = true := by
            intro z hz
            have hroot := WeakFG.fgRoot_compatible_of_bootstrap_and_recentActions_at_read
              S adm hmajority hz (time := Protocol.vote_time S.E (d + 1)) (cut := cut)
              (B := B) hfg (hrootCompatB z hz)
            simpa only [Internal.NamedRecoveryRead.voteDutyRead,
              NamedActionReads.confirmationReadAt, NamedActionReads.confirmationReadFrom,
              Protocol.NamedStore.setClock] using hroot
          have hanchorB : ∀ z ∈ rho.honest,
              Block.compatible (voterAnchorAt S rho z (d + 1)) B = true := by
            intro z hz
            by_cases hrzero : S.hc.round_of (d + 1) = 0
            · rw [WeakGenesis.voterAnchorAt_eq_fgRoot_of_round_zero
                S adm z (d + 1) hrzero]
              exact hrootB z hz
            · have hrpos : 0 < S.hc.round_of (d + 1) :=
                Nat.pos_of_ne_zero hrzero
              have hcarriersD : ∀ k, base ≤ k → k < S.hc.round_of (d + 1) →
                  ∀ u ∈ rho.honest,
                  NamedRun.emits S rho u
                    (Object.attest (actionAttestationAt S rho u k)) (S.a k) →
                  Block.Preceq (actionSGBlockAt S rho u k) D := by
                intro k hk hklt u hu hemit
                exact (hsources k hk (action_before_vote_of_round_lt S hklt)).1
                  u hu hemit
              have hfgD : ∀ r, cut ≤ r →
                  S.a r < Protocol.vote_time S.E (d + 1) →
                  ∀ u ∈ rho.honest, ∀ T,
                  fgConfirmationWitness S (actionStoreAt S rho u r) = some T →
                  Block.compatible D T = true := by
                intro r hr ht u hu T hT
                simp only [Block.compatible, Bool.or_eq_true]
                exact Or.inr (((hsources r
                  ((hspan.trans (Nat.sub_le _ _)).trans hr) ht).2 hr u hu).2 T hT)
              have hrootCompatD : ∀ u ∈ rho.honest, ∀ (C : NamedBlock V)
                  (a : NamedAttestation V) (ta : Time),
                  let R := Protocol.get_fg_root
                    (rho.storeBeforeTime S u
                      (Protocol.vote_time S.E (d + 1))).toHealing.toFG
                  C ∈ (rho.storeBeforeTime S u
                    (Protocol.vote_time S.E (d + 1))).bodies →
                  (Protocol.derive_named S.E S.cfg C).J = R →
                  a.val_index ∈ rho.honest →
                  NamedRun.emits S rho a.val_index (Object.attest a) ta →
                  ta < Protocol.vote_time S.E (d + 1) →
                  a.round < cut →
                  a.height_pair.erase = HeightPair.target
                    (Protocol.derive_named S.E S.cfg C).h_j
                    (Protocol.derive_named S.E S.cfg C).J.root →
                  fgConfirmationWitness S
                    (actionStoreAt S rho a.val_index a.round) = some R →
                  Block.compatible D R = true := by
                intro u hu C a ta
                dsimp only
                intro hC hJ ha hemit hta hold hpair hT
                have hRP := hlegacyReadRoots (d + 1) hnext hupper u hu C a ta
                  hC hJ ha hemit hta hold hpair hT
                have hRP' : Block.Preceq
                    (Protocol.get_fg_root
                      (rho.storeBeforeTime S u
                        (Protocol.vote_time S.E (d + 1))).toHealing.toFG) P := by
                  simpa only [Proofs.Optimistic.voteDutyStore, Proofs.Optimistic.voteStore,
                    Proofs.Optimistic.tickStore, Protocol.NamedStore.setClock] using hRP
                simp only [Block.compatible, Bool.or_eq_true]
                exact Or.inr (Block.preceq_trans hRP' (hprev.1.heads y hy))
              have hrootD : ∀ u ∈ rho.honest, Block.compatible
                  (Protocol.get_fg_root
                    (Internal.NamedRecoveryRead.voteDutyRead S rho u
                      (d + 1)).st.core.toHealing.toFG) D = true := by
                intro u hu
                have hroot := WeakFG.fgRoot_compatible_of_bootstrap_and_recentActions_at_read
                  S adm hmajority hu (time := Protocol.vote_time S.E (d + 1))
                  (cut := cut) (B := D) hfgD (hrootCompatD u hu)
                simpa only [Internal.NamedRecoveryRead.voteDutyRead,
                  NamedActionReads.confirmationReadAt,
                  NamedActionReads.confirmationReadFrom,
                  Protocol.NamedStore.setClock] using hroot
              have hvoteCap : Protocol.vote_time S.E (d + 1) ≤ cap := by
                apply le_trans ?_ (hconfCap d hdlast)
                rw [← vote_time_succ_add_delta_eq_confirmation_time S.E d]
                exact Int.le_add_of_nonneg_right S.E.Δ_pos.le
              have hvoteHor : Protocol.vote_time S.E (d + 1) ≤ rho.horizon := by
                apply le_trans ?_ (hconfHor d hdlast)
                rw [← vote_time_succ_add_delta_eq_confirmation_time S.E d]
                exact Int.le_add_of_nonneg_right S.E.Δ_pos.le
              have hwindowStart : base ≤ S.hc.round_of (d + 1) - S.hc.η_SG :=
                hspan.trans (Nat.sub_le_sub_right hgap _)
              have hcapEarly : DecoupledConsensusModel.Protocol.early S.E S.hc
                  (S.hc.round_of (d + 1)) .g1 ≤ cap := by
                have hdomainCapG1 : DecoupledConsensusModel.Protocol.domain S.E S.hc
                    (S.hc.round_of (d + 1)) .g1 ≤ cap := by
                  rw [NamedOutageClosure.domain_g1_eq_opening]
                  exact ((proposal_time_mono S.E
                    (Nat.div_mul_le_self (d + 1) S.hc.R)).trans
                      (proposal_time_lt_vote_time S.E (d + 1)).le).trans hvoteCap
                exact (NamedOutageHistory.GuardedHelpers.early_g1_le_domain_g1
                  S (S.hc.round_of (d + 1))).trans hdomainCapG1
              have hinterpreted := interpretedInputs_at_voteDuty_w
                S adm hdelivery hgstLo (base := base) (r := S.hc.round_of (d + 1))
                (d := d + 1) (B := D) rfl hrpos hwindowStart (fun k hk _ => hsendLo k hk) hcarriersD hrootD
                hcapEarly hvoteHor
              have hwindowB : Internal.PhaseGrades.WindowMajorityAt S.E S.hc
                  (Internal.NamedRecoveryRead.voteDutyRead S rho z
                    (d + 1)).st.core.toHealing.gradeView
                  (Internal.NamedRecoveryRead.voteDutyRead S rho z (d + 1)).st.core.F
                  rho.honest (S.hc.round_of (d + 1))
                  (DecoupledConsensusModel.Protocol.late S.E S.hc
                    (S.hc.round_of (d + 1)) .g1) := by
                apply WeakSG.windowMajorityAt_of_awakeWindowMajority S
                  (hreadWindowV2 (d + 1) hnext hupper hrpos)
                intro v hv
                obtain ⟨hvHon, k, hk, huk⟩ := WeakSG.mem_honestAwakeWindow_iff.mp hv
                obtain ⟨input, hinput, hround, hconfirmed, hfind⟩ :=
                  hinterpreted z hz v hvHon k hk huk
                refine ⟨input, ?_⟩
                exact GradeCutoffMono.interpretedInputs_mono
                  (Internal.NamedRecoveryRead.voteDutyRead S rho z
                    (d + 1)).st.core.toHealing.gradeView
                  (Internal.NamedRecoveryRead.voteDutyRead S rho z (d + 1)).st.core.F
                  S.hc.η_SG (S.hc.round_of (d + 1))
                  (NamedOutageClosure.q10_early_le_late S
                    (S.hc.round_of (d + 1)) .g1) v hinput
              have hhistoryB : ∀ k ∈ Protocol.latest_window S.hc.η_SG
                  (S.hc.round_of (d + 1)),
                  HonestSGEmissionsCompatibleAtRound S rho k B := by
                intro k hk u hu hemit
                have hcarrierD := hcarriersD k
                  (hwindowStart.trans (WeakSG.mem_latestWindow_lower_bound hk))
                  (mem_latestWindow_lt hk) u hu hemit
                exact Block.compatible_of_preceq_common hcarrierD hBhead
              have hbatchB := batchCompatibleAt_of_historyCutEmissions
                S adm hz hhistoryB
              let read := Internal.NamedRecoveryRead.voteDutyRead S rho z (d + 1)
              have hslot : read.st.core.s = d + 1 :=
                Proofs.Optimistic.voteDutyRead_slot S rho z (d + 1)
              rcases voterAnchorAt_cases S rho z (d + 1) with hroot |
                  ⟨raw, A, hframe, hactive, hA⟩
              · rw [hroot]
                exact hrootB z hz
              · have hframeRead :
                    (DecoupledConsensusModel.Protocol.readFrame read.cache read.st.core.toHealing
                      (S.hc.round_of (d + 1))).g1 = some (some raw) := by
                  simpa only [read, hslot] using hframe
                have hgrade := preparedVoteDutyG1FrameGrade_of_activePrefix
                  S adm rfl hrpos hvoteHor z hz raw hframeRead A hactive
                have hanchor := WeakSG.getSgRoot_compatible_of_windowHistory_at_read
                  S read (S.hc.round_of (d + 1)) B hbatchB hwindowB
                  (fun raw' hframe' => by
                    have heq : raw' = raw := by
                      exact Option.some.inj (Option.some.inj
                        (hframe'.symm.trans hframeRead))
                    simpa only [heq] using hgrade)
                  (hrootB z hz)
                simpa only [voterAnchorAt, Internal.PhaseGrades.nodeAnchor,
                  Internal.PhaseGrades.nodeRead, Protocol.get_sg_root_with,
                  read, hslot, hA] using hanchor
          have hfrontierB : ∀ z ∈ rho.honest, ∀ {C : NamedBlock V}, C.erase = B →
              (Protocol.derive_named S.E S.cfg C).h <
                (Internal.NamedRecoveryRead.voteDutyRead S rho z (d + 1)).st.core.h_max - 1 →
              RunBlock S rho C →
              ∀ (a : NamedAttestation V) (ta : Time) (K : NamedBlock V),
                a.val_index ∈ rho.honest →
                NamedRun.emits S rho a.val_index (Object.attest a) ta →
                ta < Protocol.vote_time S.E (d + 1) →
                a.height_pair.erase.height? =
                  some ((Proofs.Optimistic.voteDutyStore S rho z (d + 1)).h_max - 1) →
                fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) =
                  some (Protocol.derive_named S.E S.cfg K).T_h →
                RunBlock S rho K →
                Block.compatible C.erase
                  (Protocol.derive_named S.E S.cfg K).T_h = true := by
            intro z hz C hCB hCheight hCrun a ta K ha hemit hta hrow hselected hKrun
            by_cases haold : a.round < cut
            · have hnamed := hnoOldFrontier (d + 1) hnext hupper C
                (by simpa only [hCB] using hPB) z hz hCheight a ta K ha hemit hta
                hrow haold hselected
              have htarget := Proofs.Optimistic.derive_named_T_h_preceq S.E S.cfg K
              have hcases : NamedBlock.Preceq C K ∨ NamedBlock.Preceq K C := by
                simpa only [NamedBlock.compatible, Bool.or_eq_true] using hnamed
              rcases hcases with hCK | hKC
              · exact Block.compatible_of_preceq_common
                  (Proofs.NamedWire.erase_preceq hCK) htarget
              · simp only [Block.compatible, Bool.or_eq_true]
                exact Or.inr (Block.preceq_trans htarget
                  (Proofs.NamedWire.erase_preceq hKC))
            · have harecent : cut ≤ a.round := Nat.le_of_not_gt haold
              have htime : S.a a.round < Protocol.vote_time S.E (d + 1) := by
                simpa only [(Proofs.Optimistic.emits_attest_shape S hemit).2] using hta
              simpa only [hCB] using
                hfg a.round harecent htime a.val_index ha
                  (Protocol.derive_named S.E S.cfg K).T_h hselected
          exact WeakGoldfish.protectedVoteSlot_succ_of_genuineConfirmationWith
            S adm hcom hmajority (v := w) hw hdpos hpostD
            (hconfHor d hdlast) hB hfrontierB hrootB hanchorB
        · exact hPnext.of_ancestor hBP



#print axioms protectedVoteSlots_of_historyCut_v2_w
theorem protectedVoteSlots_of_historyCut_v2_after_gst
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    (hcom : HonestCommittees S rho.honest)
    (hmajority : HonestWeightMajority S rho.honest)
    {base cut : Round} {start last : Slot} {P : Block V}
    (hspan : base ≤ cut - S.hc.η_SG)
    (hbasePost : S.E.t_GST ≤ S.a base)
    (hstartpos : 0 < start)
    (hsettled : S.hc.opening_slot cut ≤ start)
    (hpost : S.E.t_GST ≤ Protocol.proposal_time S.E start)
    (hhor : Protocol.confirmation_time S.E last ≤ rho.horizon)
    (hseed : ProtectedVoteSlot S rho start P)
    (hnoOldFrontier : NoOldFrontierAtCut S rho cut start last P)
    (hsgBoot : ∀ r, base ≤ r → r < cut → ∀ w ∈ rho.honest,
      NamedRun.emits S rho w
        (Object.attest (actionAttestationAt S rho w r)) (S.a r) →
      Block.Preceq (actionSGBlockAt S rho w r) P)
    (hconfBoot : ∀ q, S.hc.opening_slot cut ≤ q → q < start →
      ∀ w ∈ rho.honest, ∀ B,
      GenuineConfirmationWith
        (NamedProfile.gradeContract
          (Internal.NamedRecoveryRead.confirmationInputRead S rho w q).cache)
        S.E S.hc (confStore S rho w q) q B →
      Block.Preceq B P)
    (hlegacyActionRoots : ∀ r, cut ≤ r →
      S.a r < Protocol.vote_time S.E (last + 1) → ∀ w ∈ rho.honest,
      ∀ (C : NamedBlock V) (a : NamedAttestation V),
      let R := Protocol.get_fg_root
        (actionStoreAt S rho w r).st.core.toHealing.toFG
      C ∈ (actionStoreAt S rho w r).st.bodies →
      (Protocol.derive_named S.E S.cfg C).J = R →
      a.val_index ∈ rho.honest →
      NamedRun.emits S rho a.val_index (Object.attest a) (S.a a.round) →
      a.round < cut →
      a.height_pair.erase = HeightPair.target
        (Protocol.derive_named S.E S.cfg C).h_j
        (Protocol.derive_named S.E S.cfg C).J.root →
      fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) =
        some R →
      Block.Preceq R P)
    (hlegacyReadRoots : ∀ d, start < d → d ≤ last + 1 →
      ∀ w ∈ rho.honest,
      ∀ (C : NamedBlock V) (a : NamedAttestation V) (ta : Time),
      let R := Protocol.get_fg_root
        (voteDutyStore S rho w d).toHealing.toFG
      C ∈ (rho.storeBeforeTime S w (Protocol.vote_time S.E d)).bodies →
      (Protocol.derive_named S.E S.cfg C).J = R →
      a.val_index ∈ rho.honest →
      NamedRun.emits S rho a.val_index (Object.attest a) ta →
      ta < Protocol.vote_time S.E d →
      a.round < cut →
      a.height_pair.erase = HeightPair.target
        (Protocol.derive_named S.E S.cfg C).h_j
        (Protocol.derive_named S.E S.cfg C).J.root →
      fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) =
        some R →
      Block.Preceq R P)
    (hwindow : ∀ r, cut ≤ r → 0 < r →
      S.a r < Protocol.vote_time S.E (last + 1) →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG r)
    (hreadWindowV2 : ∀ d, start < d → d ≤ last + 1 →
      0 < S.hc.round_of d →
      AwakeWindowMajority S.E (fun v => (S.node v).awake)
        rho.honest S.hc.η_SG (S.hc.round_of d))
    (hcapDomainV2 : ∀ r, cut ≤ r → 0 < r →
      S.a r < Protocol.vote_time S.E (last + 1) → ∀ p,
      DecoupledConsensusModel.Protocol.domain S.E S.hc r p ≤ rho.horizon) :
    ∀ d, start ≤ d → d ≤ last + 1 →
      ProtectedVoteSlot S rho d P ∧
      (∀ q, S.hc.opening_slot cut ≤ q → q < d →
        ∀ w ∈ rho.honest, ∀ B,
        GenuineConfirmationWith
          (NamedProfile.gradeContract
            (Internal.NamedRecoveryRead.confirmationInputRead S rho w q).cache)
          S.E S.hc (confStore S rho w q) q B →
          ProtectedVoteSlot S rho d B) := by
  have hsend : ∀ k, base ≤ k → S.E.t_GST ≤ S.a k := by
    intro k hk
    exact hbasePost.trans (Assembly.a_mono S hk)
  exact protectedVoteSlots_of_historyCut_v2_w S adm
    (NamedOutageClosure.healthyWindowDelivery_after_gst S rho adm)
    (le_refl _) (le_refl _) hcom hmajority hspan hsend hstartpos hsettled
    hpost hhor hhor hseed hnoOldFrontier hsgBoot hconfBoot
    hlegacyActionRoots hlegacyReadRoots hwindow hreadWindowV2 hcapDomainV2

#print axioms protectedVoteSlots_of_historyCut_v2_after_gst



















end WeakJoint
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
