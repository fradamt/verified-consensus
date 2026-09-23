module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.SafetyCompatibilityJoin

@[expose] public section

/-!
# Joint slot induction for safety

The bootstrap supplies a protected block, finite SG/confirmation history,
and closure of relevant old FG roots below that block. The suffix derives
all later action sources and protects each new genuine confirmation.
These bootstrap inputs still need a recovery-exit producer. They are not
extra assumptions accepted by the final healing theorem.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Protocol
open Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]

/-- The actual vote cone and every honest vote-duty head protect B at d. -/
structure ProtectedVoteSlot (S : Setup V) (rho : Run V) (d : Slot) (B : Block V) : Prop where
  heads : ∀ w ∈ rho.honest, Block.Preceq B (voterHeadAt S rho w d)
  cone : NamedHonestVotesCone S rho d (fun X => Block.Preceq B X)

/-- Protection of a block also protects each of its ancestors. -/
theorem ProtectedVoteSlot.of_ancestor
    {S : Setup V} {rho : Run V} {d : Slot} {B P : Block V}
    (hP : ProtectedVoteSlot S rho d P) (hBP : Block.Preceq B P) :
    ProtectedVoteSlot S rho d B := by
  refine ⟨fun w hw => Block.preceq_trans hBP (hP.heads w hw), ?_⟩
  intro w hw hwc
  obtain ⟨X, hPX, hX, hemit⟩ := hP.cone w hw hwc
  exact ⟨X, Block.preceq_trans hBP hPX, hX, hemit⟩


/- /-- Fold the two safety steps. All later genuine confirmations remain below
honest vote heads; SG and FG compatibility are derived inside the fold.
Only finite bootstrap histories and relevant previous-root closure remain as
safety inputs. The previous height-row cap is the actual honest frontier at the
last possible previous action. This theorem does not assume later confirmations,
SG outputs, or recent FG witnesses are safe. -/
/-- Fold the two safety steps. All later genuine confirmations remain below
honest vote heads; SG and FG compatibility are derived inside the fold.

Only finite bootstrap histories and relevant old-root closure remain as
safety inputs. the prior height-row cap is the actual honest frontier at the
last possible old action. This theorem does not assume later confirmations,
SG outputs, or recent FG witnesses are safe. -/
theorem protectedVoteSlots_of_bootstrap
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hcom: HonestCommittees S rho.honest)
    (hmajority: HonestWeightMajority S rho.honest)
    {base: Round} {start last: Slot} {P: Block V}
    (hsettled: S.hc.opening_slot (base + S.hc.η_SG) ≤ start)
    (hpost: S.E.t_GST ≤ Protocol.proposal_time S.E start)
    (hhor: Protocol.confirmation_time S.E last ≤ rho.horizon)
    (hseed: ProtectedVoteSlot S rho start P)
    (hheightCap: honestHMaxAt S rho (S.a (base + S.hc.η_SG - 1)) ≤
      (derived_state S.E S.cfg P).h)
    (hsgBoot: ∀ r, base ≤ r → r < base + S.hc.η_SG → ∀ w ∈ rho.honest,
      rho.emits S w (Object.attest (actionAttestationAt S rho w r)) (S.a r) →
        Block.Preceq (actionSGBlockAt S rho w r) P)
    (hconfBoot: ∀ q, S.hc.opening_slot (base + S.hc.η_SG) ≤ q → q < start →
      ∀ w ∈ rho.honest, ∀ B,
      GenuineConfirmation (contract:= Protocol.GradeContract.current) S.E S.hc (confStore S rho w q) q B → Block.Preceq B P)
    (hlegacyActionRoots: ∀ r, base + S.hc.η_SG ≤ r →
      S.a r < Protocol.vote_time S.E (last + 1) → ∀ w ∈ rho.honest,
      ∀ a: CombinedAttestation V,
      let R:= Protocol.get_fg_root (actionStoreAt S rho w r).toHealing.toFG
      a.val_index ∈ rho.honest →
      rho.emits S a.val_index (Object.attest a) (S.a a.round) →
      a.round < base + S.hc.η_SG →
      a.height_pair = HeightPair.target (derived_state S.E S.cfg R).h R.root →
      fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) = some R →
        Block.Preceq R P)
    (hlegacyReadRoots: ∀ d, start < d → d ≤ last + 1 → ∀ w ∈ rho.honest,
      ∀ (a: CombinedAttestation V) (ta: Time),
      let R:= Protocol.get_fg_root (voteDutyStore S rho w d).toHealing.toFG
      a.val_index ∈ rho.honest → rho.emits S a.val_index (Object.attest a) ta →
      ta < Protocol.vote_time S.E d → a.round < base + S.hc.η_SG →
      a.height_pair = HeightPair.target (derived_state S.E S.cfg R).h R.root →
      fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) = some R →
        Block.Preceq R P)
    (hwindow: ∀ r, base + S.hc.η_SG ≤ r →
      S.a r < Protocol.vote_time S.E (last + 1) → ∀ w ∈ rho.honest,
      rho.emits S w (Object.attest (actionAttestationAt S rho w r)) (S.a r) →
        2 * S.E.electorate.weightOf
          (Protocol.represented_set (actionStoreAt S rho w r).toHealing.sg_votes
            S.hc.η_SG r \ rho.honest) <
        Protocol.W_r S.E (actionStoreAt S rho w r).toHealing.sg_votes S.hc.η_SG r)
    (hreadWindow: ∀ d, start < d → d ≤ last + 1 → ∀ w ∈ rho.honest,
      2 * S.E.electorate.weightOf
        (Protocol.represented_set (voteDutyStore S rho w d).toHealing.sg_votes
          S.hc.η_SG (S.hc.round_of d) \ rho.honest) <
      Protocol.W_r S.E (voteDutyStore S rho w d).toHealing.sg_votes
        S.hc.η_SG (S.hc.round_of d)):
    ∀ d, start ≤ d → d ≤ last + 1 →
      ProtectedVoteSlot S rho d P ∧
      (∀ q, S.hc.opening_slot (base + S.hc.η_SG) ≤ q → q < d →
        ∀ w ∈ rho.honest, ∀ B,
        GenuineConfirmation (contract:= Protocol.GradeContract.current) S.E S.hc (confStore S rho w q) q B →
          ProtectedVoteSlot S rho d B):= by
  have hRpos: 0 < S.hc.R:= lt_of_lt_of_le (by decide: 0 < 2) S.hc.R_ge_two
  have hstartpos: 0 < start:= by
    have heta:= S.hc.η_SG_ge_one
    have hcutpos: 0 < base + S.hc.η_SG:=
      (lt_of_lt_of_le (by decide: 0 < 1) heta).trans_le (Nat.le_add_left _ _)
    exact (Nat.mul_pos hcutpos hRpos).trans_le hsettled
  have hconfHor: ∀ k, k ≤ last → Protocol.confirmation_time S.E k ≤ rho.horizon:= by
    intro k hk
    apply le_trans ?_ hhor
    rw [Protocol.confirmation_time_eq_support_cutoff_succ,
      Protocol.confirmation_time_eq_support_cutoff_succ]
    exact support_cutoff_mono S.E (Nat.add_le_add_right hk 1)
  intro d hd
  induction d, hd using Nat.le_induction with
  | base =>
      intro _
      exact ⟨hseed, fun q hq hqs w hw B hB =>
        hseed.of_ancestor (hconfBoot q hq hqs w hw B hB)⟩
  | succ d hd ih =>
      intro hupper
      have hdlast: d ≤ last:= Nat.le_of_succ_le_succ hupper
      have hprev:= ih (hdlast.trans (Nat.le_succ last))
      have hdpos: 0 < d:= hstartpos.trans_le hd
      have hnext: start < d + 1:= Nat.lt_succ_of_le hd
      have hpostD:= hpost.trans (proposal_time_mono S.E hd)
      have hpostVote:= hpostD.trans (le_of_lt (proposal_time_lt_vote_time S.E d))
      have hgap: base + S.hc.η_SG ≤ S.hc.round_of (d + 1):= by
        change base + S.hc.η_SG ≤ (d + 1) / S.hc.R
        exact (Nat.le_div_iff_mul_le hRpos).2
          (hsettled.trans (hd.trans (Nat.le_succ d)))
      have htimeMax:= vote_time_mono_slots S.E (Nat.add_le_add_right hdlast 1)
      have htimeLift: ∀ {t: Time}, t < Protocol.vote_time S.E (d + 1) →
          t < Protocol.vote_time S.E (last + 1):= fun ht => ht.trans_le htimeMax
      have hnonempty: 0 < ((S.E.committee d) ∩ rho.honest).card:= by
        have hm:= hcom d
        omega
      obtain ⟨x, hxmem⟩:= Finset.card_pos.mp hnonempty
      have hx: x ∈ rho.honest:= (Finset.mem_inter.mp hxmem).2
      have hreadCompat (B: Block V) (hPB: Block.Preceq P B):
          ∀ w ∈ rho.honest, ∀ (a: CombinedAttestation V) (ta: Time),
          let R:= Protocol.get_fg_root (voteDutyStore S rho w (d + 1)).toHealing.toFG
          a.val_index ∈ rho.honest → rho.emits S a.val_index (Object.attest a) ta →
          ta < Protocol.vote_time S.E (d + 1) → a.round < base + S.hc.η_SG →
          a.height_pair = HeightPair.target (derived_state S.E S.cfg R).h R.root →
          fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) = some R →
            Block.compatible B R = true:= by
        intro w hw a ta
        dsimp only
        intro ha hemit ht hold hpair hT
        have hRP:= hlegacyReadRoots (d + 1) hnext hupper w hw a ta ha hemit ht hold hpair hT
        simp only [Block.compatible, Bool.or_eq_true]
        exact Or.inr (Block.preceq_trans hRP hPB)
      have hnoOldFrontier (B: Block V) (hPB: Block.Preceq P B):
          ∀ w ∈ rho.honest,
          (derived_state S.E S.cfg B).h < (voteDutyStore S rho w (d + 1)).h_max - 1 →
          ∀ (a: CombinedAttestation V) (ta: Time) (T: Block V),
          a.val_index ∈ rho.honest → rho.emits S a.val_index (Object.attest a) ta →
          ta < Protocol.vote_time S.E (d + 1) →
          a.height_pair.height? = some ((voteDutyStore S rho w (d + 1)).h_max - 1) →
          a.round < base + S.hc.η_SG →
          fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) = some T →
            Block.compatible B T = true:= by
        intro w _ hhigh a ta T ha hemit _ hheight hold _
        have ht: ta ≤ S.a (base + S.hc.η_SG - 1):= by
          rw [(emits_attest_shape S hemit).2]
          exact Assembly.a_mono S (Nat.le_sub_one_of_lt hold)
        have hbound:= honestEmittedHeight_le_honestHMaxAt S adm ha hemit hheight ht
        have hfloor:= hheightCap.trans (Protocol.derived_h_mono S.E S.cfg hPB)
        exact False.elim ((Nat.not_lt_of_ge (hbound.trans hfloor)) hhigh)
      have hpreserve (B: Block V) (hPB: Block.Preceq P B)
          (hB: ProtectedVoteSlot S rho d B): ProtectedVoteSlot S rho (d + 1) B:= by
        have hstep:= goldfishCone_succ_of_priorConfirmationSafety S adm hcom hmajority
          hdpos hpostVote (hconfHor d hdlast) hB.cone (hB.heads x hx)
          (fun r hr hboot _ w hw hemit =>
            Block.preceq_trans (hsgBoot r hr hboot w hw hemit) (hprev.1.heads x hx))
          (fun q hq hqd w hw C hC => (hprev.2 q hq hqd w hw C hC).heads x hx)
          (fun r hr ht w hw a ha hemit hold hpair hT => Block.preceq_trans
            (hlegacyActionRoots r hr (htimeLift ht) w hw a ha hemit hold hpair hT)
            (hprev.1.heads x hx))
          (fun r hr ht w hw hemit => hwindow r hr (htimeLift ht) w hw hemit)
          hgap (hreadWindow (d + 1) hnext hupper)
          (hreadCompat B hPB) (hnoOldFrontier B hPB)
        exact ⟨hstep.1, hstep.2⟩
      have hPnext:= hpreserve P (Block.preceq_self P) hprev.1
      refine ⟨hPnext, ?_⟩
      intro q hq hqd w hw B hB
      by_cases hqd': q < d
      · have hBold:= hprev.2 q hq hqd' w hw B hB
        have hordered: Block.Preceq P B ∨ Block.Preceq B P:= by
          simpa only [Block.compatible, Bool.or_eq_true] using
            Block.compatible_of_preceq_common (hprev.1.heads x hx) (hBold.heads x hx)
        rcases hordered with hPB | hBP
        · exact hpreserve B hPB hBold
        · exact hPnext.of_ancestor hBP
      · have hqe: q = d:=
          Nat.le_antisymm (Nat.le_of_lt_succ hqd) (Nat.le_of_not_gt hqd')
        subst q
        obtain ⟨y, hy, _, hBY⟩:= genuineConfirmation_exists_honestVoteSupporter_after_gst
          S adm hcom hw hdpos hpostVote (hconfHor d hdlast) hB
        have hordered: Block.Preceq P B ∨ Block.Preceq B P:= by
          simpa only [Block.compatible, Bool.or_eq_true] using
            Block.compatible_of_preceq_common (hprev.1.heads y hy) hBY
        rcases hordered with hPB | hBP
        · have hstep:= goldfishCone_of_priorConfirmationSafety S adm hcom hmajority hw
            hdpos hpostD (hconfHor d hdlast) hB
            (fun r hr hboot _ v hv hemit z hz _ =>
              Block.preceq_trans (hsgBoot r hr hboot v hv hemit) (hprev.1.heads z hz))
            (fun k hk hkd v hv C hC z hz _ => (hprev.2 k hk hkd v hv C hC).heads z hz)
            (fun r hr ht v hv a ha hemit hold hpair hT z hz _ => Block.preceq_trans
              (hlegacyActionRoots r hr (htimeLift ht) v hv a ha hemit hold hpair hT)
              (hprev.1.heads z hz))
            (fun r hr ht v hv hemit => hwindow r hr (htimeLift ht) v hv hemit)
            hgap (hreadWindow (d + 1) hnext hupper)
            (hreadCompat B hPB) (hnoOldFrontier B hPB)
          exact ⟨hstep.1, hstep.2⟩
        · exact hPnext.of_ancestor hBP
-/


/-
/-- The slot history exports safety of later round-action outputs. The
action's root and live confirmation, its actual SG output, and its exact FG
witness all precede every later honest vote-duty head. An FG timeout keeps
the same witness. Only the already-proved genuine-confirmation slot history
is used; SG/FG safety is not an extra history premise. -/
theorem roundActionOutputs_preceq_laterVoteHead
    (S: Setup V) {rho: Run V} (adm: Admissible S rho)
    (hmajority: HonestWeightMajority S rho.honest)
    {base r: Round} {d: Slot} {P: Block V}
    (hgap: base + S.hc.η_SG ≤ r)
    (hfuture: S.a r < Protocol.vote_time S.E d)
    (hP: ProtectedVoteSlot S rho d P)
    (hconfirmations: ∀ q, S.hc.opening_slot (base + S.hc.η_SG) ≤ q → q < d →
      ∀ w ∈ rho.honest, ∀ B,
      GenuineConfirmation (contract:= Protocol.GradeContract.current) S.E S.hc (confStore S rho w q) q B →
        ProtectedVoteSlot S rho d B)
    (hsgBoot: ∀ k, base ≤ k → k < base + S.hc.η_SG → ∀ w ∈ rho.honest,
      rho.emits S w (Object.attest (actionAttestationAt S rho w k)) (S.a k) →
        Block.Preceq (actionSGBlockAt S rho w k) P)
    (hlegacyActionRoots: ∀ k, base + S.hc.η_SG ≤ k →
      S.a k < Protocol.vote_time S.E (d + 1) → ∀ w ∈ rho.honest,
      ∀ a: CombinedAttestation V,
      let R:= Protocol.get_fg_root (actionStoreAt S rho w k).toHealing.toFG
      a.val_index ∈ rho.honest →
      rho.emits S a.val_index (Object.attest a) (S.a a.round) →
      a.round < base + S.hc.η_SG →
      a.height_pair = HeightPair.target (derived_state S.E S.cfg R).h R.root →
      fgConfirmationWitness S (actionStoreAt S rho a.val_index a.round) = some R →
        Block.Preceq R P)
    (hwindow: ∀ k, base + S.hc.η_SG ≤ k →
      S.a k < Protocol.vote_time S.E (d + 1) → ∀ w ∈ rho.honest,
      rho.emits S w (Object.attest (actionAttestationAt S rho w k)) (S.a k) →
        2 * S.E.electorate.weightOf
          (Protocol.represented_set (actionStoreAt S rho w k).toHealing.sg_votes
            S.hc.η_SG k \ rho.honest) <
        Protocol.W_r S.E (actionStoreAt S rho w k).toHealing.sg_votes S.hc.η_SG k):
    ∀ w ∈ rho.honest, ∀ x ∈ rho.honest,
      Block.Preceq (Protocol.get_fg_root (actionStoreAt S rho w r).toHealing.toFG)
        (voteDutyHead S rho x d) ∧
      Block.Preceq (actionStoreAt S rho w r).live_confirmed (voteDutyHead S rho x d) ∧
      (rho.emits S w (Object.attest (actionAttestationAt S rho w r)) (S.a r) →
        Block.Preceq (actionSGBlockAt S rho w r) (voteDutyHead S rho x d)) ∧
      (∀ T, fgConfirmationWitness S (actionStoreAt S rho w r) = some T →
        Block.Preceq T (voteDutyHead S rho x d)):= by
  intro w hw x hx
  have haction: S.a r < Protocol.vote_time S.E (d + 1):=
    hfuture.trans_le (vote_time_mono_slots S.E (Nat.le_succ d))
  have hprior: ∀ q, S.hc.opening_slot (base + S.hc.η_SG) ≤ q → q < d →
      ∀ v ∈ rho.honest, ∀ C,
      GenuineConfirmation (contract:= Protocol.GradeContract.current) S.E S.hc (confStore S rho v q) q C →
        Block.Preceq C (voteDutyHead S rho x d):=
    fun q hq hqd v hv C hC => (hconfirmations q hq hqd v hv C hC).heads x hx
  have hsources:= actionSources_preceq_of_priorConfirmations_and_bootstrap S adm hmajority
    (fun k hk hboot _ v hv hemit =>
      Block.preceq_trans (hsgBoot k hk hboot v hv hemit) (hP.heads x hx))
    hprior (fun k hk ht v hv a ha hemit hold hpair hT => Block.preceq_trans
      (hlegacyActionRoots k hk ht v hv a ha hemit hold hpair hT) (hP.heads x hx)) hwindow
  have hcurrent:= hsources r ((Nat.le_add_right base S.hc.η_SG).trans hgap) haction
  have hroot:= (hcurrent.2 hgap w hw).1
  have hstart: S.hc.opening_slot (base + S.hc.η_SG) ≤ S.hc.opening_slot r:=
    Nat.mul_le_mul_right S.hc.R hgap
  exact ⟨hroot, actionLiveConfirmed_preceq_of_priorConfirmations S rho hstart haction
    hprior hw hroot, hcurrent.1 w hw, (hcurrent.2 hgap w hw).2⟩
-/

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
