module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.W4NamedMixedStep
public import DecoupledConsensusProofs.Execution.W4NamedFoldSupplies

@[expose] public section

/-!
# Named fold iteration after the boundary

This is the horizon-sensitive named iteration. It keeps the ceiling and
ordinary schedule records separate. The ordinary arm uses the additive
`w4FoldAtEverySlot_of_initial` consumer, whose adoption supply is discharged
by `movingSlotAdoptionSupplyAt_of_foldStep`; the ceiling and mixed arms use
their own named ceiling records and entry producers.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface Internal.NamedRecoveryRead
open Protocol Proofs.HealingLemmas
open Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]
variable {delayExtra : Nat}

private theorem w4nfi_confirmation_time_mono
    (E : Env V) {a b : Slot} (hab : a ≤ b) :
    Protocol.confirmation_time E a ≤ Protocol.confirmation_time E b :=
  Int.add_le_add_right (Protocol.proposal_time_mono E hab) _


private theorem w4nfi_vote_time_succ_le_confirmation_time
    (E : Env V) (s : Slot) :
    Protocol.vote_time E (s + 1) ≤ Protocol.confirmation_time E s := by
  rw [← Protocol.vote_time_succ_add_delta_eq_confirmation_time E s]
  exact Int.le_add_of_nonneg_right E.Δ_pos.le


/-- Iterate a named fold through the ceiling, mixed, and ordinary schedule
regions. The initial fold is supplied at the caller's boundary cursor; each
step preserves its base-family equality. -/
theorem w4MovingSlotFoldAtN_iterate_hybrid_named
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    (hfb : BelowOneThird S rho.honest)
    {rGST gap : Round} (hrec : MultiProposerRecurrence S rho gap)
    (hdelay : TimeoutDelayBound S delayExtra)
    (hpost : S.E.t_GST ≤ S.a rGST)
    {q : Round} {D : NamedBlock V} {M0 : Height}
    (hR0pos : 0 < S.hc.round_of (S.hc.opening_slot q + 3))
    (hpostBase : S.E.t_GST ≤
      S.a (S.hc.round_of (S.hc.opening_slot q + 3) - 1))
    (hcarrierBase : ∀ r : Round,
      S.hc.round_of (S.hc.opening_slot q + 3) = r + 1 →
      ∀ u ∈ rho.honest,
        Block.Preceq (actionSGBlockAt S rho u r) D.erase)
    (hcarrierQ : ∀ u ∈ rho.honest,
      Block.Preceq (actionSGBlockAt S rho u q) D.erase)
    {c : Slot} {F : Slot → Block V} {End : Block V}
    (hfold : MovingSlotFoldAtN S rho
      (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2)) M0
      (S.hc.opening_slot q + 3) (c + 1) F End)
    (hsBase : S.hc.opening_slot q + 3 ≤ c + 1)
    (hbaseEq : F (S.hc.opening_slot q + 3) = D.erase)
    (hdeadline : ∀ {j : Slot},
      S.hc.opening_slot q + 3 ≤ j + 1 →
      S.hc.opening_slot
        (fgSafetyProgressDeadline S rho rGST gap delayExtra + 2) ≤ j + 2) :
    ∀ n : Nat,
      Protocol.confirmation_time S.E (c + n) ≤ rho.horizon →
      ∃ (F' : Slot → Block V) (End' : Block V),
        MovingSlotFoldAtN S rho
          (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2)) M0
          (S.hc.opening_slot q + 3) (c + 1 + n) F' End' ∧
        F' (S.hc.opening_slot q + 3) = D.erase := by
  obtain ⟨v, hv⟩ := honest_nonempty_of_honestCommittees hcom
  have hR0q : S.hc.round_of (S.hc.opening_slot q + 3) - 1 ≤ q := by
    have hupper := w4_handoffBaseRound_bounds S q |>.2
    have hpos := hR0pos
    exact Nat.lt_succ_iff.mp
      ((Nat.sub_lt hpos (by decide : 0 < 1)).trans_le hupper)
  have hpostQ : S.E.t_GST ≤ S.a q :=
    hpostBase.trans ((action_strictMono S).monotone hR0q)
  have hpostQ1 : S.E.t_GST ≤ S.a (q + 1) :=
    hpostQ.trans ((action_strictMono S).monotone (Nat.le_succ q))
  intro n
  induction n generalizing c F End with
  | zero =>
      intro _hhor
      exact ⟨F, End, by simpa only [Nat.add_zero] using hfold, hbaseEq⟩
  | succ n ih =>
      intro hhor
      have hcTarget : c + 1 ≤ c + (n + 1) := by
        exact Nat.add_le_add_left (Nat.succ_le_succ (Nat.zero_le n)) c
      have hhorC : Protocol.confirmation_time S.E c ≤ rho.horizon :=
        (w4nfi_confirmation_time_mono S.E
          (Nat.le_trans (Nat.le_succ c) hcTarget)).trans hhor
      have hhorNext : Protocol.confirmation_time S.E (c + 1) ≤
          rho.horizon :=
        (w4nfi_confirmation_time_mono S.E hcTarget).trans hhor
      have hs0c : S.hc.opening_slot q + 3 ≤ c + 1 := hsBase
      have hDPrev : Block.Preceq D.erase (F (c + 1)) := by
        rw [← hbaseEq]
        exact hfold.mono _ _ (Nat.le_refl _)
          hs0c (Nat.le_refl _)
      have hstep : ∃ (F1 : Slot → Block V) (End1 : Block V),
          MovingSlotFoldAtN S rho
            (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2)) M0
            (S.hc.opening_slot q + 3) (c + 2) F1 End1 ∧
          ∀ d : Slot, d ≤ c + 1 → F1 d = F d := by
        rcases lt_trichotomy (c + 2)
            (S.hc.opening_slot (q + 2)) with
          hbefore | heq | hafter
        · have hbaseLower : S.hc.opening_slot q + 2 ≤ c := by
            apply Nat.le_of_succ_le_succ
            show (S.hc.opening_slot q + 2) + 1 ≤ c + 1
            exact hsBase
          have hbefore' : c + 1 < S.hc.opening_slot (q + 2) := by
            exact Nat.lt_of_lt_of_le (Nat.lt_succ_self (c + 1))
              (Nat.le_of_lt hbefore)
          have hdata := ceilingWindowData (M0 := M0) S hR0pos hpostBase
            hcarrierBase hcarrierQ hDPrev hbaseLower hbefore' hhorC
          have hdata' := ceilingWindowData (M0 := M0) S hR0pos hpostBase
            hcarrierBase hcarrierQ hDPrev
            (hbaseLower.trans (Nat.le_succ c)) hbefore hhorNext
          have htiming := ceilingActionTiming S hpostQ hcarrierQ hDPrev
            hbaseLower hbefore' hhorC
          exact w4MovingSlotFoldAtN_step_of_ceiling_named S adm hcom hfb
            hrec hdelay hpost hfold hdata htiming hdata' hv
            (hdeadline hsBase)
        · have hbaseLower : S.hc.opening_slot q + 2 ≤ c := by
            apply Nat.le_of_succ_le_succ
            show (S.hc.opening_slot q + 2) + 1 ≤ c + 1
            exact hsBase
          have hbefore' : c + 1 < S.hc.opening_slot (q + 2) := by
            rw [← heq]
            exact Nat.lt_succ_self (c + 1)
          have hdata := ceilingWindowData (M0 := M0) S hR0pos hpostBase
            hcarrierBase hcarrierQ hDPrev hbaseLower hbefore' hhorC
          have htake : S.hc.opening_slot (q + 2) ≤ c + 2 := by
            rw [heq]
          have hdata' := ordinaryWindowData (M0 := M0) S hR0pos hpostBase
            htake hhorNext
          have htiming := ceilingActionTiming S hpostQ hcarrierQ hDPrev
            hbaseLower hbefore' hhorC
          exact w4MovingSlotFoldAtN_step_of_mixed_named S adm hcom hfb
            hrec hdelay hpost hfold hdata htiming hdata' hv
            (hdeadline hsBase)
            ((w4nfi_vote_time_succ_le_confirmation_time S.E (c + 1)).trans
              hhorNext)
        · have htake : S.hc.opening_slot (q + 2) ≤ c + 1 :=
            Nat.le_of_lt_succ hafter
          have hdata := ordinaryWindowData (M0 := M0) S hR0pos hpostBase
            htake hhorC
          have hdata' := ordinaryWindowData (M0 := M0) S hR0pos hpostBase
            (htake.trans (Nat.le_succ _)) hhorNext
          have htiming := ordinaryActionTiming S hpostQ1 htake hhorC
          have hsupply : MovingSlotStepSupply S rho
              (Protocol.support_cutoff S.E (S.hc.opening_slot q + 2)) M0 c :=
            ⟨hdata, htiming, hdata'⟩
          obtain ⟨F1, End1, hfold1, hbase1⟩ :=
            MovingSlotFoldAtN.iterate_withBase S adm hcom hfb hrec hdelay
              hpost (t1 := Protocol.support_cutoff S.E
                (S.hc.opening_slot q + 2)) (M0 := M0) (s0 :=
                S.hc.opening_slot q + 3) (v := v) hv
              1 c F End hfold
              (fun j hj hjlt => by
                have hjc : j = c := Nat.le_antisymm
                  (Nat.le_of_lt_succ hjlt) hj
                subst hjc
                exact hsupply)
              (fun j F2 End2 hj hjlt hf => by
                have hjc : j = c := Nat.le_antisymm
                  (Nat.le_of_lt_succ hjlt) hj
                subst hjc
                exact w4MovingSlotCeilingSupplyAt_of_ordinaryFoldStep
                  S adm hf hsupply)
              (hdeadline hsBase)
              (fun j hj hjlt => by
                have hjc : j = c := Nat.le_antisymm
                  (Nat.le_of_lt_succ hjlt) hj
                subst hjc
                exact (w4nfi_vote_time_succ_le_confirmation_time
                  S.E (j + 1)).trans hhorNext)
          exact ⟨F1, End1, hfold1, hbase1⟩
      obtain ⟨F1, End1, hfold1, hkeep⟩ := hstep
      have hbaseEq1 : F1 (S.hc.opening_slot q + 3) = D.erase := by
        exact (hkeep _ hs0c).trans hbaseEq
      obtain ⟨F', End', hfold', hbaseEq'⟩ := ih (c := c + 1)
        (F := F1) (End := End1) hfold1
        (hsBase := hsBase.trans (Nat.le_succ (c + 1))) hbaseEq1
        (by simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hhor)
      refine ⟨F', End', ?_, hbaseEq'⟩
      have hshift : c + 1 + 1 + n = c + 1 + (n + 1) := by
        calc
          c + 1 + 1 + n = c + 1 + (1 + n) := Nat.add_assoc _ _ _
          _ = c + 1 + (n + 1) := by rw [Nat.add_comm 1 n]
      rw [hshift] at hfold'
      exact hfold'

#print axioms w4MovingSlotFoldAtN_iterate_hybrid_named

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
