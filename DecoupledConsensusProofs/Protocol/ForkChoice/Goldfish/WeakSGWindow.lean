module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusInternal.Execution.AwakeWindow
public import DecoupledConsensusProofs.Protocol.Handlers.SGArrival
public import DecoupledConsensusProofs.Protocol.Store.WeakSGRepresentationNamed
public import DecoupledConsensusProofs.Protocol.Schedule.Action
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.RecoveryRelativeMajorityProvenance
public import DecoupledConsensusProofs.Protocol.Handlers.BlockAdmission
public import DecoupledConsensusProofs.Protocol.Schedule.PostHealingBoundaryCanonicality

@[expose] public section

/-!
# Awake-window representation at a reader

An eligible awake validator emits at some action in the expiry window.
Core admissibility and the action's relay deadline place that vote in
the reader's pool. The window majority then gives the local relative
majority used by SG fork choice. No grade or full participation is used.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface
namespace WeakSG

open Internal Execution

variable {V : Type} [DecidableEq V] [Fintype V]



omit [DecidableEq V] [Fintype V] in
/-- Window membership retains the exact awake source round. -/
theorem mem_honestAwakeWindow_iff
    {awake : V → Round → Bool} {Hon : Finset V} {etaSG r : Round} {v : V} :
    v ∈ honestAwakeWindow awake Hon etaSG r ↔
      v ∈ Hon ∧ ∃ k ∈ Protocol.latest_window etaSG r, awake v k = true := by
  simp only [honestAwakeWindow, Finset.mem_filter, List.any_eq_true]

omit [DecidableEq V] [Fintype V] in
/-- Every validator counted in the awake window is honest. -/
theorem honestAwakeWindow_subset
    (awake : V → Round → Bool) (Hon : Finset V) (etaSG r : Round) :
    honestAwakeWindow awake Hon etaSG r ⊆ Hon :=
  Finset.filter_subset _ _

/-- The awake-window bound implies an honest majority of total weight. -/
theorem honestWeightMajority_of_awakeWindowMajority
    (S : Setup V) {Hon : Finset V} {r : Round}
    (hwindow : AwakeWindowMajority S.E (fun v => (S.node v).awake)
      Hon S.hc.η_SG r) : HonestWeightMajority S Hon :=
  lt_of_lt_of_le hwindow (S.E.electorate.weightOf_mono
    (honestAwakeWindow_subset _ _ _ _))


/-- If each eligible source action is post-GST and its relay deadline
precedes the read, every honest awake validator is represented there. -/
theorem honestAwakeWindow_subset_represented_stateBeforeTime
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {w : V} (hw : w ∈ rho.honest) {r : Round} {t : Time}
    (hpost : ∀ k ∈ Protocol.latest_window S.hc.η_SG r, S.E.t_GST ≤ S.a k)
    (hread : ∀ k ∈ Protocol.latest_window S.hc.η_SG r,
      S.a k + S.E.Δ ≤ t)
    (hhor : t ≤ rho.horizon) :
    honestAwakeWindow (fun v => (S.node v).awake) rho.honest S.hc.η_SG r ⊆
      Protocol.represented_set
        (rho.stateBeforeTime S t w).st.core.toHealing.sg_votes S.hc.η_SG r := by
  intro v hv
  obtain ⟨hvHon, k, hk, hA⟩ := mem_honestAwakeWindow_iff.mp hv
  have hu := awake_sgVote_mem_stateBeforeTime S adm hvHon hw hA
    (hpost k hk) (hread k hk) hhor
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ v, ?_⟩
  apply Protocol.represented_of_vote_mem hk hu
  exact (actionAttestationAt_shape S rho v k).1

/-- The same producer gives the relative-majority inequality used by
the SG anchor walk. There is no absolute-grade premise. -/
theorem sgWindowMajority_stateBeforeTime
    (S : Setup V) {rho : Run V} (adm : AdmissibleCore S rho)
    {w : V} (hw : w ∈ rho.honest) {r : Round} {t : Time}
    {pre : Protocol.Store V}
    (hpre : (rho.stateBeforeTime S t w).st.core = pre)
    (hwindow : AwakeWindowMajority S.E (fun v => (S.node v).awake)
      rho.honest S.hc.η_SG r)
    (hpost : ∀ k ∈ Protocol.latest_window S.hc.η_SG r, S.E.t_GST ≤ S.a k)
    (hread : ∀ k ∈ Protocol.latest_window S.hc.η_SG r,
      S.a k + S.E.Δ ≤ t)
    (hhor : t ≤ rho.horizon) :
    2 * S.E.electorate.weightOf
        (Protocol.represented_set
          pre.toHealing.sg_votes S.hc.η_SG r \ rho.honest) <
      Protocol.W_r S.E pre.toHealing.sg_votes S.hc.η_SG r := by
  have hrepresented := honestAwakeWindow_subset_represented_stateBeforeTime
    S adm hw hpost hread hhor
  rw [hpre] at hrepresented
  exact sgWindowMajority_of_representedHonestSubset S.E
    (honestAwakeWindow_subset _ _ _ _)
    hrepresented
    hwindow

/-- Every eligible source round is at or after the window's left end. -/
theorem mem_latestWindow_lower_bound {etaSG r k : Round}
    (hk : k ∈ Protocol.latest_window etaSG r) : r - etaSG ≤ k := by
  simp only [Protocol.latest_window, List.mem_range'] at hk
  obtain ⟨n, _, hkn⟩ := hk
  simp only [one_mul] at hkn
  rw [hkn]
  exact Nat.le_add_right _ _




/-- Every eligible source action has relayed before any vote duty in
the read round, including its opening slot. -/
theorem window_deadline_le_vote (S : Setup V) {s : Slot} {k : Round}
    (hk : k ∈ Protocol.latest_window S.hc.η_SG (S.hc.round_of s)) :
    S.a k + S.E.Δ ≤ Protocol.vote_time S.E s := by
  have hkr := mem_latestWindow_lt hk
  have hopen : S.hc.opening_slot (S.hc.round_of s) ≤ s :=
    Nat.div_mul_le_self s S.hc.R
  have htime : Protocol.proposal_time S.E s ≤ Protocol.vote_time S.E s := by
    change S.E.t s ≤ S.E.t s + S.E.Δ
    exact le_add_of_nonneg_right (le_of_lt S.E.Δ_pos)
  exact le_trans (Proofs.HealingLemmas.action_add_delta_le_openingProposal_of_round_lt S hkr)
    (le_trans (Protocol.proposal_time_mono S.E hopen) htime)




end WeakSG
end HealingSurface
end Proofs
end DecoupledConsensusModel

end
