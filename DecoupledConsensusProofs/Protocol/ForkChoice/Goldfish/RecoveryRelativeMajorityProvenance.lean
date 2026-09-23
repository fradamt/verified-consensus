module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.RecoveryFreshGradeProvenance
public import DecoupledConsensusProofs.Protocol.Store.HonestPoolActionBridge
public import DecoupledConsensusProofs.Objects.PostGSTSync
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.HonestMajorityCore

@[expose] public section

/-!
# Honest provenance of a relative-majority recovery anchor

The final Section 7 SG root uses the relative-majority walk only when no fresh
grade-1 anchor exists. If that walk moves past its FG-root anchor, its result
has a strict majority of the represented weight. Once all honest validators
are represented, below-one-third faults force one of those supporters to be
honest.

This file first records that pure counting fact. The run-level section then
connects the selected latest support vote to an earlier honest Section 7
action.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Pure relative-majority provenance -/

/-- A represented honest subset that outweighs all faulty validators gives
the local relative-majority bound. Other honest validators may be absent. -/
theorem sgWindowMajority_of_representedHonestSubset
    (E : Env V) {pool : Round → Finset (Protocol.SGVote V)}
    {etaSG r : Round} {Hon Awake : Finset V}
    (hHon : Awake ⊆ Hon)
    (hrepresented : Awake ⊆ Protocol.represented_set pool etaSG r)
    (hweight : E.electorate.weightOf (Finset.univ \ Hon) <
      E.electorate.weightOf Awake) :
    2 * E.electorate.weightOf (Protocol.represented_set pool etaSG r \ Hon) <
      Protocol.W_r E pool etaSG r := by
  let R := Protocol.represented_set pool etaSG r
  have hfaults : E.electorate.weightOf (R \ Hon) ≤
      E.electorate.weightOf (Finset.univ \ Hon) := by
    apply E.electorate.weightOf_mono
    intro v hv
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, (Finset.mem_sdiff.mp hv).2⟩
  have hdisjoint : Disjoint Awake (R \ Hon) := by
    apply Finset.disjoint_left.mpr
    intro v hvA hvF
    exact (Finset.mem_sdiff.mp hvF).2 (hHon hvA)
  have hsum : E.electorate.weightOf Awake + E.electorate.weightOf (R \ Hon) ≤
      E.electorate.weightOf R := by
    calc
      _ = E.electorate.weightOf (Awake ∪ (R \ Hon)) :=
        (Finset.sum_union hdisjoint).symm
      _ ≤ _ := E.electorate.weightOf_mono (by
        intro v hv
        rcases Finset.mem_union.mp hv with hv | hv
        · exact hrepresented hv
        · exact (Finset.mem_sdiff.mp hv).1)
  change 2 * E.electorate.weightOf (R \ Hon) < E.electorate.weightOf R
  omega

/-- A moved relative-majority anchor has an honest latest supporter under
only the reader's window-majority bound. No absolute grade or full honest
representation is required. -/
theorem majorityForkChoice_eq_anchor_or_honestLatestSupport_of_windowMajority
    (E : Env V) {pool : Round → Finset (Protocol.SGVote V)}
    {etaSG : Round} {T : Finset (Block V)} {Hon : Finset V} {r : Round}
    {anchor : Block V} {tree : Finset (Block V)}
    (hwindow :
      2 * E.electorate.weightOf (Protocol.represented_set pool etaSG r \ Hon) <
        Protocol.W_r E pool etaSG r) :
    let A := Protocol.majority_fork_choice E pool etaSG T anchor tree r
    A = anchor ∨
      ∃ v ∈ Hon, ∃ u : Protocol.SGVote V,
        Protocol.latest_support_vote pool etaSG T v r = some u ∧
          Protocol.heads_under T A u = true := by
  intro A
  rcases Protocol.ghost_eligible anchor tree
      (Protocol.sg_support E pool etaSG T r)
      (fun B => decide (Protocol.W_r E pool etaSG r <
        2 * Protocol.sg_support E pool etaSG T r B)) with heq | helig
  · exact Or.inl heq
  · have hmajority : Protocol.W_r E pool etaSG r <
        2 * Protocol.sg_support E pool etaSG T r A := by
      simpa only [decide_eq_true_eq] using helig
    have hex : ∃ v ∈ Hon, v ∈ Protocol.sgSupporters pool etaSG T r A := by
      by_contra hnone
      push Not at hnone
      have hsub : Protocol.sgSupporters pool etaSG T r A ⊆
          Protocol.represented_set pool etaSG r \ Hon := by
        intro v hv
        refine Finset.mem_sdiff.mpr ⟨?_, fun hvHon => hnone v hvHon hv⟩
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ v,
          Protocol.HonestWeightMajority.represented_of_supports
            (Finset.mem_filter.mp hv).2⟩
      have hbound := E.electorate.weightOf_mono hsub
      unfold Protocol.sg_support at hmajority
      omega
    obtain ⟨v, hvHon, hvSupport⟩ := hex
    have hsupports := (Finset.mem_filter.mp hvSupport).2
    simp only [Protocol.supports] at hsupports
    split at hsupports
    · exact absurd hsupports (by simp)
    · rename_i u hu
      exact Or.inr ⟨v, hvHon, u, hu, hsupports⟩

/-- If a relative-majority walk moves past its anchor while every honest
validator is represented, its result is supported by one honest validator's
selected latest vote.

The conclusion keeps the exact selector equation and resolved-head predicate.
These are the inputs needed to recover the vote's pool round and named block.
-/
theorem majorityForkChoice_eq_anchor_or_honestLatestSupport
    (E : Env V) {pool : Round → Finset (Protocol.SGVote V)}
    {etaSG : Round} {T : Finset (Block V)} {Hon : Finset V} {r : Round}
    {anchor : Block V} {tree : Finset (Block V)}
    (hfb : 3 * E.electorate.weightOf (Finset.univ \ Hon) < E.W)
    (hrepresented : ∀ v ∈ Hon,
      Protocol.represented pool etaSG v r = true) :
    let A := Protocol.majority_fork_choice E pool etaSG T anchor tree r
    A = anchor ∨
      ∃ v ∈ Hon, ∃ u : Protocol.SGVote V,
        Protocol.latest_support_vote pool etaSG T v r = some u ∧
          Protocol.heads_under T A u = true := by
  intro A
  have hwalk : A = Protocol.ghost anchor tree
      (Protocol.sg_support E pool etaSG T r)
      (fun B => decide (Protocol.W_r E pool etaSG r <
        2 * Protocol.sg_support E pool etaSG T r B)) := rfl
  rcases Protocol.ghost_eligible anchor tree
      (Protocol.sg_support E pool etaSG T r)
      (fun B => decide (Protocol.W_r E pool etaSG r <
        2 * Protocol.sg_support E pool etaSG T r B)) with heq | helig
  · exact Or.inl (by rw [hwalk, heq])
  · right
    have hmajority : Protocol.W_r E pool etaSG r <
        2 * Protocol.sg_support E pool etaSG T r A := by
      rw [hwalk]
      simpa only [decide_eq_true_eq] using helig
    have hex : ∃ v ∈ Hon,
        v ∈ Protocol.sgSupporters pool etaSG T r A := by
      by_contra hnone
      push Not at hnone
      have hsupportSub : Protocol.sgSupporters pool etaSG T r A ⊆
          Finset.univ \ Hon := by
        intro v hv
        refine Finset.mem_sdiff.mpr ⟨Finset.mem_univ v, ?_⟩
        intro hvHon
        exact hnone v hvHon hv
      have hsupportLe := E.electorate.weightOf_mono hsupportSub
      have hhonestSub : Hon ⊆ Protocol.represented_set pool etaSG r := by
        intro v hv
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ v,
          hrepresented v hv⟩
      have hhonestLe := E.electorate.weightOf_mono hhonestSub
      have hsum := E.electorate.weightOf_add_weightOf_sdiff Hon
      unfold Protocol.sg_support Protocol.W_r at hmajority
      unfold Env.W at hfb
      omega
    obtain ⟨v, hvHon, hvSupport⟩ := hex
    have hsupports : Protocol.supports pool etaSG T r A v = true :=
      (Finset.mem_filter.mp hvSupport).2
    simp only [Protocol.supports] at hsupports
    split at hsupports
    · exact absurd hsupports (by simp)
    · rename_i u hu
      exact ⟨v, hvHon, u, hu, hsupports⟩

omit [Fintype V] in
/-- A selected latest support vote retains its exact pool round, window
membership, and author. -/
theorem latestSupportVote_mem_window_and_author
    {pool : Round → Finset (Protocol.SGVote V)} {etaSG : Round}
    {T : Finset (Block V)} {v : V} {r : Round}
    {u : Protocol.SGVote V}
    (h : Protocol.latest_support_vote pool etaSG T v r = some u) :
    ∃ k : Round,
      k ∈ Protocol.latest_window etaSG r ∧
        u ∈ pool k ∧ u.val_index = v := by
  unfold Protocol.latest_support_vote at h
  split at h
  · exact absurd h (by simp)
  · rename_i k hk
    have hkmem : k ∈ Protocol.latest_window etaSG r := by
      unfold Protocol.latest_support_round at hk
      rw [List.getLast?_eq_some_iff] at hk
      obtain ⟨xs, hxs⟩ := hk
      have hkfilter : k ∈ (Protocol.latest_window etaSG r).filter
          (fun round => Protocol.holds_resolved_vote_by T
            (pool round) v) := by
        rw [hxs]
        simp
      exact (List.mem_filter.mp hkfilter).1
    obtain ⟨humem, huval⟩ := Protocol.sole_vote_mem_and_author h
    exact ⟨k, hkmem, humem, huval⟩

omit [DecidableEq V] [Fintype V] in
/-- Every round in the half-open relative-SG window is strictly earlier than
the read round. -/
theorem mem_latestWindow_lt {etaSG k r : Round}
    (hk : k ∈ Protocol.latest_window etaSG r) : k < r := by
  simp only [Protocol.latest_window, List.mem_range'] at hk
  obtain ⟨n, hn, hkn⟩ := hk
  simp only [one_mul] at hkn
  subst k
  by_cases heta : etaSG ≤ r
  · rw [min_eq_right heta] at hn
    calc
      r - etaSG + n < r - etaSG + etaSG :=
        Nat.add_lt_add_left hn (r - etaSG)
      _ = r := Nat.sub_add_cancel heta
  · have hrle : r ≤ etaSG := Nat.le_of_not_ge heta
    rw [min_eq_left hrle] at hn
    have hsub : r - etaSG = 0 := Nat.sub_eq_zero_of_le hrle
    simpa only [hsub, zero_add] using hn

/-- Window-majority provenance retains the exact support round and resolved
head. This form also permits an expiry-based safety handover. -/
theorem majorityForkChoice_eq_anchor_or_honestLatestHead_of_windowMajority
    (E : Env V) {pool : Round → Finset (Protocol.SGVote V)}
    {etaSG : Round} {T : Finset (Block V)} {Hon : Finset V} {r : Round}
    {anchor : Block V} {tree : Finset (Block V)}
    (hwindow :
      2 * E.electorate.weightOf (Protocol.represented_set pool etaSG r \ Hon) <
        Protocol.W_r E pool etaSG r) :
    let A := Protocol.majority_fork_choice E pool etaSG T anchor tree r
    A = anchor ∨
      ∃ v ∈ Hon, ∃ k ∈ Protocol.latest_window etaSG r,
        ∃ u : Protocol.SGVote V, u ∈ pool k ∧ u.val_index = v ∧
          ∃ head : Block V, u.confirmed = some head.root ∧
            Block.find? T head.root = some head ∧ head ∈ T ∧ Block.Preceq A head := by
  intro A
  rcases majorityForkChoice_eq_anchor_or_honestLatestSupport_of_windowMajority E
      (T := T) (anchor := anchor) (tree := tree) hwindow with
      hroot | ⟨v, hv, u, hlatest, hheads⟩
  · exact Or.inl hroot
  · obtain ⟨k, hkwindow, hu, huval⟩ :=
      latestSupportVote_mem_window_and_author hlatest
    rw [Proofs.Optimistic.heads_under_eq_head_covers] at hheads
    obtain ⟨root, head, huRoot, hfind, hmem, hAhead⟩ :=
      Proofs.HealingLemmas.exists_head_of_head_covers hheads
    have hheadRoot : head.root = root := Proofs.HealingLemmas.find?_root hfind
    refine Or.inr ⟨v, hv, k, hkwindow, u, hu, huval, head, ?_, ?_, hmem, hAhead⟩
    · rw [hheadRoot]
      exact huRoot
    · rw [hheadRoot]
      exact hfind

/-- Once the previous SG rounds have expired, a canonical suffix history bounds
the relative-majority anchor. Only the local window majority is required;
the theorem has no grade, full-participation, or one-third premise. -/
theorem majorityForkChoice_preceq_of_expiredCanonicalHistory
    (E : Env V) {pool : Round → Finset (Protocol.SGVote V)}
    {etaSG : Round} {T : Finset (Block V)} {Hon : Finset V} {base r : Round}
    {anchor Can : Block V} {tree : Finset (Block V)}
    (hgap : base + etaSG ≤ r)
    (hwindow :
      2 * E.electorate.weightOf (Protocol.represented_set pool etaSG r \ Hon) <
        Protocol.W_r E pool etaSG r)
    (hanchor : Block.Preceq anchor Can)
    (hhistory : ∀ k, base ≤ k → k < r → ∀ u ∈ pool k,
      u.val_index ∈ Hon → ∀ head : Block V,
        u.confirmed = some head.root → Block.find? T head.root = some head →
          Block.Preceq head Can) :
    Block.Preceq (Protocol.majority_fork_choice E pool etaSG T anchor tree r) Can := by
  rcases majorityForkChoice_eq_anchor_or_honestLatestHead_of_windowMajority E
      (T := T) (anchor := anchor) (tree := tree) hwindow with
      hroot | ⟨v, hv, k, hk, u, hu, huval, head, huRoot, hfind, _, hpre⟩
  · simpa only [hroot] using hanchor
  · have hklo : base ≤ k := by
      have hstart : base ≤ r - etaSG := Nat.le_sub_of_add_le hgap
      simp only [Protocol.latest_window, List.mem_range'] at hk
      obtain ⟨n, _, hkn⟩ := hk
      simp only [one_mul] at hkn
      subst k
      exact hstart.trans (Nat.le_add_right _ _)
    have huHon : u.val_index ∈ Hon := huval ▸ hv
    exact Block.preceq_trans hpre
      (hhistory k hklo (mem_latestWindow_lt hk) u hu huHon head huRoot hfind)

/-- Block-level form of honest relative-majority provenance. If the walk
moves, its output lies below the resolved head of an honest selected vote from
one strictly earlier round in the live SG window. -/
theorem majorityForkChoice_eq_anchor_or_honestLatestHead
    (E : Env V) {pool : Round → Finset (Protocol.SGVote V)}
    {etaSG : Round} {T : Finset (Block V)} {Hon : Finset V} {r : Round}
    {anchor : Block V} {tree : Finset (Block V)}
    (hfb : 3 * E.electorate.weightOf (Finset.univ \ Hon) < E.W)
    (hrepresented : ∀ v ∈ Hon,
      Protocol.represented pool etaSG v r = true) :
    let A := Protocol.majority_fork_choice E pool etaSG T anchor tree r
    A = anchor ∨
      ∃ v ∈ Hon, ∃ k < r, ∃ u : Protocol.SGVote V,
        u ∈ pool k ∧ u.val_index = v ∧
          ∃ head : Block V,
            u.confirmed = some head.root ∧
              Block.find? T head.root = some head ∧
              head ∈ T ∧ Block.Preceq A head := by
  intro A
  rcases majorityForkChoice_eq_anchor_or_honestLatestSupport
      E hfb hrepresented with hroot | ⟨v, hv, u, hlatest, hheads⟩
  · exact Or.inl hroot
  · right
    obtain ⟨k, hkwindow, hu, huval⟩ :=
      latestSupportVote_mem_window_and_author hlatest
    rw [Proofs.Optimistic.heads_under_eq_head_covers] at hheads
    obtain ⟨root, head, huRoot, hfind, hmem, hAhead⟩ :=
      Proofs.HealingLemmas.exists_head_of_head_covers hheads
    have hheadRoot : head.root = root := Proofs.HealingLemmas.find?_root hfind
    refine ⟨v, hv, k, mem_latestWindow_lt hkwindow, u, hu, huval,
      head, ?_, ?_, hmem, hAhead⟩
    · rw [hheadRoot]
      exact huRoot
    · rw [hheadRoot]
      exact hfind

/-! ## Run-level relative-anchor provenance -/

/-- At an honest action store, the relative-majority fallback either stays at
the store's FG root or lies below an honest exact SG carrier from a strictly
earlier round.

The full-representation premise is the normal post-GST delivery fact. The
selected vote itself needs no timing premise: pool provenance and authenticity
identify it with its author's scheduled Section 7 action. -/
theorem actionRelativeAnchor_eq_fgRoot_or_preceq_honestEarlierCarrier
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hfb : BelowOneThird S rho.honest)
    {w : V} (hw : w ∈ rho.honest) (r : Round)
    (hrepresented : ∀ v ∈ rho.honest,
      Protocol.represented
        (actionStoreAt S rho w r).toHealing.sg_votes
        S.hc.η_SG v r = true) :
    let ast := actionStoreAt S rho w r
    let root := Protocol.get_fg_root ast.toHealing.toFG
    let A := Protocol.majority_fork_choice S.E
      ast.toHealing.sg_votes S.hc.η_SG ast.T root
      (Protocol.get_filtered_block_tree ast.toHealing.toFG) r
    A = root ∨
      ∃ v ∈ rho.honest, ∃ k < r,
        Block.Preceq A (actionSGBlockAt S rho v k) := by
  intro ast root A
  have hpure := majorityForkChoice_eq_anchor_or_honestLatestHead
    S.E (pool := ast.toHealing.sg_votes) (etaSG := S.hc.η_SG)
      (T := ast.T) (Hon := rho.honest) (r := r) (anchor := root)
      (tree := Protocol.get_filtered_block_tree ast.toHealing.toFG)
      hfb hrepresented
  change A = root ∨
    ∃ v ∈ rho.honest, ∃ k < r, ∃ u : Protocol.SGVote V,
      u ∈ ast.toHealing.sg_votes k ∧ u.val_index = v ∧
        ∃ head : Block V,
          u.confirmed = some head.root ∧
            Block.find? ast.T head.root = some head ∧
            head ∈ ast.T ∧ Block.Preceq A head at hpure
  rcases hpure with hroot | ⟨v, hv, k, hkr, u, hu, huval,
      head, huHead, -, hheadMem, hAhead⟩
  · exact Or.inl hroot
  · right
    have huEq : u = actionSGVoteAt S rho v k :=
      honestSGVote_eq_actionSGVoteAt_of_mem_actionStore
        S adm hv (w := w) (r := r) hu huval
    let C := actionSGBlockAt S rho v k
    have hheadRoot : head.root = C.root := by
      have hconfirmed : (actionSGVoteAt S rho v k).confirmed =
          some head.root := by
        simpa only [huEq] using huHead
      simpa only [actionSGVoteAt, C, Option.some.injEq] using hconfirmed.symm
    have hheadMem' : head ∈ (rho.storeBeforeTime S w (S.a r)).T := by
      simpa only [ast, actionStoreAt, Run.storeBeforeTime,
        NamedActionReads.actionReadAt, NamedActionReads.actionReadFrom,
        NamedActionReads.confirmationReadFrom, NamedActionReads.preparedCache] using hheadMem
    obtain ⟨headNamed, hheadNamed, hheadRun⟩ :=
      Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
        adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hw (S.a r) hheadMem'
    have hCmem : C ∈ (rho.storeBeforeTime S v (S.a k)).T := by
      simpa only [C] using actionSGBlockAt_mem_storeBeforeTime S rho v k
    obtain ⟨CNamed, hCNamed, hCRun⟩ :=
      Proofs.NamedStoreBridge.runBlock_of_mem_core_T_stateBeforeTime S
        adm.toNamedAdmissibleCore.toNamedScheduleWellFormed hv (S.a k) hCmem
    have hheadRootNamed : headNamed.root = CNamed.root := by
      rw [← Proofs.NamedWire.erase_root headNamed, ← Proofs.NamedWire.erase_root CNamed,
        hheadNamed, hCNamed]
      exact hheadRoot
    have hheadEqNamed : headNamed = CNamed :=
      adm.toNamedAdmissibleCore.toNamedRootCollisionFree.root_injective
        headNamed CNamed hheadRun hCRun headNamed CNamed
        (Or.inl (Proofs.NamedAncestry.named_self headNamed))
        (Or.inr (Proofs.NamedAncestry.named_self CNamed)) hheadRootNamed
    have hheadEq : head = C := by
      calc
        head = headNamed.erase := hheadNamed.symm
        _ = CNamed.erase := congrArg NamedBlock.erase hheadEqNamed
        _ = C := hCNamed
    exact ⟨v, hv, k, hkr, by simpa only [C, hheadEq] using hAhead⟩

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
