module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.ProposalSnapshotBridge
public import DecoupledConsensusProofs.Protocol.ForkChoice.Goldfish.FrontierParent

@[expose] public section

/-!
# Pure proposer-to-voter GHOST transport

This module isolates the order-theoretic part of honest-proposal walk
transport. The source and target may use different trees, anchors, scores,
and eligibility predicates. The target walk follows the source result when:

* the target anchor is a descendant of the source anchor on the source-result
  chain;
* the source-selected child at each remaining path position is still an
  eligible target candidate;
* every eligible target child at those positions reflects to an eligible
  source child; and
* source and target scores agree on common candidates.

These are proof interfaces only. They add no protocol state or execution
assumption.

The pivot form below does not assume that the source and target anchors are
temporally monotone. Both walks can start below a common pivot. An explicit
target-prefix premise drives the target to that pivot, after which the source
walk supplies the remaining choices.
-/

namespace DecoupledConsensusModel
namespace Protocol

open Internal
open DecoupledConsensusModel.Execution

variable {V : Type} [DecidableEq V] [Fintype V]

omit [Fintype V] in
/-- Restricting an `argmax?` to reflected candidates preserves its selected
block when the selected block remains present and all retained scores agree.

Root injectivity is needed only for the target set. It rules out the raw
datatype's degenerate equal-score/equal-root tie. -/
theorem argmax?_transport_of_subset
    {sourceChildren targetChildren : Finset (Block V)}
    {sourceScore targetScore : Block V → Nat} {C : Block V}
    (hroot : RootInjectiveBelow targetChildren)
    (hsource : Protocol.argmax? sourceScore sourceChildren = some C)
    (hCtarget : C ∈ targetChildren)
    (hreflect : targetChildren ⊆ sourceChildren)
    (hscore : ∀ D ∈ targetChildren, targetScore D = sourceScore D) :
    Protocol.argmax? targetScore targetChildren = some C := by
  have hCsource : C ∈ sourceChildren := Proofs.Engine.pickUnique?_mem hsource
  have hCbestSource :
      Protocol.is_best_in sourceScore sourceChildren C = true := by
    unfold Protocol.argmax? pickUnique? at hsource
    split at hsource
    next hex =>
      have hspec := Finset.choose_spec
        (fun B => Protocol.is_best_in sourceScore sourceChildren B = true)
        sourceChildren hex
      have heq : sourceChildren.choose
          (fun B => Protocol.is_best_in sourceScore sourceChildren B = true)
          hex = C := Option.some.inj hsource
      rw [heq] at hspec
      exact hspec.2
    next => contradiction
  have hCbestTarget :
      Protocol.is_best_in targetScore targetChildren C = true := by
    simp only [Protocol.is_best_in, decide_eq_true_eq] at hCbestSource ⊢
    intro D hD
    have hbest := hCbestSource D (hreflect hD)
    simpa only [Protocol.outranks, hscore D hD, hscore C hCtarget] using hbest
  apply pickUnique?_eq_some hCtarget hCbestTarget
  intro D hD hDbest
  simp only [Protocol.is_best_in, decide_eq_true_eq] at hCbestTarget hDbest
  have hDC := hCbestTarget D hD
  have hCD := hDbest C hCtarget
  simp only [Protocol.outranks, Bool.or_eq_false_iff,
    Bool.and_eq_false_iff, decide_eq_false_iff_not] at hDC hCD
  have hscoreEq : targetScore D = targetScore C := by
    apply Nat.le_antisymm
    · exact le_of_not_gt hDC.1
    · exact le_of_not_gt hCD.1
  have hrootDLeC : D.root ≤ C.root := by
    by_cases heq : targetScore C = targetScore D
    · rcases hDC.2 with hne | hnot
      · exact False.elim (hne heq)
      · exact le_of_not_gt hnot
    · exact False.elim (heq hscoreEq.symm)
  have hrootCLeD : C.root ≤ D.root := by
    by_cases heq : targetScore D = targetScore C
    · rcases hCD.2 with hne | hnot
      · exact False.elim (hne heq)
      · exact le_of_not_gt hnot
    · exact False.elim (heq hscoreEq)
  have hrootEq : D.root = C.root := le_antisymm hrootDLeC hrootCLeD
  exact hroot D C
    ⟨D, hD, Block.preceq_self D⟩
    ⟨C, hCtarget, Block.preceq_self C⟩ hrootEq

omit [Fintype V] in
/-- Every strict block on the chain from a GHOST start to its result has the
source walk's next selected child below that result. -/
theorem ghost_walk_step_towards_result
    {tree : Finset (Block V)} {score : Block V → Nat}
    {eligible : Block V → Bool} :
    ∀ (n : Nat) (A H X : Block V),
      Protocol.ghost_walk tree score eligible n A = H →
      Block.Preceq A X → Block.Preceq X H → X ≠ H →
      ∃ C, Protocol.ghost_step tree score eligible X = some C ∧
        Block.Preceq C H := by
  intro n
  induction n with
  | zero =>
      intro A H X hwalk hAX hXH hne
      simp only [Protocol.ghost_walk] at hwalk
      subst H
      exact False.elim (hne (Block.preceq_antisymm hXH hAX))
  | succ n ih =>
      intro A H X hwalk hAX hXH hne
      cases hstep : Protocol.ghost_step tree score eligible A with
      | none =>
          simp only [Protocol.ghost_walk, hstep] at hwalk
          subst H
          exact False.elim (hne (Block.preceq_antisymm hXH hAX))
      | some C =>
          have hwalk' : Protocol.ghost_walk tree score eligible n C = H := by
            simpa only [Protocol.ghost_walk, hstep] using hwalk
          have hCdata := ghost_step_child hstep
          have hCH : Block.Preceq C H := by
            have hpre := ghost_walk_preceq tree score eligible n C
            rwa [hwalk'] at hpre
          by_cases hXA : X = A
          · subst X
            exact ⟨C, hstep, hCH⟩
          · have hCX : Block.Preceq C X := by
              rcases Block.preceq_linear hCH hXH with hCX | hXC
              · exact hCX
              · have hAdepth : A.depth < X.depth := by
                  have hle := Block.preceq_depth_le hAX
                  have hneDepth : A.depth ≠ X.depth := by
                    intro heq
                    exact hXA (Block.preceq_eq_of_depth_le hAX (by omega)).symm
                  omega
                have hCdepth : C.depth = A.depth + 1 :=
                  depth_of_parent? hCdata.2.1
                have hXdepth := Block.preceq_depth_le hXC
                have hEq : X = C := Block.preceq_eq_of_depth_le hXC (by omega)
                rw [hEq]
                exact Block.preceq_self C
            exact ih C H X hwalk' hCX hXH hne

omit [Fintype V] in
/-- One source GHOST result transfers to a target GHOST walk.

`hpersist` is the selected-candidate premise. `hreflect` is the explicit
extra-child premise: a target-only candidate cannot become eligible at a path
position. `hscore` is required only for blocks present in both trees. -/
theorem ghost_transport_of_source
    {sourceTree targetTree : Finset (Block V)}
    {sourceScore targetScore : Block V → Nat}
    {sourceEligible targetEligible : Block V → Bool}
    {sourceAnchor targetAnchor H : Block V}
    (hsourceRoot : RootInjectiveBelow sourceTree)
    (htargetRoot : RootInjectiveBelow targetTree)
    (hsource : Protocol.ghost sourceAnchor sourceTree sourceScore
      sourceEligible = H)
    (hanchors : Block.Preceq sourceAnchor targetAnchor ∧
      Block.Preceq targetAnchor H)
    (hpath : ∀ C : Block V,
      Block.Preceq targetAnchor C → C ≠ targetAnchor →
      Block.Preceq C H → C ∈ targetTree)
    (hpersist : ∀ X C : Block V,
      Block.Preceq targetAnchor X → Block.Preceq X H → X ≠ H →
      Protocol.ghost_step sourceTree sourceScore sourceEligible X = some C →
      Block.Preceq C H →
      C ∈ targetTree ∧ targetEligible C = true)
    (hreflect : ∀ X C : Block V,
      Block.Preceq targetAnchor X → Block.Preceq X H →
      C ∈ targetTree → C.parent? = some X → targetEligible C = true →
      C ∈ sourceTree ∧ sourceEligible C = true)
    (hscore : ∀ C, C ∈ sourceTree → C ∈ targetTree →
      targetScore C = sourceScore C) :
    (∀ C ∈ targetTree, C.parent? = some H → targetEligible C = false) ∧
      Protocol.ghost targetAnchor targetTree targetScore targetEligible = H := by
  have hsourceSteps : ∀ X : Block V,
      Block.Preceq targetAnchor X → Block.Preceq X H → X ≠ H →
      ∃ C, Protocol.ghost_step sourceTree sourceScore sourceEligible X = some C ∧
        Block.Preceq C H := by
    intro X hAX hXH hne
    apply ghost_walk_step_towards_result sourceTree.card sourceAnchor H X
    · simpa only [Protocol.ghost] using hsource
    · exact Block.preceq_trans hanchors.1 hAX
    · exact hXH
    · exact hne
  have htargetStep : ∀ X : Block V,
      Block.Preceq targetAnchor X → Block.Preceq X H → X ≠ H →
      ∃ C, Protocol.ghost_step targetTree targetScore targetEligible X = some C ∧
        Block.Preceq C H := by
    intro X hAX hXH hne
    obtain ⟨C, hsourceStep, hCH⟩ := hsourceSteps X hAX hXH hne
    have hkeep := hpersist X C hAX hXH hne hsourceStep hCH
    have hsourceChild := ghost_step_child hsourceStep
    refine ⟨C, ?_, hCH⟩
    rw [Protocol.ghost_step] at hsourceStep ⊢
    have htargetChildRoot : RootInjectiveBelow
        (Protocol.ghost_children targetTree targetEligible X) := by
      intro A D hA hD hroot
      apply htargetRoot A D
      · obtain ⟨Y, hY, hAY⟩ := hA
        exact ⟨Y, (Finset.mem_filter.mp hY).1, hAY⟩
      · obtain ⟨Y, hY, hDY⟩ := hD
        exact ⟨Y, (Finset.mem_filter.mp hY).1, hDY⟩
      · exact hroot
    apply argmax?_transport_of_subset htargetChildRoot hsourceStep
    · rw [Protocol.ghost_children, Finset.mem_filter]
      exact ⟨hkeep.1, hsourceChild.2.1, hkeep.2⟩
    · intro D hD
      rw [Protocol.ghost_children, Finset.mem_filter] at hD ⊢
      have href := hreflect X D hAX hXH hD.1 hD.2.1 hD.2.2
      exact ⟨href.1, hD.2.1, href.2⟩
    · intro D hD
      rw [Protocol.ghost_children, Finset.mem_filter] at hD
      have href := hreflect X D hAX hXH hD.1 hD.2.1 hD.2.2
      exact hscore D href.1 hD.1
  have hstopped : ∀ C ∈ targetTree,
      C.parent? = some H → targetEligible C = false := by
    intro C hC hparent
    cases helig : targetEligible C with
    | false => rfl
    | true =>
        have href := hreflect H C hanchors.2 (Block.preceq_self H)
          hC hparent helig
        have hfalse := Proofs.HealingSurface.eligible_child_false_at_ghost_result
          hsourceRoot href.1 (show C.parent? = some
            (Protocol.ghost sourceAnchor sourceTree sourceScore sourceEligible) by
              rw [hsource]
              exact hparent)
        rw [href.2] at hfalse
        contradiction
  refine ⟨hstopped, ?_⟩
  exact ghost_reaches hanchors.2 hpath
    (ghost_step_none hstopped) htargetStep

omit [Fintype V] in
/-- Transport through a common pivot without comparing the two anchors.

`hprefix` is the only extra premise: before the pivot, it gives the target
walk's next child towards the pivot. From the pivot through `H`, the source
walk, candidate persistence, eligible-child reflection, and common-candidate
score equality provide the target steps exactly as in
`ghost_transport_of_source`.

This form is suitable when a later fresh-anchor read can move behind an earlier
relative anchor. -/
theorem ghost_transport_via_pivot
    {sourceTree targetTree : Finset (Block V)}
    {sourceScore targetScore : Block V → Nat}
    {sourceEligible targetEligible : Block V → Bool}
    {sourceAnchor targetAnchor pivot H : Block V}
    (hsourceRoot : RootInjectiveBelow sourceTree)
    (htargetRoot : RootInjectiveBelow targetTree)
    (hsource : Protocol.ghost sourceAnchor sourceTree sourceScore
      sourceEligible = H)
    (hanchors : Block.Preceq sourceAnchor pivot ∧
      Block.Preceq targetAnchor pivot ∧ Block.Preceq pivot H)
    (hpath : ∀ C : Block V,
      Block.Preceq targetAnchor C → C ≠ targetAnchor →
      Block.Preceq C H → C ∈ targetTree)
    (hprefix : ∀ X : Block V,
      Block.Preceq targetAnchor X → Block.Preceq X pivot → X ≠ pivot →
      ∃ C, Protocol.ghost_step targetTree targetScore targetEligible X = some C ∧
        Block.Preceq C pivot)
    (hpersist : ∀ X C : Block V,
      Block.Preceq pivot X → Block.Preceq X H → X ≠ H →
      Protocol.ghost_step sourceTree sourceScore sourceEligible X = some C →
      Block.Preceq C H →
      C ∈ targetTree ∧ targetEligible C = true)
    (hreflect : ∀ X C : Block V,
      Block.Preceq pivot X → Block.Preceq X H →
      C ∈ targetTree → C.parent? = some X → targetEligible C = true →
      C ∈ sourceTree ∧ sourceEligible C = true)
    (hscore : ∀ C, C ∈ sourceTree → C ∈ targetTree →
      targetScore C = sourceScore C) :
    (∀ C ∈ targetTree, C.parent? = some H → targetEligible C = false) ∧
      Protocol.ghost targetAnchor targetTree targetScore targetEligible = H := by
  have hpathPivot : ∀ C : Block V,
      Block.Preceq pivot C → C ≠ pivot → Block.Preceq C H →
      C ∈ targetTree := by
    intro C hPC hne hCH
    apply hpath C (Block.preceq_trans hanchors.2.1 hPC) _ hCH
    intro hCt
    subst C
    exact hne (Block.preceq_antisymm hanchors.2.1 hPC)
  obtain ⟨hstopped, hsuffix⟩ := ghost_transport_of_source
    hsourceRoot htargetRoot hsource ⟨hanchors.1, hanchors.2.2⟩
      hpathPivot hpersist hreflect hscore
  have hsuffixStep : ∀ X : Block V,
      Block.Preceq pivot X → Block.Preceq X H → X ≠ H →
      ∃ C, Protocol.ghost_step targetTree targetScore targetEligible X = some C ∧
        Block.Preceq C H := by
    intro X hPX hXH hne
    apply ghost_walk_step_towards_result targetTree.card pivot H X
    · simpa only [Protocol.ghost] using hsuffix
    · exact hPX
    · exact hXH
    · exact hne
  have htargetStep : ∀ X : Block V,
      Block.Preceq targetAnchor X → Block.Preceq X H → X ≠ H →
      ∃ C, Protocol.ghost_step targetTree targetScore targetEligible X = some C ∧
        Block.Preceq C H := by
    intro X hAX hXH hne
    rcases Block.preceq_linear hXH hanchors.2.2 with hXP | hPX
    · by_cases hEq : X = pivot
      · subst X
        exact hsuffixStep pivot (Block.preceq_self pivot) hanchors.2.2 hne
      · obtain ⟨C, hstep, hCP⟩ := hprefix X hAX hXP hEq
        exact ⟨C, hstep, Block.preceq_trans hCP hanchors.2.2⟩
    · exact hsuffixStep X hPX hXH hne
  refine ⟨hstopped, ?_⟩
  exact ghost_reaches
    (Block.preceq_trans hanchors.2.1 hanchors.2.2) hpath
      (ghost_step_none hstopped) htargetStep

omit [Fintype V] in
/-- A target walk that passes the pivot supplies the prefix-step premise of
`ghost_transport_via_pivot`.

The next target step from a strict prefix block lies on the chain to the
target walk's actual result. Because that result also descends from `pivot`,
linearity and the one-edge depth increase put the next step at or below the
pivot. -/
theorem ghost_transport_via_pivot_of_target_passes
    {sourceTree targetTree : Finset (Block V)}
    {sourceScore targetScore : Block V → Nat}
    {sourceEligible targetEligible : Block V → Bool}
    {sourceAnchor targetAnchor pivot H : Block V}
    (hsourceRoot : RootInjectiveBelow sourceTree)
    (htargetRoot : RootInjectiveBelow targetTree)
    (hsource : Protocol.ghost sourceAnchor sourceTree sourceScore
      sourceEligible = H)
    (hanchors : Block.Preceq sourceAnchor pivot ∧
      Block.Preceq targetAnchor pivot ∧ Block.Preceq pivot H)
    (hpath : ∀ C : Block V,
      Block.Preceq targetAnchor C → C ≠ targetAnchor →
      Block.Preceq C H → C ∈ targetTree)
    (hpasses : Block.Preceq pivot
      (Protocol.ghost targetAnchor targetTree targetScore targetEligible))
    (hpersist : ∀ X C : Block V,
      Block.Preceq pivot X → Block.Preceq X H → X ≠ H →
      Protocol.ghost_step sourceTree sourceScore sourceEligible X = some C →
      Block.Preceq C H →
      C ∈ targetTree ∧ targetEligible C = true)
    (hreflect : ∀ X C : Block V,
      Block.Preceq pivot X → Block.Preceq X H →
      C ∈ targetTree → C.parent? = some X → targetEligible C = true →
      C ∈ sourceTree ∧ sourceEligible C = true)
    (hscore : ∀ C, C ∈ sourceTree → C ∈ targetTree →
      targetScore C = sourceScore C) :
    (∀ C ∈ targetTree, C.parent? = some H → targetEligible C = false) ∧
      Protocol.ghost targetAnchor targetTree targetScore targetEligible = H := by
  apply ghost_transport_via_pivot hsourceRoot htargetRoot hsource hanchors
    hpath _ hpersist hreflect hscore
  intro X hAX hXP hne
  let R := Protocol.ghost targetAnchor targetTree targetScore targetEligible
  have hPR : Block.Preceq pivot R := by
    simpa only [R] using hpasses
  have hXR : Block.Preceq X R :=
    Block.preceq_trans hXP hPR
  have hXneR : X ≠ R := by
    intro hEq
    have hPX : Block.Preceq pivot X := by
      rw [hEq]
      exact hPR
    exact hne (Block.preceq_antisymm hXP hPX)
  obtain ⟨C, hstep, hCR⟩ := ghost_walk_step_towards_result
    targetTree.card targetAnchor R X (by rfl) hAX hXR hXneR
  refine ⟨C, hstep, ?_⟩
  rcases Block.preceq_linear hCR hPR with
    hCP | hPC
  · exact hCP
  · have hchild := ghost_step_child hstep
    have hCdepth : C.depth = X.depth + 1 := depth_of_parent? hchild.2.1
    have hXdepth : X.depth < pivot.depth := by
      have hle := Block.preceq_depth_le hXP
      have hneq : X.depth ≠ pivot.depth := by
        intro heq
        exact hne (Block.preceq_eq_of_depth_le hXP (by omega))
      omega
    have hEq : pivot = C :=
      Block.preceq_eq_of_depth_le hPC (by omega)
    rw [← hEq]
    exact Block.preceq_self pivot

omit [Fintype V] in
/-- Transport through a source-side bridge without ordering that bridge and
the target anchor.

Both are ancestors of `H`, so they are comparable. If the target anchor is
already above the bridge, ordinary source transport starts there. Otherwise,
the bridge is the pivot and `hpasses` supplies the target prefix. -/
theorem ghost_transport_via_bridge_of_target_passes
    {sourceTree targetTree : Finset (Block V)}
    {sourceScore targetScore : Block V → Nat}
    {sourceEligible targetEligible : Block V → Bool}
    {sourceAnchor targetAnchor bridge H : Block V}
    (hsourceRoot : RootInjectiveBelow sourceTree)
    (htargetRoot : RootInjectiveBelow targetTree)
    (hsource : Protocol.ghost sourceAnchor sourceTree sourceScore
      sourceEligible = H)
    (hsourceBridge : Block.Preceq sourceAnchor bridge)
    (hbridgeH : Block.Preceq bridge H)
    (htargetH : Block.Preceq targetAnchor H)
    (hpath : ∀ C : Block V,
      Block.Preceq targetAnchor C → C ≠ targetAnchor →
      Block.Preceq C H → C ∈ targetTree)
    (hpasses : Block.Preceq bridge
      (Protocol.ghost targetAnchor targetTree targetScore targetEligible))
    (hpersist : ∀ X C : Block V,
      Block.Preceq bridge X → Block.Preceq X H → X ≠ H →
      Protocol.ghost_step sourceTree sourceScore sourceEligible X = some C →
      Block.Preceq C H →
      C ∈ targetTree ∧ targetEligible C = true)
    (hreflect : ∀ X C : Block V,
      Block.Preceq bridge X → Block.Preceq X H →
      C ∈ targetTree → C.parent? = some X → targetEligible C = true →
      C ∈ sourceTree ∧ sourceEligible C = true)
    (hscore : ∀ C, C ∈ sourceTree → C ∈ targetTree →
      targetScore C = sourceScore C) :
    (∀ C ∈ targetTree, C.parent? = some H → targetEligible C = false) ∧
      Protocol.ghost targetAnchor targetTree targetScore targetEligible = H := by
  rcases Block.preceq_linear hbridgeH htargetH with hbridgeTarget | htargetBridge
  · apply ghost_transport_of_source hsourceRoot htargetRoot hsource
      ⟨Block.preceq_trans hsourceBridge hbridgeTarget, htargetH⟩ hpath
    · intro X C htargetX hXH hne hstep hCH
      exact hpersist X C (Block.preceq_trans hbridgeTarget htargetX)
        hXH hne hstep hCH
    · intro X C htargetX hXH hC hparent helig
      exact hreflect X C (Block.preceq_trans hbridgeTarget htargetX)
        hXH hC hparent helig
    · exact hscore
  · exact ghost_transport_via_pivot_of_target_passes
      hsourceRoot htargetRoot hsource
        ⟨hsourceBridge, htargetBridge, hbridgeH⟩ hpath hpasses
          hpersist hreflect hscore


end Protocol
end DecoupledConsensusModel

end
