module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.EventualHeightProgress
public import DecoupledConsensusProofs.Protocol.ChainState.RecoveryPrefix
public import DecoupledConsensusProofs.Protocol.ValidatorClient.RecordFresh
public import DecoupledConsensusProofs.Protocol.ChainState.NamedNjGap
public import DecoupledConsensusProofs.Protocol.ValidatorClient.RecoveryTimeout

@[expose] public section

/-!
# Causal recovery boundary

This module keeps recovery inside exact event prefixes. It connects prefix-wide
record freshness to one validator, replaces the whole-run timeout invariant by
an honest-store prefix-cap invariant, and composes the least finality/crossing
race. The original prefix-wide interfaces remain available as wrappers.
-/

namespace DecoupledConsensusModel
namespace Internal

open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-- Prefix-wide freshness restricts to one honest validator's local record
history. -/
theorem NoLocalHeightPairBefore.local
    {S : Setup V} {rho : Run V} {n : Nat} {blocked : Height}
    (h : NoLocalHeightPairBefore S rho n blocked)
    {v : V} (hv : v ∈ rho.honest) :
    Proofs.HealingSurface.NoLocalHeightPairBefore S rho v n blocked := by
  intro i t a hi hevent hemitted
  exact h hi hv hevent hemitted

end Internal

namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Protocol

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Prefix-bounded recovery timeout -/



/-! ## Preserved prefix-wide interfaces -/

/-! ## Named NJ/head producers -/

/-- The exact selected FG source inherits its `nj` bit from the causal prefix
universe. The action store and its strict pre-action store have the same tree
and derived-state map. -/
theorem actionSource_nj_of_honestPrefixNJUniverse
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {n : Nat} {blocked : Height}
    (huniverse : HonestPrefixNJUniverse S rho n blocked)
    {v : V} (hv : v ∈ rho.honest) {r : Round}
    (hstate : rho.stateBefore S n v =
      rho.stateBeforeTime S (S.a r) v)
    {Q : Block V}
    (hsource : actionFGSource S (actionStoreAt S rho v r) = some Q)
    (hheight : ((actionStoreAt S rho v r).st.σ Q).h = blocked) :
    ((actionStoreAt S rho v r).st.σ Q).nj = true := by
  obtain ⟨C, hC, hErase, hderive, -⟩ :=
    NamedActionSources.action_witness S rho v r Q hsource
  have hCprefix : C ∈ (rho.stateBefore S n v).st.bodies := by
    rw [hstate]
    exact hC
  have hheight' : (derive_named S.E S.cfg C).h = blocked := by
    rw [← hderive]
    exact hheight
  have hnj := (huniverse v hv C hCprefix).1 hheight'
  have hderive' : (actionStoreAt S rho v r).st.core.σ Q =
      derive_named S.E S.cfg C := by
    change (actionReadAt S rho v r).st.core.σ Q = derive_named S.E S.cfg C
    exact hderive
  change ((actionStoreAt S rho v r).st.core.σ Q).nj = true
  rw [hderive']
  exact hnj

/-- The Goldfish head read by the action cannot carry a justification at the
recovery height when the exact action prefix has the corresponding NJ
universe. -/
theorem actionHead_h_j_ne_of_honestPrefixNJUniverse
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {n : Nat} {blocked : Height}
    (huniverse : HonestPrefixNJUniverse S rho n blocked)
    {v : V} (hv : v ∈ rho.honest) {r : Round}
    (hstate : rho.stateBefore S n v =
      rho.stateBeforeTime S (S.a r) v) :
    ((actionStoreAt S rho v r).st.core.σ
      (actionHeadWith (NamedProfile.gradeContract (actionStoreAt S rho v r).cache)
        S.E S.hc (actionStoreAt S rho v r).st.core.toHealing)).h_j ≠ blocked := by
  have hhead := actionHeadWith_mem_storeBeforeTime (rho := rho) S v r
  obtain ⟨D, hDtime, hErase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime S rho (S.a r) v hhead
  have hDprefix : D ∈ (rho.stateBefore S n v).st.bodies := by
    rw [hstate]
    exact hDtime
  have hderivedNe := (huniverse v hv D hDprefix).2
  have hview := Proofs.NamedStoreBridge.derivedView_stateBeforeTime S rho (S.a r) v D hDtime
  have hσ : (actionStoreAt S rho v r).st.core.σ =
      (rho.stateBeforeTime S (S.a r) v).st.core.σ := rfl
  have hErase' : D.erase = actionHeadWith
      (NamedProfile.gradeContract (actionStoreAt S rho v r).cache)
      S.E S.hc (actionStoreAt S rho v r).st.core.toHealing := by
    exact hErase
  change ((actionStoreAt S rho v r).st.core.σ
    (actionHeadWith (NamedProfile.gradeContract (actionStoreAt S rho v r).cache)
      S.E S.hc (actionStoreAt S rho v r).st.core.toHealing)).h_j ≠ blocked
  rw [hσ, ← hErase', hview]
  exact hderivedNe

theorem actionAttestationAt_height_pair_timeout_of_honestPrefixNJUniverse
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    {n : Nat} {blocked : Height}
    (huniverse : HonestPrefixNJUniverse S rho n blocked)
    {v : V} (hv : v ∈ rho.honest) {r : Round}
    (hstate : rho.stateBefore S n v =
      rho.stateBeforeTime S (S.a r) v)
    {Q : Block V}
    (hsource : actionFGSource S (actionStoreAt S rho v r) = some Q)
    (hheight : ((actionStoreAt S rho v r).st.σ Q).h = blocked)
    (hfresh : RecordFreshAt (actionStoreAt S rho v r).record.legacy blocked) :
    (actionAttestationAt S rho v r).height_pair =
      NamedHeightPair.vote blocked
        ((actionStoreAt S rho v r).st.σ Q).T_h.root true := by
  have hnj := actionSource_nj_of_honestPrefixNJUniverse
    S adm huniverse hv hstate hsource hheight
  have hheadj := actionHead_h_j_ne_of_honestPrefixNJUniverse
    S adm huniverse hv hstate
  let nread := actionStoreAt S rho v r
  let gc := NamedProfile.gradeContract nread.cache
  show (Protocol.NamedActions.round_action_with gc S.E S.hc (S.node v)
      nread.st.core.toHealing nread.record).2.height_pair = _
  exact round_action_height_pair_timeout_of_fresh_source gc S.E S.hc (S.node v)
    nread.st.core.toHealing nread.record hsource hheight hnj hfresh hheadj






/-! ## Least causal finality/crossing boundary -/





end HealingSurface
end Proofs
end DecoupledConsensusModel

end
