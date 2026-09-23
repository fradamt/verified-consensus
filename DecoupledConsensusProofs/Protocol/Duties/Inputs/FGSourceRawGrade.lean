module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Grades.RecoveryGenuineClearNextVote
public import DecoupledConsensusProofs.Protocol.Grades.RecoveryG1AfterCutoffReflection
public import DecoupledConsensusProofs.Execution.FGSelectorWitness
public import DecoupledConsensusProofs.Protocol.Grades.RelativeCrossReader
public import DecoupledConsensusProofs.Protocol.Grades.RelativeSupporter
public import DecoupledConsensusProofs.Protocol.Grades.GradeFormsBridge
public import DecoupledConsensusProofs.Protocol.ValidatorClient.Schedule
public import DecoupledConsensusProofs.Protocol.Grades.Persistence
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge

@[expose] public section

/-!
# Raw grades from an actual FG source

An active selected G2 at the source action bounds the source's finalized
block. One-delay finality relay then bounds each reader's finalized block
at the first interior vote read. This supplies the grade-delivery guard.
No common frontier, recovery frame, or previous-head admission is assumed.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal Execution Internal.HealingSurface
open Protocol Proofs.HealingLemmas Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]




/-! ## Prepared relative-grade replacements -/

/-- A selected prepared Q2 at an honest action has relative G1 at another
honest reader's G1-domain read when the cross-reader body guard holds. -/
theorem selectedG2_G1_at_read_after_cutoff
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (_hbelow : BelowOneThird S rho.honest)
    {r : Round} (ready : GradeRoundReady S rho r)
    (_hhor : S.a r ≤ rho.horizon)
    {p w : V} (hp : p ∈ rho.honest) (hw : w ∈ rho.honest)
    {Q : Block V}
    (hQ : PhaseGrades.nodeQ2 S (actionReadAt S rho p r) r = some Q)
    (hguard : CrossReaderBodyReadyGuard S rho r p w Q) :
    PhaseGrades.storeGrade S.E S.hc
      (PhaseGrades.readAt S rho
        (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st r .g1 Q = true := by
  have hG2 := selectedQ2_storeGrade_at_g2Domain S adm hQ
  exact storeGrade_g1_of_storeGrade_g2_cross_reader
    S rho adm.toNamedAdmissibleCore r
      (twoCutoffDelivery_of_core S adm.toNamedAdmissibleCore ready.1)
      ready.2 p w hp hw Q hG2 hguard

/-- A nonempty prepared FG source exposes a selected Q2 with relative G1 at
the target reader's G1-domain read. -/
theorem actionFGSource_rawG1_at_read_after_cutoff
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hbelow : BelowOneThird S rho.honest)
    {r : Round} (ready : GradeRoundReady S rho r)
    (hhor : S.a r ≤ rho.horizon)
    {p w : V} (hp : p ∈ rho.honest) (hw : w ∈ rho.honest)
    {B : Block V}
    (hsource : actionFGSource S (actionStoreAt S rho p r) = some B)
    (hguard : ∀ Q,
      PhaseGrades.nodeQ2 S (actionReadAt S rho p r) r = some Q →
      CrossReaderBodyReadyGuard S rho r p w Q) :
    ∃ Q : Block V,
      PhaseGrades.nodeQ2 S (actionReadAt S rho p r) r = some Q ∧
      PhaseGrades.storeGrade S.E S.hc
        (PhaseGrades.readAt S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st r .g1 Q = true := by
  cases hQ : PhaseGrades.nodeQ2 S (actionReadAt S rho p r) r with
  | none =>
      have hsource' := hsource
      simp only [actionFGSource, actionStoreAt_round] at hsource'
      have hround : S.hc.round_of
          (actionStoreAt S rho p r).st.core.toHealing.s = r := by
        simpa only [Protocol.Store.toHealing] using
          actionStoreAt_round S rho p r
      rw [hround] at hsource'
      have hQ' : Protocol.grade2_block_with
          (NamedProfile.gradeContract (actionStoreAt S rho p r).cache)
          S.E S.hc (actionStoreAt S rho p r).st.core.toHealing r = none := by
        simpa only [PhaseGrades.nodeQ2, PhaseGrades.nodeRead] using hQ
      rw [hQ'] at hsource'
      simp only [Protocol.fg_source_with] at hsource'
      cases hsource'
  | some Q =>
      have hQorig : PhaseGrades.nodeQ2
          S (actionReadAt S rho p r) r = some Q := by
        rw [hQ]
      exact ⟨Q, rfl,
        selectedG2_G1_at_read_after_cutoff
          S adm hbelow ready hhor hp hw hQorig (hguard Q hQorig)⟩


/-- The first-interior records is the same prepared G1-domain fact, for every
honest reader. -/
theorem actionFGSource_rawG1_at_firstInterior
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hbelow : BelowOneThird S rho.honest)
    {r : Round} (ready : GradeRoundReady S rho r)
    (hhor : S.a r ≤ rho.horizon)
    {p : V} (hp : p ∈ rho.honest) {B : Block V}
    (hsource : actionFGSource S (actionStoreAt S rho p r) = some B)
    (hguard : ∀ w, w ∈ rho.honest → ∀ Q,
      PhaseGrades.nodeQ2 S (actionReadAt S rho p r) r = some Q →
      CrossReaderBodyReadyGuard S rho r p w Q) :
    ∀ w ∈ rho.honest, ∃ Q : Block V,
      PhaseGrades.nodeQ2 S (actionReadAt S rho p r) r = some Q ∧
      PhaseGrades.storeGrade S.E S.hc
        (PhaseGrades.readAt S rho
          (DecoupledConsensusModel.Protocol.domain S.E S.hc r .g1) w).st r .g1 Q = true := by
  intro w hw
  exact actionFGSource_rawG1_at_read_after_cutoff
    S adm hbelow ready hhor hp hw hsource (hguard w hw)


#print axioms selectedG2_G1_at_read_after_cutoff
#print axioms actionFGSource_rawG1_at_read_after_cutoff
#print axioms actionFGSource_rawG1_at_firstInterior

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
