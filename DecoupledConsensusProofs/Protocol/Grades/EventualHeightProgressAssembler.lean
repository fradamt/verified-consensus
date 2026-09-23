module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Execution.EventualHeightProgressComposition
public import DecoupledConsensusProofs.Execution.RecurringArithmeticCore
public import DecoupledConsensusProofs.Execution.RecoveryGradeProcessedRead
public import DecoupledConsensusProofs.Protocol.ChainState.NamedNjGap
public import DecoupledConsensusProofs.Execution.NamedAncestry
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge
public import DecoupledConsensusProofs.Execution.Wire

@[expose] public section

/-!
# Triple-proposer recurrence height-progress assembler

The four selected honest openings are separated by two rounds. This spacing is
required because a lifecycle at `q` supplies its common grade at `q + 1`, while
the next exact-height opening consumes a common grade at `q' - 1`.

The third opening creates the first strict-height proposal. If that successor
is nonjustifiable, the fourth opening creates the next exact successor, whose
nonjustifiability latch is clear because `K ≥ 3`. The final common grade is
available one round after its opening. Therefore the sound uniform
grade-carrying lag is `4 * gap + 9`. There is no same-round G1-to-G2 shortcut.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface

variable {V : Type} [DecidableEq V] [Fintype V]









/-- Pointwise mixed result of the height ladder. Each start either has the
strong grade-bearing Claim-4 carrier or has already obtained the required
public frontier rise. The disjunction stays under `start`; mixed branches do
not fabricate a global carrier. -/
def BoundedHeightGradeOrProgressFrom
    (S : Setup V) (rho : Run V) (r0 lag : Round) : Prop :=
  0 < lag ∧
    ∀ start, r0 ≤ start → S.a (start + lag) ≤ rho.horizon →
      (∃ origin source C,
        BoundedHeightGradeSourceAt
          S rho r0 start (start + lag) origin source C) ∨
      honestHMaxAt S rho (S.a start) <
        honestHMaxAt S rho (S.a (start + lag))

private theorem assembler_runBlock_of_mem_storeBeforeTime
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    {w : V} (hw : w ∈ rho.honest) {t : Time} {D : NamedBlock V}
    (hD : D ∈ (rho.storeBeforeTime S w t).bodies) : RunBlock S rho D := by
  obtain ⟨n, hn, -⟩ := Proofs.Bridges.stateBeforeTime_eq_stateBefore S sch t
  have hD' : D ∈ (rho.stateBefore S n w).st.bodies := by
    simpa only [Run.storeBeforeTime, hn] using hD
  exact Proofs.Bridges.runBlock_of_stateBefore_mem S hw hD'

private theorem assembler_runBlock_unique_of_erase_eq
    {S : Setup V} {rho : Run V} (adm : Admissible S rho)
    {A D : NamedBlock V} (hA : RunBlock S rho A) (hD : RunBlock S rho D)
    (herase : A.erase = D.erase) : A = D :=
  adm.toNamedRootCollisionFree.root_injective A D hA hD A D
    (Or.inl (Proofs.NamedAncestry.named_self A))
    (Or.inr (Proofs.NamedAncestry.named_self D))
    (by rw [← Proofs.NamedWire.erase_root A, ← Proofs.NamedWire.erase_root D, herase])

/-- A single bounded grade-bearing source raises the public frontier by its
declared bound. -/
theorem honestHMaxAt_lt_of_boundedHeightGradeSourceAt
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    {r0 start bound origin source : Round} {C : NamedBlock V}
    (hsource : BoundedHeightGradeSourceAt
      S rho r0 start bound origin source C) :
    honestHMaxAt S rho (S.a start) < honestHMaxAt S rho (S.a bound) := by
  obtain ⟨v, hv⟩ := Protocol.honest_nonempty_of_honestCommittees hcom
  have hCmem : C.erase ∈
      (rho.storeBeforeTime S v (S.a source)).core.T :=
    gradeFormsAt_processedAtRead_of_action_le
      S adm hsource.grade hv (le_refl (S.a source))
  obtain ⟨D, hDbody, hDerase⟩ :=
    Proofs.NamedStoreBridge.exists_named_of_mem_stateBeforeTime
      S rho (S.a source) v hCmem
  have hDrun : RunBlock S rho D :=
    assembler_runBlock_of_mem_storeBeforeTime
      S adm.toNamedScheduleWellFormed hv hDbody
  have hDC : D = C :=
    assembler_runBlock_unique_of_erase_eq
      adm hDrun hsource.lifecycle.runBlock hDerase
  have hCbody : C ∈
      (rho.storeBeforeTime S v (S.a source)).bodies := by
    simpa only [hDC] using hDbody
  have hheightLocal :
      (Protocol.derive_named S.E S.cfg C).h ≤
        (rho.storeBeforeTime S v (S.a source)).core.h_max :=
    Proofs.NamedStoreBridge.heights_le_hMax_stateBeforeTime
      S rho (S.a source) v C hCbody
  have hheightPublic : (Protocol.derive_named S.E S.cfg C).h ≤
      honestHMaxAt S rho (S.a source) :=
    hheightLocal.trans
      ((storeBeforeTime_hMax_le_storeAt
          S adm.toNamedScheduleWellFormed v (S.a source)).trans
        (localHMax_le_honestHMaxAt S rho (S.a source) hv))
  exact hsource.sourceAbove.trans_le
    (hheightPublic.trans
      (honestHMaxAt_mono S adm.toNamedScheduleWellFormed
        (Assembly.a_mono S hsource.sourceUpper)))

/-- The pointwise mixed ladder result projects to the unconditional public
height-progress contract. -/
theorem eventualHeightProgressFrom_of_boundedHeightGradeOrProgress
    (S : Setup V) {rho : Run V} (adm : Admissible S rho)
    (hcom : HonestCommittees S rho.honest)
    {r0 lag : Round}
    (h : BoundedHeightGradeOrProgressFrom S rho r0 lag) :
    EventualHeightProgressFrom S rho r0 lag := by
  refine ⟨h.1, ?_⟩
  intro start hr0 hhor
  rcases h.2 start hr0 hhor with hsource | hprogress
  · obtain ⟨origin, source, C, hsource⟩ := hsource
    exact honestHMaxAt_lt_of_boundedHeightGradeSourceAt
      S adm hcom hsource
  · exact hprogress








/-
/-- A common grade discharges the selected-G2 totality field of Claim 1 at
every honest action store. The remaining Claim-1 obligations are filter/root
retention facts, not grade-selection facts. -/
theorem grade2Block_exists_at_action_of_gradeFormsAt
    (S: Setup V) {rho: Run V} {r: Round} {P: Block V}
    (hforms: NamedGradeFormsAt S rho r P):
    ∀ u ∈ rho.honest, ∃ Q: Block V,
      Protocol.grade2_block S.E S.hc
        (actionStoreAt S rho u r).toHealing r = some Q:= by
  intro u hu
  let ast:= actionStoreAt S rho u r
  have hgraded:= gradeFormsAt_actionStore S hforms hu
  have hsome:
      (Protocol.grade2_block S.E S.hc ast.toHealing r).isSome = true:= by
    refine deepest?_isSome_of_compatible ?_
      ⟨P, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
    · intro X hX Y hY
      exact Proofs.HealingLemmas.G2_compatible S.E
        (Finset.mem_filter.mp hX).2 (Finset.mem_filter.mp hY).2
    · simpa only [ast] using hgraded.1
    · simpa only [ast] using hgraded.2
  exact Option.isSome_iff_exists.mp hsome
-/





end HealingSurface
end Proofs
end DecoupledConsensusModel

namespace DecoupledConsensusModel.Proofs.HealingSurface
#print axioms honestHMaxAt_lt_of_boundedHeightGradeSourceAt
#print axioms eventualHeightProgressFrom_of_boundedHeightGradeOrProgress
end DecoupledConsensusModel.Proofs.HealingSurface

end
