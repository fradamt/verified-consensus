module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusInternal.RecoveryPrefix
public import DecoupledConsensusProofs.Protocol.Handlers.Blocks
public import DecoupledConsensusProofs.Protocol.ChainState.NjGap
public import DecoupledConsensusProofs.Protocol.Handlers.HMaxCore
public import DecoupledConsensusProofs.Protocol.ChainState.NamedNjGap
public import DecoupledConsensusProofs.Objects.EmittedHeightBound
public import DecoupledConsensusProofs.Protocol.Handlers.StoreBridge
public import DecoupledConsensusProofs.Execution.BodyRetention
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

/-!
# Run-level causal recovery prefixes

All witnesses in this module come from `rho.events.take n` or
`rho.stateBefore S n`. In particular, none uses `Run.objects`, a later store,
or a whole-run nonfinality premise.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Protocol (HeightConfig)
open Internal
open Execution

variable {V : Type} [DecidableEq V] [Fintype V]

/-! ## Exact object sources -/





/-! ## Prefix monotonicity and ancestry -/



/-! ## Honest-store prefix cap -/

/-- An honest-store cap at a later event prefix restricts to every earlier
prefix. -/
theorem honestPrefixFinalityCap_of_le
    (S : Setup V) {rho : Run V} (sch : ScheduleWellFormed S rho)
    {m n : Nat} (hmn : m ≤ n) {hF0 : Height}
    (hcap : HonestPrefixFinalityCap S rho n hF0) :
    HonestPrefixFinalityCap S rho m hF0 := by
  intro v hv B hB
  exact hcap v hv B
    (NamedBodyRetention.stateBefore_bodies_mono S rho v hmn hB)

/-- The finite honest-store finality bound at one exact prefix. -/
def recoveryPrefixFinalityHeight
    (S : Setup V) (rho : Run V) (n : Nat) : Height :=
  rho.honest.sup (fun v =>
    (rho.stateBefore S n v).st.bodies.sup
      (fun B => (Protocol.derive_named S.E S.cfg B).h_F))

/-- The nested finite maximum caps every block in every honest prefix store. -/
theorem honestPrefixFinalityCap_recoveryPrefixFinalityHeight
    (S : Setup V) (rho : Run V) (n : Nat) :
    HonestPrefixFinalityCap S rho n
      (recoveryPrefixFinalityHeight S rho n) := by
  intro v hv B hB
  unfold recoveryPrefixFinalityHeight
  exact (Finset.le_sup
    (f := fun C : NamedBlock V => (Protocol.derive_named S.E S.cfg C).h_F)
    hB).trans (Finset.le_sup
      (f := fun w : V =>
        (rho.stateBefore S n w).st.bodies.sup
          (fun C => (Protocol.derive_named S.E S.cfg C).h_F))
      hv)

/-- A named ancestor of a body held in a parent-closed named store is itself
held. Local twin of `NamedCheckpointRows.ancestor_body_mem` (private there),
reproved here to avoid editing that file. -/
private theorem namedAncestor_mem {st : Protocol.NamedStore V}
    (hpc : Proofs.NamedStore.NamedParentClosed st) {A B : NamedBlock V}
    (hB : B ∈ st.bodies) (hAB : NamedBlock.Preceq A B) : A ∈ st.bodies := by
  revert hB hAB
  induction B with
  | genesis =>
      intro hB hAB
      simp only [NamedBlock.Preceq, NamedBlock.preceq, decide_eq_true_eq] at hAB
      exact hAB ▸ hB
  | node p s r gv gsv ats proposer ih =>
      intro hB hAB
      simp only [NamedBlock.Preceq, NamedBlock.preceq, Bool.or_eq_true,
        decide_eq_true_eq] at hAB
      rcases hAB with rfl | hparent
      · exact hB
      · exact ih (hpc.2 _ hB) hparent

/-- The named-body parent closure of one exact prefix state, read off the
`NodeInvariant` bundle `Proofs.NamedRuntime.stateBefore_invariants` supplies. -/
private theorem namedParentClosed_stateBefore
    (S : Setup V) (rho : Run V) (n : Nat) (v : V) :
    Proofs.NamedStore.NamedParentClosed (rho.stateBefore S n v).st :=
  (Proofs.NamedRuntime.stateBefore_invariants S rho n v).1.1.1.2.2.1



/-! ## Exact cap-or-observation split -/



/-! ## Honest cap-or-observation split -/


/-! ## Bounded recovery-height arithmetic -/

/-- The first `K`-multiple strictly above `lower + D` lies in the bounded
inclusive interval shown below. The left inequality also implies the strict
fact `lower < blocked`. -/
theorem exists_recoveryHeight_between
    (cfg : HeightConfig) (hF lower : Height) (hhF : hF ≤ lower) :
    ∃ blocked : Height,
      lower + cfg.D + 1 ≤ blocked ∧
      blocked ≤ lower + cfg.D + cfg.K ∧
      NjGap.RecoveryHeight cfg hF blocked := by
  let base : Nat := lower + cfg.D
  let blocked : Nat := cfg.K * (base / cfg.K + 1)
  have hK : 0 < cfg.K :=
    lt_of_lt_of_le (by decide : 0 < 3) cfg.K_ge_three
  have hmod : base % cfg.K < cfg.K := Nat.mod_lt base hK
  have hlowerBase : base + 1 ≤ blocked := by
    calc
      base + 1 =
          (base % cfg.K + cfg.K * (base / cfg.K)) + 1 := by
            rw [Nat.mod_add_div]
      _ ≤ cfg.K * (base / cfg.K) + cfg.K := by omega
      _ = blocked := by simp [blocked, Nat.mul_add]
  have hupperBase : blocked ≤ base + cfg.K := by
    calc
      blocked = cfg.K * (base / cfg.K) + cfg.K := by
        simp [blocked, Nat.mul_add]
      _ ≤ (base % cfg.K + cfg.K * (base / cfg.K)) + cfg.K := by omega
      _ = base + cfg.K := by rw [Nat.mod_add_div]
  have hlower : lower + cfg.D + 1 ≤ blocked := by
    simpa only [base] using hlowerBase
  have hupper : blocked ≤ lower + cfg.D + cfg.K := by
    simpa only [base] using hupperBase
  have hdebtAdd : hF + cfg.D < blocked := by
    exact (Nat.add_le_add_right hhF cfg.D).trans_lt
      ((Nat.lt_succ_self (lower + cfg.D)).trans_le hlower)
  have hdebt : cfg.D < blocked - hF :=
    Nat.lt_sub_of_add_lt (by
      simpa only [Nat.add_comm] using hdebtAdd)
  exact ⟨blocked, hlower, hupper,
    dvd_mul_right cfg.K (base / cfg.K + 1), hdebt⟩

/-! ## Prefix-local fresh rows and NJ universe -/



/-- An honest-store finality cap and a recovery height give the local NJ
universe. Parent closure keeps the chain-cap proof in the same honest store. -/
theorem honestPrefixNJUniverse_of_finalityCap
    (S : Setup V) {rho : Run V}
    (del : DeliveryWellFormed S rho)
    {n : Nat} {hF0 blocked : Height}
    (hcap : HonestPrefixFinalityCap S rho n hF0)
    (hrec : NjGap.RecoveryHeight S.cfg hF0 blocked) :
    HonestPrefixNJUniverse S rho n blocked := by
  intro v hv B hB
  have hpc := namedParentClosed_stateBefore S rho n v
  have hchainCap :
      ∀ C : NamedBlock V, NamedBlock.Preceq C B →
        (Protocol.derive_named S.E S.cfg C).h_F ≤ hF0 := by
    intro C hCB
    exact hcap v hv C (namedAncestor_mem hpc hB hCB)
  constructor
  · intro hheight
    exact NjGap.nj_of_cap_named (E := S.E) (cfg := S.cfg) hrec
      (hchainCap B (Proofs.NamedAncestry.named_self B)) hheight
  · exact NjGap.h_j_ne_recovery_height_named (E := S.E) (cfg := S.cfg)
      hrec B hchainCap



end HealingSurface
end Proofs
end DecoupledConsensusModel

end
