module
public import DecoupledConsensusProofs.Execution.ModelVocabulary
public import DecoupledConsensusProofs.Protocol.Schedule.SeedBoundaryConeLead
public import DecoupledConsensusProofs.Protocol.Handlers.FinalityMonotoneCore
public import DecoupledConsensusProofs.Protocol.Schedule.PostHealingContinuation
public import DecoupledConsensusProofs.Protocol.Handlers.Monotone

@[expose] public section

/-!
# The complement of the common-root window

Under the gate-off frame every honest FG root is the store's own finalized
block, which only moves forward along its chain. So over a window either every
honest read shows one root, or some honest store's finalized root strictly
advances inside the window: a new finalized block revealed post-GST, the
finality case the healing track handles.
-/

namespace DecoupledConsensusModel
namespace Proofs
namespace HealingSurface

open Internal
open Execution
open Internal.HealingSurface
open Protocol
open Proofs.HealingLemmas
open Proofs.Optimistic

variable {V : Type} [DecidableEq V] [Fintype V]

/- The named boundary module keeps these predicates local to its lead module.
   Re-state them here over the core store so this consumer keeps its public
   proof-layer names without using the retired reachability route. -/
def GateOffFrameAt (S : Setup V) (rho : Run V) (M : Height) (lo hi : Round) :
    Prop :=
  ∀ read : Time, S.a lo ≤ read → read ≤ S.a hi → ∀ w ∈ rho.honest,
    (rho.storeBeforeTime S w read).core.h_j + 2 ≤ M ∧
      (rho.storeBeforeTime S w read).core.h_max = M





omit [Fintype V] in
/-- Under the gate-off frame the FG root read is the store's finalized block. -/
theorem fgRoot_eq_F_of_frame {st : Protocol.Store V} {M : Height}
    (hgate : st.h_j + 2 ≤ M) (hmax : st.h_max = M) :
    Protocol.get_fg_root st.toHealing.toFG = st.F := by
  apply NjGap.get_fg_root_eq_F_of_gap (H := M - 1)
  · exact Nat.lt_of_succ_le (Nat.le_sub_of_add_le hgate)
  · rw [hmax]
    have h1 : 1 ≤ M := le_trans (Nat.succ_le_succ (Nat.zero_le _))
      ((Nat.le_add_left 2 st.h_j).trans hgate)
    exact le_of_eq (Nat.sub_add_cancel h1)





#print axioms fgRoot_eq_F_of_frame

end HealingSurface
end Proofs
end DecoupledConsensusModel

end
