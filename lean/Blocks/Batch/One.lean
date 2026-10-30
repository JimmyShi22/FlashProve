-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/Batch/One.lean: helper lemmas for one slot of a protocol with slots.

Protocols with slots: `BatchInteractiveOracleProof`, Iop/Batch.lean.
`BRho.rep`: the verifier's randomness of a batch in which every slot sees ρ; `BRho.slot_rep`: each
of its slots is ρ. Also: `BatchInteractiveOracleProof.ReadsAtMost.one`.

Limits: the declarations of this file name no protocol: they are for every annotation (`RoundSplits`) or
every `BatchInteractiveOracleProof`.
-/
import Iop.BatchSlot
import Blocks.Batch.Hvzk
import Blocks.Batch.Sound
import Blocks.ErrSup
import Blocks.LevelAcc
import Blocks.LevelLocal
import Blocks.LevelSound
import Blocks.LinkHVZK_rs
import Blocks.LinkSound
import Blocks.Reads
import Iop.RbrLast
import Mathlib.Data.FinEnum

set_option autoImplicit false

namespace Iop

/-- The verifier's randomness of a whole batch in which every slot sees ρ. -/
def BRho.rep (N : ℕ) : {s : Shape} → (A : RoundSplits s) → Rho s → BRho N s A
  | [], _, _ => ()
  | _ :: _, (⟨.sh, _, _, _, _, _, _, _, _, _⟩, A), (c, ρ) => (c, BRho.rep N A ρ)
  | _ :: _, (⟨.lo, _, _, _, _, _, _, _, _, _⟩, A), (c, ρ) => (fun _ => c, BRho.rep N A ρ)

theorem BRho.slot_rep {N : ℕ} (j : Fin N) :
    ∀ {s : Shape} (A : RoundSplits s) (ρ : Rho s), (BRho.rep N A ρ).slot j = ρ
  | [], _, _ => rfl
  | r :: s, (⟨.sh, _, _, _, _, _, _, _, _, _⟩, A), (c, ρ) => by
      show ((c, (BRho.rep N A ρ).slot j) : r.Chal × Rho s) = (c, ρ)
      rw [BRho.slot_rep j A ρ]
  | r :: s, (⟨.lo, _, _, _, _, _, _, _, _, _⟩, A), (c, ρ) => by
      show ((c, (BRho.rep N A ρ).slot j) : r.Chal × Rho s) = (c, ρ)
      rw [BRho.slot_rep j A ρ]

/-- For N > 0: what bounds the positions read by a batch of N slots bounds those read by one
verifier. -/
theorem BatchInteractiveOracleProof.ReadsAtMost.one {X : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof X E} {N q : ℕ}
    (hN : 0 < N) (h : Q.ReadsAtMost N q) (x : X) (ρ : Rho Q.loc.shape) :
    (Q.loc.extReads x ρ).card ≤ q := by
  classical
  refine le_trans (Finset.card_le_card ?_) (h (fun _ => some x) (BRho.rep N Q.ann ρ))
  intro p hp
  refine Finset.mem_biUnion.mpr ⟨⟨0, hN⟩, Finset.mem_univ _, ?_⟩
  show p ∈ Q.loc.extReads x ((BRho.rep N Q.ann ρ).slot ⟨0, hN⟩)
  rw [BRho.slot_rep]
  exact hp

end Iop
