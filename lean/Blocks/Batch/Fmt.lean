-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/Batch/Fmt.lean: lemmas on the format of rounds that the compiled scheme supports.

`Iop.RoundSplits.Fmt` (Iop/BatchFmt.lean) is a condition on the annotation (`RoundSplits`) of a protocol with
slots (`BatchInteractiveOracleProof`, Iop/Batch.lean). It says that the kinds of the rounds are, in this order, if
there is a round at all: local rounds, at least one; shared rounds; local rounds; and that a
component of a prover message that is not sent (the shared component in a local round, the slot's
component in a shared round after the first) is empty. Main names: `RoundSplits.fmtFrom_app_lo`,
`RoundSplits.fmtFrom_app_sh`.

Notation: from Iop/Batch.lean: `Kind`: a round is called shared (sh) or local (lo) after its
verifier message; `RAnn r`: the annotation of one round r of the local shape: its kind, and the
splitting of a prover message of the local transcript into (m_0, m_j); `RoundSplits s`: the annotation of a
shape; `RAnn.ofSlot k r`: a round in which only the slots send: there is no shared prover message;
`RAnn.ofShared k r`: a round in which only the shared part is sent: the slots send nothing; from
Iop/BatchFmt.lean: `FPhase`: the phase of a round: before the first round; in the local rounds
before the shared ones; in the shared rounds; in the local rounds after them; `FPhase.afterLo`: the
phase after a local round; `RoundSplits.FmtFrom s A ph`: from the phase ph on, every round has a format,
and a component that is not sent is empty.

Limits: this file says nothing on the annotation of a given protocol.
-/
import Iop.BatchFmt
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

theorem FPhase.afterLo_afterLo (ph : FPhase) : ph.afterLo.afterLo = ph.afterLo := by
  cases ph <;> rfl

/-- Local rounds in which only the slots send, at least one, followed by rounds that have the format
from the phase after a local round on, have the format from the phase ph on. -/
theorem RoundSplits.fmtFrom_app_lo {t : Shape} {B : RoundSplits t} :
    ∀ (r : Round) (s : Shape) (ph : FPhase), RoundSplits.FmtFrom t B ph.afterLo →
      RoundSplits.FmtFrom ((r :: s) ++ t) (RoundSplits.app (RoundSplits.const (RAnn.ofSlot .lo) (r :: s)) B) ph
  | r, [], _, h => ⟨RAnn.noShared_ofSlot .lo r, h⟩
  | r, r' :: s, ph, h =>
    ⟨RAnn.noShared_ofSlot .lo r,
      RoundSplits.fmtFrom_app_lo r' s ph.afterLo (by rw [FPhase.afterLo_afterLo]; exact h)⟩

/-- Shared rounds after the first, in which only the shared component is sent, followed by rounds
that have the format in the shared phase, have the format in that phase. -/
theorem RoundSplits.fmtFrom_app_sh {t : Shape} {B : RoundSplits t} : ∀ s : Shape, RoundSplits.FmtFrom t B .shr →
    RoundSplits.FmtFrom (s ++ t) (RoundSplits.app (RoundSplits.const (RAnn.ofShared .sh) s) B) .shr
  | [], h => h
  | r :: s, h => ⟨RAnn.noSlot_ofShared .sh r, RoundSplits.fmtFrom_app_sh s h⟩

end Iop
