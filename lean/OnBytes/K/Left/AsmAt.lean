-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Left/AsmAt.lean: where the exit code 0 holds of eight files' bytes, what the program's own
reader of the entry file has read of the chain can be typed at the entry's description.

Main name:
  `asm`: under `PortYesAt` and `G.SaysLines`, for the value r that `Entry.read` returns at G's
    parameters with the three public files' digest: `assembleS (entryXD G c) dec r.chain.out` is
    some string, whatever the decision `dec`; so at `decRun`
    (OnBytes/TypedOracleCompiler/Slice/EntryRunMain.lean).

Hypotheses: `PortYesAt`; `G.SaysLines F.pol`; the ground's tables have a record (a test on G,
decided at both grounds: `record_answers`, `small_record_answers`, OnBytes/K/Left/Conv.lean).

It is `ground` (OnBytes/K/Left/LaxGround.lean), which has the strict reader's equation, and
`asm_eq` (OnBytes/K/Left/Asm.lean).

Limits: values alone: that a string can be typed says nothing on whether any verifier accepts it.
Nothing on soundness; no probability. That some files meet `PortYesAt` is not shown here.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.K.Left.Asm
import OnBytes.K.Left.LaxGround

set_option autoImplicit false

namespace OnBytes.K.Left
open OnBytes.Tie TypedOracleCompiler.Slice

/-- What the program has read of the entry's chain can be typed. -/
theorem asm (G : EntryGround) (hA : (G.q.link.table.answers == 0) = false)
    {F : Files} {id : String} {table further : Params.TableName}
    (h : PortYesAt F id table further) (hl : G.SaysLines F.pol) {r : Entry.EntryRead}
    (hr : Entry.read (linkAtCfg G.q (Params.configurationDigest [F.pol, F.lay, F.KL])) table
      F.ent = .ok r)
    {X : Type} (dec : X → _root_.Run.PQ.View → Bool) :
    ∃ π, assembleS (entryXD G (Params.configurationDigest [F.pol, F.lay, F.KL])) dec r.chain.out =
      some π := by
  obtain ⟨r', -, -, i, hr', -, -, -, -, -, e, -⟩ := ground G hA h hl
  obtain rfl : r' = r := Except.ok.inj (hr'.symm.trans hr)
  exact asm_eq G _ _ e dec

end OnBytes.K.Left
