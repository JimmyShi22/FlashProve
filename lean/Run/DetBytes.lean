-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/DetBytes.lean: the run over the single oracle, with each answer computed once.

A definition that computes, two theorems. The run is that of an oracle computation
`c : OComp (rom 256) α` (Rom/OComp.lean) in which every coin toss yields 0 (Rom/Cache.lean:
`OComp.det`).

Why: an answer of the single oracle is 256 bits as a function (Rom/OSpec.lean: `rom 256`). If the
oracle is s ↦ (i ↦ bit i of a hash of s), Lean's evaluator computes the hash anew for every bit
that is read. Lean's evaluator: what runs the tests (`#guard`) when a file is compiled; not the
kernel. Here the run takes the oracle as a function into bytes, computes the bytes of an answer
once, when the query is asked, and hands on the function that reads bits off these bytes.

Main names:
  `OComp.detB O c`: the run of c (every coin toss yields 0) at the oracle s ↦ the bits of O s.
  `detB_eq`: c.detB O = c.det (fun _ s => bytesToDig (O s)): the same value as Rom/Cache.lean's
    run.
  `detB_oBits`: at the format's oracle: c.detB (fun s => Fmt.oracle (toBytes s)) = c.det oBits
    (`oBits`, `toBytes`: Run/OracleBits.lean).

Limits: this file says nothing on a verifier; it has an equation between two ways of computing one
value.

Terms: lean/GLOSSARY.md.
-/
import Run.OracleBits
import Rom.Cache

set_option autoImplicit false

namespace Rom

/-- The run, each answer's bytes computed once. -/
def OComp.detB {α : Type} (O : List Bool → ByteArray) : OComp (rom 256) α → α
  | .pure a => a
  | .sample _ k => (k 0).detB O
  | .query _ q k =>
      let b := O q
      (k (Run.bytesToDig b)).detB O

theorem detB_eq {α : Type} (O : List Bool → ByteArray) (c : OComp (rom 256) α) :
    c.detB O = c.det (fun _ s => Run.bytesToDig (O s)) := by
  induction c with
  | pure a => rfl
  | sample n k ih => exact ih 0
  | query o q k ih => exact ih _

theorem detB_oBits {α : Type} (c : OComp (rom 256) α) :
    c.detB (fun s => _root_.Fmt.oracle (Run.toBytes s)) = c.det Run.oBits := detB_eq _ c

end Rom
