-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Tab/TabH.lean:
the tables of what the head's costly keys read, and the rows that read them. Definitions with code.

Terms. Honest/K3/GLOSSARY.md; a table: `Memo.tab` (Honest/K3/Memo.lean); the rows: `InnerH`
(Honest/K3/Tab/SisterH.lean).

What is defined.
  `nrTab`: the normalized activations: position, channel. `whTab`: the head's weights: entry of the
    vocabulary, channel.
  `colTabH`: which entry of which segment stands in a column: call, column.
  `innerTabH`: the rows off three arrays, with the library's formula behind each.
  `lwTab`: the third of these arrays: the checked token's logit: position. It is made of the two
    others: each logit is `lgBy` off their rows.

How it is meant. Whoever wants a table made once binds it by a let in front of the structure that
one application returns (Honest/K3/Tab/TabHSeat.lean does).

Imported. Honest/K3/Memo.lean, Honest/K3/Tab/SisterH.lean: nothing of the seated readers, so that
this file stands over little.

Limits. The sizes are read off the head's own structures (the numbers of positions, of channels and
of entries; a call's number of columns). No statement rests on a size: beyond an array's end the
formula itself is read. Nothing says how long anything takes. The equations are in
Honest/K3/Tab/TabHLaw.lean.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Memo
import Johnson.Desc.ProofFile.Honest.K3.Tab.SisterH

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.TabH
open OnBytes.Model OnBytes.Ends.H
open ProofFile.Honest.K3.Memo (tab)

variable {R : Type} [Field R] (P : PubH) (cell : NameH → R)

/-- The normalized activations: position, channel. -/
def nrTab : Array (Array R) := tab P.h.T fun t => tab P.h.d fun k => nrm P cell k t

/-- The head's weights: entry of the vocabulary, channel. -/
def whTab : Array (Array R) := tab P.h.V fun v => tab P.h.d fun k => wH P cell k v

/-- Which entry of which segment stands in a column: call, column. -/
def colTabH : Array (Array (Option (String × ℕ))) :=
  tab P.L.calls.size fun q => tab (2 ^ (P.L.calls.getD q default).lJ) fun j => colH P.L q j

/-- **The rows off three arrays.** Beyond an array's end the library's formula is read. -/
def innerTabH (nr wh : Array (Array R)) (lw : Array R) : InnerH R :=
  { nr := fun t => ⟨nr.getD t #[], fun k => nrm P cell k t⟩
    wh := fun v => ⟨wh.getD v #[], fun k => wH P cell k v⟩
    lw := ⟨lw, fun t => lg P cell (P.win.getD t 0) t⟩ }

/-- The checked token's logit: position. Made of the two arrays before it: each logit is `lgBy` off
their rows. -/
def lwTab (nr wh : Array (Array R)) : Array R :=
  let I := innerTabH P cell nr wh #[]
  tab P.h.T fun t => lgBy P I (P.win.getD t 0) t

end ProofFile.Honest.K3.TabH
