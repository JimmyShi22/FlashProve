-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/ReadsH.lean: the quiet step behind an attention segment's sending of its reads,
as a block without a round, at the first chain's state.

What the step does (`readsStepH`), each refusal under its test's name: the list of tables must still
be open ("A.reads.open"); what the tables read is made of what K5 heard ("A.reads.points"; at the
state: "A.reads.heard" where nothing was heard, "A.reads.look" where the lookup has laid nothing); the
tables are made by Att/TablesP.lean ("A.reads.tables"); the smallness test's list is closed and the
guard of order is asked (Johnson/Top/H0/L3/Frame.lean: closeStep, drawFront).
The tables are laid into the state through Att/TabsBack.lean's `tabsBack`.
`readsAtSH`, `readsAtH`: the step at the state; the block at a segment.
It reads, inside an attention segment, heard5, the lookup's return, the smallness test's record, the
segment's record and the ledger, and the chain's statement. It lays the tables and the closed
record. It takes no round and no column.
Of OnBytes/Model it calls, through Att/SeatC.lean's lookOf and the frame: the lookup's planeCols,
phiB and phiP; the smallness test's closeFuns, arrayFixed and funClosed.
The step on data returns the ledger's next free number as its third value; the step at the
state lays it nowhere (the record has no field for it).

Definitions with code; no theorem. Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.SeatH
import Johnson.Desc.First.Att.TabsBack
import Johnson.Desc.First.Att.Reads

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Place named need)

/-- **The step, on data.** c: the place's numbers. look: what the lookup's kind hands in for the tables. -/
def readsStepH (c : P.ParC) (zk : Array (Array E)) (look : P.LookIn) (h : P.Heard) (tl : HTailF2) (L : LinkCtx)
    (S : Statement) (F : Fork) : Except String (Attention.Tables × HTailF2 × Nat) := do
  need "A.reads.open" tl.funOpen
  let p ← named "A.reads.points" (P.ptsFrom c.geo zk h F)
  let t ← named "A.reads.tables" (P.tablesP c.geo c.mats c.nW look p)
  let t := tabsBack t
  let s ← L3.closeStep t.funs ({ L := L, F := F, tl := tl, w := () } : L3.St Unit)
  L3.drawFront s.tl L S
  pure (t, s.tl, F.next)

/-- The step at the state. -/
def readsAtSH (A : Attention.Plan) (s : First.S) : Except String First.S :=
  let c := P.parCOf A
  match s.here with
  | .att a => do
    let h ← named "A.reads.heard" s.heard5?
    let g ← named "A.reads.look" a.g
    let r ← readsStepH c g.zk (P.lookOf c.geo.lmb g) h a.tl a.L s.st a.F
    pure { s with here := .att { a with t := some r.1, tl := r.2.1 } }
  | _ => .error "A.reads.here"

/-- At segment l, group g, from the public files' record. -/
def readsAtH {Cl : Type} (W : Verify.Public) (l g : Nat) : Option (Block First.S Cl) :=
  (W.A[g]?).map fun A =>
    { name := "an attention segment's tables are made of what was heard and the list is closed"
      place := ⟨1, some l, 4, .K1⟩
      planOk := true
      rounds := []
      oracles := []
      before := []
      decide := fun s _ _ => readsAtSH A s
      claims := []
      after := [] }

end VerifiableInference.Desc.First.Att
