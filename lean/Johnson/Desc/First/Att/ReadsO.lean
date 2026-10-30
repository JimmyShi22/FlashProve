-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/ReadsO.lean: the quiet step behind an attention segment's sending of its
reads, as a block without a round, at the first chain's state: Att/ReadsH.lean's step with the
smallness test's two texts of Johnson/Desc/First/K8/Order.lean (close, front) in the place of
Johnson/Top/H0/L3/Frame.lean's closeStep and drawFront.

What the step does (`readsStepO`), each refusal under its test's name: the list of tables must still
be open ("A.reads.open": the record's field, read outright); what the tables read is made of what K5
heard ("A.reads.points"); the tables are made by Att/TablesP.lean ("A.reads.tables"); the list is
closed and the guard of order is asked (under K8/Order.lean's own names).
`readsAtSO`, `readsAtO`: the step at the state; the block at a segment.
It reads and lays what Att/ReadsH.lean's step reads and lays. It takes no round and no column.
What the lookup's kind hands in for the tables is Att/LookO.lean's lookOfO. Of OnBytes/Model's
functions that can refuse it calls the ledger's shown alone (through Att/LeftP.lean).
That it says yes where Att/ReadsH.lean's step does, with the same next state, is
Att/ReadsOAgrees.lean's theorem; the refusals' names differ.
The step on data returns the ledger's next free number as its third value; the step at the
state lays it nowhere (the record has no field for it).

Definitions with code; no theorem. Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.SeatO
import Johnson.Desc.First.Att.TabsBack
import Johnson.Desc.First.K8.Order

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Place named need)

/-- **The step, on data.** c: the place's numbers. look: what the lookup's kind hands in for the
tables. -/
def readsStepO (c : P.ParC) (zk : Array (Array E)) (look : P.LookIn) (h : P.Heard) (tl : HTailF2)
    (L : LinkCtx) (S : Statement) (F : Fork) :
    Except String (Attention.Tables × HTailF2 × Nat) := do
  need "A.reads.open" (!tl.funClosed)
  let p ← named "A.reads.points" (P.ptsFrom c.geo zk h F)
  let t ← named "A.reads.tables" (P.tablesP c.geo c.mats c.nW look p)
  let t := tabsBack t
  let tl' ← K8.Order.close tl t.funs
  K8.Order.front tl' L S
  pure (t, tl', F.next)

/-- The step at the state. -/
def readsAtSO (A : Attention.Plan) (s : First.S) : Except String First.S :=
  let c := P.parCOf A
  match s.here with
  | .att a => do
    let h ← named "A.reads.heard" s.heard5?
    let g ← named "A.reads.look" a.g
    let r ← readsStepO c g.zk (P.lookOfO c.geo.lmb g) h a.tl a.L s.st a.F
    pure { s with here := .att { a with t := some r.1, tl := r.2.1 } }
  | _ => .error "A.reads.here"

/-- At segment l, group g, from the public files' record. -/
def readsAtO {Cl : Type} (W : Verify.Public) (l g : Nat) : Option (Block First.S Cl) :=
  (W.A[g]?).map fun A =>
    { name := "an attention segment's tables are made of what was heard and the list is closed"
      place := ⟨1, some l, 4, .K1⟩
      planOk := true
      rounds := []
      oracles := []
      before := []
      decide := fun s _ _ => readsAtSO A s
      claims := []
      after := [] }

end VerifiableInference.Desc.First.Att
