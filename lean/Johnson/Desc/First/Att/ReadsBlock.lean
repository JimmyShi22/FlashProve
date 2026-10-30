-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/ReadsBlock.lean: the quiet step behind an attention segment's sending of its reads,
as a block without a round, at the first chain's state, with the tables made by Att/Tables.lean of the
four records of OnBytes/Model's verifier. Att/ReadsH.lean is the same step on what K5 itself heard.

`readsStepE`: Att/Reads.lean's step, line for line, with each refusal under its test's name:
"A.reads.open", "A.reads.tables", then the names of Johnson/Top/H0/L3/Frame.lean's closeStep and drawFront;
at the state: "A.reads.heard" where the lookup's return or the records are not laid.
`readsAtS`, `readsBlock`, `readsAt`: the step at the state; the block; the block at a segment.
It reads, inside an attention segment, the smallness test's record, the lookup's return, the four
records, the segment's record and the ledger, and the chain's statement. It lays the tables and the
closed record. It takes no round and no column.
The block is laid behind the block of the sending itself (Block.andThen), at that block's place.
The step on data returns the ledger's next free number as its third value; the step at the state
lays it nowhere (the record has no field for it).

Definitions with code; no theorem. Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.Block
import Johnson.Desc.First.State
import Johnson.Desc.First.Att.Reads
import OnBytes.Model.VerifyPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Place named need)

/-- **The step, on data, each refusal under its test's name.** Returns the tables, the closed record, and the next free number. -/
def readsStepE (P : Attention.Plan) (tl : HTailF2) (f : Attention.First) (L : LinkCtx) (S : Statement) (F : Fork) :
    Except String (Attention.Tables × HTailF2 × Nat) := do
  need "A.reads.open" tl.funOpen
  let t ← named "A.reads.tables" (Tab.tables P.S P.mats P.nW f.g f.planes f.scores f.d f.x)
  let s ← L3.closeStep t.funs ({ L := L, F := F, tl := tl, w := () } : L3.St Unit)
  L3.drawFront s.tl L S
  pure (t, s.tl, F.next)

/-- The step at the state. -/
def readsAtS (P : Attention.Plan) (s : First.S) : Except String First.S :=
  match s.here with
  | .att a =>
    match a.g, a.planes, a.scores with
    | some g, some planes, some scores =>
      (readsStepE P a.tl ⟨g, planes, scores, a.d, a.x⟩ a.L s.st a.F).map fun r =>
        { s with here := .att { a with t := some r.1, tl := r.2.1 } }
    | _, _, _ => .error "A.reads.heard"
  | _ => .error "A.reads.here"

/-- The block without a round. -/
def readsBlock {Cl : Type} (P : Attention.Plan) (place : Place) : Block First.S Cl :=
  { name := "an attention segment's tables are made and the list is closed"
    place := place
    planOk := true
    rounds := []
    oracles := []
    before := []
    decide := fun s _ _ => readsAtS P s
    claims := []
    after := [] }

/-- At segment l, group g, from the public files' record. -/
def readsAt {Cl : Type} (W : Verify.Public) (l g : Nat) : Option (Block First.S Cl) :=
  (W.A[g]?).map fun P => readsBlock P ⟨1, some l, 4, .K1⟩

end VerifiableInference.Desc.First.Att
