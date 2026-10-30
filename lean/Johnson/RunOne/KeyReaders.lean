-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/KeyReaders.lean. **THE EIGHT READERS AND THE BOOK OF THE TABLE OF JOINTS OF THE KEY FILE (Johnson/Desc/Key/KeyMeaning.lean: KReaders · KPlan; KeyShape.lean: KBook), FILLED AT THE CARRIED STATE**: chain 1's
state FirstState := ChainState LookupRecord. Definitions alone. What each reads:
  marked    nothing marks: no block of the key file's writes a mark on a failed test and goes on
  st        the statement (oracle messages with their sample rows and ledgers; groups with their open rows): s.d.st
  grpB      the ranges' group's number, once msg.1.send has made the group: s.grp
  rowsAt l  lookup l's rows as they lie behind its layer: s.base.rows[l]: rows of the program's type (a first filling, which is not in this library, made them of the stand-ins' rows by DecOneE.rowOf)
  keysAt l  lookup l's pending rows on the matrix: of the claims on its parts' keys (s.base.keys[l]) by `verify-on-bytes`'s pure Wf.pendingRow | Wf.eqPlaces (as that first filling has it)
  pile      the one row that the batching hands on: off K13's claim: KeyState.rowOfClaim
  eval      the row (Eval) as it lies: the own group's first open row
  g         the claim's row weights
  book      the lookup's ledger (next · ns · sized · free · filled) · whether K3 has heard · the number of homes
  planOf    the plan's public values; which oracle message of the statement is the witness's message k: I ↦ 0 · B ↦ 1 · V ↦ W's number: OFF THE PLAN: the number of oracle messages that chain 1 sends in front of W's sending (that first filling typed 9)
No theorem. Nothing on soundness.
-/
import Johnson.Desc.Key.Link
import Johnson.Desc.Key.Chain1
import Johnson.Desc.Key.FileOk
import Johnson.Desc.Key.Desc
import Johnson.Desc.Key.KeyShape
import Johnson.Desc.Key.KeyLaws

set_option autoImplicit false

namespace Johnson.RunOne.KeyReaders

open OnBytes OnBytes.Params VerifiableInference.Desc.Key
open VerifiableInference.Desc.Key

/-- w: W's number in chain 1's statement. -/
def planOf (one : OneTime) (w : Nat) : KPlan :=
  { lin := one.lin, lookups := one.ranges.lookups
    orc := fun k => if k == 0 then some 0 else if k == 1 then some 1 else if k == 2 then some w else none
    num := fun o => if o == 0 then some 0 else if o == 1 then some 1 else if o == w then some 2 else none }

def pendingOf (one : OneTime) (l : Nat) (cs : List Lkp.Keys) : Option (List TensorRow) :=
  (one.ranges.lookups[l]?).map fun L =>
    (L.parts.zip cs).map fun x => Wf.pendingRow (Wf.matrixOf one.lin) L x.1 x.2 (Wf.eqPlaces (Wf.matrixOf one.lin) x.2.point)

/-- **The eight readers.** -/
def readers (one : OneTime) : KReaders FirstState :=
  { marked := fun _ => false
    st := fun s => s.d.st
    grpB := fun s => if s.grp == noId then none else some s.grp
    rowsAt := fun s l => s.base.rows[l]?
    keysAt := fun s l => (s.base.keys[l]?).bind (pendingOf one l)
    pile := fun s => s.lin.map fun L => rowOfLinClaim L.claim
    eval := fun s => s.lin.bind fun L => (s.d.st.groups[L.own]?).bind fun G => G.rows[0]?
    g := fun s => s.lin.map (·.claim.g) }

/-- **The book.** -/
def book : KBook FirstState :=
  { ledger := fun s => s.base.fork.map fun F =>
      { next := F.next, ns := F.ns, sized := F.vp.size == F.ns && F.mf.size == F.ns && F.gotF.size == F.ns
        free := (List.range (F.ns - F.next)).all fun j => !F.gotF.getD (F.next + j) true
        filled := (List.range F.next).all fun j => F.gotF.getD j false }
    heard := fun s => s.base.heard.isSome
    homes := fun s => s.base.home.size }

end Johnson.RunOne.KeyReaders
