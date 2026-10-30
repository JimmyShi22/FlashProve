-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Key/Link.lean: a lookup of the key's proof of the ranges as a link of a key file's
first chain. Definitions only, all computable; nothing is proved here.

The first chain of a key file is the protocol's argument that the committed matrix's entries lie in
their ranges; it goes by lookups. Each lookup is one link: a block that lays the lookup's ledger
(`caller`), the lookup's own block (`K3.lookupKind`, Johnson/Desc/First/Look/K3LookupGeneral.lean), and a
block that turns the lookup's claims into rows of the verifier program's type (`layer`). When all
lookups are through, one block lays all their rows onto the group of the proximity test on the
ranges (`layRows`).

Main names.
  Claim, Lookup, lookupsOf, lookupPlace: a lookup's claims, public record and place.
  LookupRecord, FirstState, lookupSeat: what the first chain's state holds for the lookups; the
    state; how the lookup's block reads and writes it.
  caller, layer, lookupLink: the two blocks without a round, and the link.
  layerOrder, rowOfClaim, rowsInOrder: the order in which claims become rows; a claim's row.
  layRows: the block that lays the rows.

Limits. The three blocks of this file have no round and take no column: what they read of a prover's
messages they read through the state and the claims. `layer` marks the claims on the parts' keys as
paid when it has WRITTEN them into the record: that they are tested is another block's matter (the
batching's, `batchTableRows`, which is handed `(·.keys)`), and nothing in this file asks it. A
link's two fields for tests, `each` (behind a run of claims) and `tests` (behind the adding), ASK
NOTHING HERE, BY THIS FILE's HAND. What a proof file's link asks there is asked elsewhere: the
counts by the lookup's own block, by `rowsInOrder` and where the rows on the table are made
(Johnson/Desc/Key/TableRows.lean: a claim for each part); that no debt stands open by `doneG` in
`layer`, the third debt behind `layer`'s own mark. That the claims on keys are `keyClaims`' rests on
`layer`'s text: the list is counted and each claim's point and weights are held, its content is
compared with nothing. THAT EVERY SENT HIDDEN VALUE STANDS IN A CLAIM IS ASKED NOWHERE. (The row
`KeySound` is proved, with no premise (`keySound_holds`, Johnson/Goal/Conditions/KeyOpenHolds.lean),
of the description whose first chain lays these links as they stand here (`kseat_name`,
Johnson/Goal/Description/KeySeat.lean): it does not rest on what is not asked here. What that row
says, and where it is empty: that file's limits.)
`layerOrder` is written out here; that it is the order in which the verifier program lays these rows
is not proved here. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Key.One
import Johnson.Desc.First.Look.K3Key

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Key

open OnBytes OnBytes.Params
open OnBytes.Model (Fork Aff)
open VerifiableInference.Desc.Ground (takeMasksP addRowsP)
open VerifiableInference.Desc.K3 (HeardG PlaneClaim SeatG PG lookupKind doneG faceOfLkp homes rowOfAff
  rowOfPlane keyClaims)

/-- A claim that a lookup leaves: one on hidden values alone (`Aff`), or one that reads the planes
(`PlaneClaim`). -/
abbrev Claim : Type := Aff ⊕ PlaneClaim

/-- A lookup of the plan: its public record, in the verifier program's type. -/
abbrev Lookup : Type := Lkp.Public

/-- The lookups of the key's proof of the ranges, in order: the verifier program's own list
(`Wf.lookupsOf`) at the one-time chain's public values. -/
def lookupsOf (one : OneTime) : List Lookup := Wf.lookupsOf one.ranges (Wf.matrixOf one.lin)

/-- **The order in which a lookup's claims become rows.** An entry says from which run the claim is
taken (false: the claims on hidden values alone; true: the three claims on planes), its place in
that run, and the flag that `rowOfPlane` takes (read at a claim on planes alone). n: the number of
claims on hidden values alone. -/
def layerOrder (n : Nat) : List (Bool × Nat × Bool) :=
  ((List.range (n - 1)).map fun j => (false, j, true)) ++ [(true, 0, true), (false, n - 1, true),
      (true, 1, false), (true, 2, true)]

/-- The numbers of lookup i's place, for the lookup's block (`K3.lookupKind`): chain 1, link i, piece 2;
the face made of the public record; the rounds take the hidden values from number 0 on, and the
ledger has room for just the face's hidden values. -/
def lookupPlace (set : Setting) (i : Nat) (x : Lookup) : PG :=
  let f := faceOfLkp x
  { name := s!"look{i}.2.K3", chain := 1, link := i, piece := 2, set := set, scope := .once,
    face := f, first := 0, ns := f.slots }

/-- **What chain 1's state holds for the lookups**, beside the statement. -/
structure LookupRecord where
  /-- the ledger of the lookup that is open; none between lookups -/
  fork : Option Fork := none
  /-- what the open lookup's block has heard -/
  heard : Option HeardG := none
  /-- for each hidden value of the open lookup: the message and the entry that hold it -/
  home : Array Slot := #[]
  /-- the lookups' rows, as rows of the verifier program's type, lookup by lookup: written by the
  layer, laid onto the ranges' group by the block "rng.0.rows" -/
  rows : List (List OnBytes.Row) := []
  /-- the claims on the parts' keys, lookup by lookup -/
  keys : List (List Lkp.Keys) := []

/-- Chain 1's state: the statement, the book and the roots (`ChainState`), with the lookups' record.
-/
abbrev FirstState : Type := ChainState LookupRecord

/-- How the lookup's block reads and writes chain 1's state: the ledger and what was heard lie in
the lookups' record; nothing is owed from outside; a claim on hidden values alone goes to the left,
a claim on planes to the right. -/
def lookupSeat : SeatG FirstState Claim :=
  { fork := (·.base.fork), owed := fun _ => none,
    put := fun s g F => { s with base := { s.base with fork := some F, heard := some g } }
    mark := fun s F => { s with base := { s.base with fork := some F } },
    heard := (·.base.heard), claim := .inl, claimP := fun _ c => some (.inr c) }

/-- **The block in front of lookup i's rounds**; it has no round. It asks that no ledger is open and
that the lookups come in their order. It takes the entries that hold the lookup's hidden values from
two messages' ledgers: two for each part of the keys from the index-mask message, all others from
the lookups' own message. It asks that every hidden value has a home, and opens a fresh ledger with
room for just these. -/
def caller (one : OneTime) (i : Nat) (x : Lookup) : Block FirstState Claim :=
  quietAt s!"look{i}.1.caller" ⟨1, some i, 1, .frame⟩ fun s => do
    need "the caller: a ledger is open" s.base.fork.isNone
    need "the caller: the lookups come in their order" (s.base.keys.length == i)
    let f := faceOfLkp x
    let msg := one.ranges.messageId
    let o ← named "the caller: the own message's ledger does not hand out the lookup's entries"
        (takeMasksP s.d msg (f.slots - 2 * f.parts.length))
    let k ← named "the caller: the index-mask message's ledger does not hand out the lookup's \
          entries" (takeMasksP o.2 s.idx (2 * f.parts.length))
    let home := homes f (o.1.map fun j => ⟨msg, j⟩) (k.1.map fun j => ⟨s.idx, j⟩)
    need "the caller: every hidden value has a home" (home.size == f.slots)
    pure
      { s with d := k.2,
               base := { s.base with fork := some (({} : Fork).slots f.slots), heard := none,
                                     home := home } }

/-- A claim as a row of the verifier program's type: by `rowOfAff`, or by `rowOfPlane` with the
table's flag. -/
def rowOfClaim (planesAt : OnBytes.Row → Tensor → OnBytes.Row) (F : Fork) (home : Array Slot)
    (turned : Bool) : Claim → Option OnBytes.Row
  | .inl a => rowOfAff F home a
  | .inr c => rowOfPlane planesAt F home turned c

/-- The claims as rows, in a table's order. Nothing unless there are just three claims on planes,
the table has as many entries as there are claims, every entry names a claim that is there, and
every such claim has a row. Not asked: that the table names every claim just once; `layerOrder`
does. -/
def rowsInOrder (planesAt : OnBytes.Row → Tensor → OnBytes.Row) (tab : List (Bool × Nat × Bool))
    (F : Fork) (home : Array Slot) (cls : List Claim) : Option (List OnBytes.Row) :=
  let objects := cls.filter fun c => c.isLeft
  let planes := cls.filter fun c => c.isRight
  if planes.length != 3 || tab.length != cls.length then none
  else tab.mapM fun t => ((if t.1 then planes else
      objects)[t.2.1]?).bind (rowOfClaim planesAt F home t.2.2)

/-- **The block behind lookup i's rounds**; it has no round. It is handed the link's claims. It
makes them rows, in `layerOrder`; makes the claims on the parts' keys; marks as paid what the
hearing says is owed to the join; asks that nothing of the lookup is left open in the ledger
(`doneG`); and writes the rows and the claims on keys into the lookups' record. The mark is set when
the claims on keys are written, not when they are tested: see the file's limits. -/
def layer (one : OneTime) (set : Setting) (i : Nat) (x : Lookup)
    (claims : FirstState → Except String (List Claim × FirstState)) : Block FirstState Claim :=
  quietAt s!"look{i}.3.layer" ⟨1, some i, 3, .frame⟩ fun s => do
    let (cls, s') ← claims s
    let F ← named "the layer: no ledger is open" s'.base.fork
    let g ← named "the layer: nothing was heard" s'.base.heard
    let rows ← named "the layer: a claim has no row"
      (rowsInOrder (Wf.planesAt one.ranges one.codes i)
        (layerOrder (cls.filter fun c => c.isLeft).length) F s'.base.home cls)
    let keys ← named "the layer: a part's form has no claim on its keys"
        (keyClaims x F s'.base.home g)
    let F' := F.paid g.owedJoin
    need "the layer: something of the lookup is left open in the ledger (doneG)"
        (doneG (lookupPlace set i x) g F')
    pure
      { s' with base := { s'.base with fork := some F', rows := s'.base.rows ++ [rows],
                                       keys := s'.base.keys ++ [keys] } }

/-- **Lookup i as a link.** Laid only where no ledger is open. Heard: the caller, then the lookup's
block, which names the pairs (1, 0) and (1, 1) as fixed before its first draw and has no guest. The
claims come in the order objects, planes, guests, all of the second block. No test stands behind a
run of claims or behind the adding. The layer stands at the batching's place. Nothing closes. At the
end the ledger, the hearing and the homes are cleared. -/
def lookupLink (one : OneTime) (set : Setting) (i : Nat) (x : Lookup) : Link FirstState Claim :=
  { name := s!"look{i}", chain := 1, number := i
    lay := fun s => do need "a lookup's link: a ledger is open" s.base.fork.isNone; pure s
    hear := [caller one i x, lookupKind lookupSeat [(1, 0), (1, 1)] 0 [] (lookupPlace set i x)]
    order := [(1, "objects"), (1, "planes"), (1, "guests")]
    each := fun _ _ _ => .ok ()
    orderAfter := []
    batch := layer one set i x
    tests := fun _ => .ok ()
    close := []
    clear := fun s =>
      pure { s with base := { s.base with fork := none, heard := none, home := #[] } } }

/-- **The block "rng.0.rows"**; it has no round. All lookups' rows, in the lookups' order, are laid
onto the ranges' group in the statement (`addRowsP`). Asked in front: all lookups have laid their
rows; the group holds no open row and its test has not begun. -/
def layRows (one : OneTime) : Block FirstState Claim :=
  quietAt "rng.0.rows" ⟨1, none, 4, .frame⟩ fun s => do
    need "rng.0.rows: all lookups have laid their rows"
        (s.base.rows.length == (lookupsOf one).length)
    need "rng.0.rows: the ranges' group holds no open row and its test has not begun"
        ((s.d.st.groups[s.grp]?).any fun G => G.rows.isEmpty && !G.inRun)
    let d ← named "rng.0.rows: a row does not fit the ranges' group"
        (addRowsP s.d s.grp s.base.rows.flatten)
    pure { s with d := d }

end VerifiableInference.Desc.Key
