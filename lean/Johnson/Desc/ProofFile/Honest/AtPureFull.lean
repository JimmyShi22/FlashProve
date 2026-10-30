-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/AtPureFull.lean: THE HONEST PROVER's FILLING AT THE FULL SIZE: THE
TRACE AND THE READERS ARE LAID: the trace of `OnlineProverParts` (Honest/AtPure.lean) is the full-size trace with
its planes (`OnBytes.HonestTrace.theTrace`, Johnson/HonestTrace/FullPlanes.lean) where the index
serves the request (`ServesAt`, Johnson/HonestTrace/Full.lean), and nothing elsewhere; the cells'
reader is that trace read by the sub-proof's number and the matrix's label (`cellOf`); the index's
reader is the index's own matrix of digits (`entryOf`). Definitions; no theorem.

  `Owners`        WHAT IS STILL ANOTHER WRITER's, as fields: the encoded index's columns · the
                 messages' data · the lots · the later chains' halves · what the parts pass on
  `fullTrace`     the trace, general in the reader of an instance off the two files' bytes
  `fullReaders`   the readers
  `fullFill`      the filling: THE READER OF AN INSTANCE IS `ProofFile.instOf`
                 (Johnson/Desc/ProofFile/InstOf.lean: nothing where the programs' own reader rejects
                 the two files; laws on it stand there); the index is `Cm.Idx`, the index
                 committer's coins are a `TableRand` for each item of the statement, the trace is
                 `OnBytes.HonestTrace.Tr`

Why. The laws on the full-size trace speak of `theTrace X i x`; the laws on the honest side speak of
`H.trace w₀ ξ`. This file lays the one into the other, so that the first can be spent in the second:
where `fullTrace` is there, it is `theTrace` at an instance that the bytes are read as and that the
index serves: by unfolding; stated by no theorem here.

Limits. NONCOMPUTABLE: the trace picks names by choice, and whether an index serves a request is a
proposition: no test program can run this filling. THE FULL SIZE ALONE: the instance's type, the
twelve groups and the 25 sub-proofs are the reference sizes'. The range of an index is in its type
(`Cm.Idx` is a well-formed matrix of digits): so `inRange` says yes at every index. The index's
reader is `entryOf` (Johnson/HonestTrace/IndexReaders.lean): the index's matrix of digits by row and
column, in the field; that this row and column are those of docs/format/11-5-weights-in-the-table.md
is held by nobody. `Owners` is filled by nothing here. This file proves nothing about soundness,
completeness, hiding or any other property of the protocol.
-/
import Johnson.Desc.ProofFile.Honest.AtPure
import Johnson.HonestTrace.FullPlanes
import Johnson.HonestTrace.IndexReaders
import Johnson.Desc.ProofFile.InstOf
import Policy.Rel.PosGuards

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open Inst.Model (Instance ppref)
open OnBytes.HonestTrace (Tr theTrace ServesAt cellOf entryOf)

/-- The index committer's coins: for each item of the statement. -/
abbrev FullRc : Type := Nat → TableRand

/-- What a part of the first or the second chain is handed, at the full size. -/
abbrev FullIn : Type := Local Cm.Idx FullRc Inst Tr

/-- **What is still another writer's.** -/
structure Owners (X₀ X : Type) where
  /-- the encoded index's column: by the statement's item and the position -/
  enc : Pub → Cm.Idx → FullRc → Nat → Nat → Option (List Cb.Gl.F)
  /-- the data of the oracle messages' main rows: of the public part and the ground; a function of
  the public instance -/
  rows : Pub → Ground → RowDataOf Inst
  own₀ : X
  ownShared₀ : X₀
  meet : X → State (Common Cm.Idx FullRc OnBytes.TableKey) X₀ → X
  lots : List (HLot FullIn FullIn X)
  shared : Pub → Ground → List (Placed Empty (Common Cm.Idx FullRc OnBytes.TableKey) X₀)
  second : Pub → Ground → List (Placed FullIn FullIn X)

/-- **The trace.** -/
noncomputable def fullTrace (instOf : Inst → Option (Instance ppref)) (Z : Pub) (i : Cm.Idx)
    (ξ : Inst) : Option Tr :=
  open Classical in
  (instOf ξ).bind fun x => if ServesAt Z.p.X i x then some (theTrace Z.p.X i x) else none

/-- **The readers.** -/
def fullReaders (Z : Pub) (i : Cm.Idx) (rc : FullRc) (T : Tr) : Readers :=
  ⟨⟨cellOf Z.p.X T⟩, ⟨entryOf i⟩, rc⟩

variable {X₀ X : Type}

/-- **The filling at the full size.** -/
noncomputable def fullFill (O : Owners X₀ X) : OnlineProverParts Cm.Idx FullRc Tr X₀ X :=
  { trace := fullTrace ProofFile.instOf, readers := fullReaders, rows := O.rows
    inRange := fun _ => true, dummy := Policy.PosGuards.idx0, enc := O.enc
    own₀ := O.own₀, ownShared₀ := O.ownShared₀, meet := O.meet
    lots := O.lots, shared := O.shared, second := O.second }

end ProofFile.Honest
