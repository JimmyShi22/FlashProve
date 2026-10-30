-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Compile/Batch/ListedExt.lean: the two walks of the compiled verifier over the external
strings (the stored tables), along lists that the caller hands over, and never along the list of all
positions. Definitions alone; all have code. The equations with the verifier's own two functions are
in OnBytes/TypedOracleCompiler/Compile/Batch/ListedExtLaws.lean.

No soundness: a test. This module serves the runs of lean/Ask/; it states nothing on soundness.

Why. "strictExt" (Compile/Bcs.lean) and "forestExt" (OnBytes/TypedOracleCompiler/Compile/Batch/Verifier.lean) walk
"we.all", the wiring's list of all positions of the external strings. At a stored table of depth a
that list has 2 ^ a members ("weOne", OnBytes/Maker/Wire.lean; "WireE.one", Iop/WireOf.lean: all :=
List.finRange n). The field "all" of "WireE" (Iop/Wire.lean) is a plain list, no function of Unit:
compiled code evaluates the arguments of a constructor before it builds the record, so whoever
builds a WireE builds that list, whether a walk reads it or not. (By reading, and by what is known
of Lean's compiled code; not measured here.) So the two walks take a record without that field.

Main names.
  WireELess E: the wiring of the external strings less its list of all positions. The text of
    "OnBytes.RunA.WireELess" (OnBytes/RunA/ListedDefs.lean), said again so that this file imports
    the verifier alone. "WireE.less": what is left of a wiring. The fields build and dec are read by
    neither walk: they are there for the other parts of a verifier along lists.
  strictExtL sMT isRead g listed: the strict format's test at the listed positions: where an opening
    stands, the position is read and the salt has sMT bits.
  checksExtL wl emb cms g rd: the checks of the positions of rd, in rd's order, each with the number
    of its tree; none if one of them has no opening. All members of rd are taken as read.
  forestExtL wl emb cms g rd: their forest, whole or split as the flag pr says.
  The three are "strictListed", "checksRead" and "forestRead" of OnBytes/RunA/ListedDefs.lean, said
  again over this layer's types.
Which list feeds which. listed: every position at which an opening of the string stands, read or
not: the strict format is there to refuse an opening at a position that is not read. rd: the
positions read, in the order of the wiring's list. Neither list is to be taken as an input of its
own from the proof's side: rd is computed from the verifier's messages, listed from the record from
which the string is made.
Limits: at other lists these are other functions than the verifier's: a run that calls them at lists
for which the premises of ListedExtLaws.lean are not shown is no run of the compiled verifier.
Nothing on time or memory is a theorem. Nothing on soundness. The program does not import this file.

-/
import OnBytes.TypedOracleCompiler.Compile.Batch.Verifier

set_option autoImplicit false

namespace TypedOracleCompiler.Compile.Batch
open _root_.Compile TypedOracleCompiler.Iop Rom
open _root_.Iop hiding BatchProtocol

variable {I X : Type} {lam K : ℕ} {L : BatchProtocolWithLeafBody I X}

/-- The wiring of the external strings (Iop/Wire.lean, WireE) less its list of all positions. -/
structure WireELess (E : ExtSpec) where
  which : E.Pos → ℕ
  leaf : E.Pos → ℕ
  depth : ℕ
  build : (E.Pos → Option E.Sym) → E.Str
  dec : DecidableEq E.Pos
  pr : Bool

/-- What is left of a wiring. For statements: a run builds a WireELess outright. -/
def _root_.Iop.WireE.less {E : ExtSpec} (we : WireE E) : WireELess E :=
  ⟨we.which, we.leaf, we.depth, we.build, we.dec, we.pr⟩

/-- The strict format's test of the external openings (Compile/Bcs.lean, strictExt), at the listed
positions. -/
def strictExtL (sMT : ℕ) {E : ExtSpec} (isRead : E.Pos → Bool)
    (g : E.Pos → Option (Opening lam E.Sym)) (listed : List E.Pos) : Bool :=
  listed.all fun p => match g p with
    | none => true
    | some op => isRead p && decide (op.salt.length = sMT)

/-- The checks of the external openings (checksExtW), along a list of positions, all of them taken
as read. -/
def checksExtL {E : ExtSpec} (wl : WireELess E) (emb : E.Sym → Body L) (cms : List (Dig lam))
    (g : E.Pos → Option (Opening lam E.Sym)) : List E.Pos → Option (List (ℕ × Check lam L))
  | [] => some []
  | p :: ps =>
      match g p, checksExtL wl emb cms g ps with
      | some op, some cs =>
        some ((wl.which p,
              ⟨⟨emb op.sym, op.salt⟩, wl.leaf p, op.path,
                cms.getD (wl.which p) default, wl.depth⟩) :: cs)
      | _, _ => none

/-- The forest of the external openings (forestExt), along a list of positions. -/
def forestExtL {E : ExtSpec} (wl : WireELess E) (emb : E.Sym → Body L) (cms : List (Dig lam))
    (g : E.Pos → Option (Opening lam E.Sym)) (rd : List E.Pos) : Option (List (Forest lam L)) :=
  (checksExtL wl emb cms g rd).map fun cs =>
    Forest.split wl.pr ⟨wl.depth, fun t => cms.getD t default, cs⟩

end TypedOracleCompiler.Compile.Batch
