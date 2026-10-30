-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/AttentionConfig.lean: from the parameter files to the plans of the attention
sub-proofs.

There is one attention sub-proof for each group of layers. This file fills the configuration of each
(the record Cfg of OnBytes/Model/AttentionShape.lean), makes its plan
(OnBytes/Model/AttentionPlan.lean), and checks the plan against what the layer sub-proofs say of qa,
the matrix that both kinds of sub-proof read. It follows the part of the function runStage of
verifier/src/cp_verify.cpp that builds the attention sub-proofs. That part runs only at profile 4
(the whole model, with attention), so config must be called only there. The caller is
OnBytes/Model/VerifyPublic.lean. OnBytes/Model/AttentionHeard.lean explains the terms.

The steps, in the order of the C++ program as read.
 1. The lines callA of the parameter file are read: a name, a kind of table, kinds of segments.
 2. The lines are written out again as text, and the text's digest is taken.
 3. Two tests on the parameter file's numbers.
 4. For each group of layers: the configuration is filled, the expanded calls are counted, the plan
    is made, and the plan is checked against the line iotaA_0 and against the layers' layout.
 5. The digest of the table of exponentials is taken. If the parameter file gives the digests of
    the public tables, the two must be equal.

The sections say more: One group of layers on widths and on what the caller owes; All groups on
refusals, the two digests and the table of exponentials, which the two programs compute differently.

Main definitions: readLines, callsDigest, fill, inOf, group, Config, config, configNames.

This file reads no proof. It calls a hash only on public text and on a public table. No theorem is
stated here. Its digests are not compared with the statement here. Without digest lines no test here
notices a difference between the two tables.
-/
import OnBytes.Model.Config
import OnBytes.Model.LayerLayout
import OnBytes.Model.AttentionPlan

namespace OnBytes.Attention

open OnBytes.Model (refuseIf)

/-! ## The call lines -/

/-- The kind of table with this spelling in the parameter file; nothing for any other word. -/
def Table.ofName : String → Option Table
  | "KR" => some .kr
  | "KFD" => some .kfd
  | "R16" => some .r16
  | "WH" => some .wh
  | _ => none

/-- How the parameter file spells a kind of table. -/
def Table.name : Table → String
  | .kr => "KR"
  | .kfd => "KFD"
  | .r16 => "R16"
  | .wh => "WH"

/-- The kind of segment with this spelling in the parameter file; nothing for any other word. -/
def Seg.ofName : String → Option Seg
  | "RM" => some .rm
  | "RD" => some .rd
  | "FM" => some .fm
  | "FD" => some .fd
  | "WL" => some .wl
  | "WH" => some .wh
  | "IX" => some .ix
  | _ => none

/-- How the parameter file spells a kind of segment. -/
def Seg.name : Seg → String
  | .rm => "RM"
  | .rd => "RD"
  | .fm => "FM"
  | .fd => "FD"
  | .wl => "WL"
  | .wh => "WH"
  | .ix => "IX"

/-- Reads one line callA, given without its first word: a name, a kind of table, kinds of segments.
before holds the lines read so far. Refused: a kind of table or of segment that is not known, and a
name that an earlier line has. A line of fewer than two words is refused too; the reader of the
parameter file lets none through. -/
def readLine (before : List Line) (ln : List String) : Except String Line :=
  match ln with
  | name :: kind :: segs =>
    match Table.ofName kind, segs.mapM Seg.ofName with
    | some k, some s =>
      if before.any fun o => o.name == name then throw "policy-call-list-A"
      else pure { name := name, kind := k, segs := s }
    | _, _ => throw "policy-call-list-A"
  | _ => throw "policy-call-list-A"

/-- Reads the lines that are left. soFar holds the lines read so far, the last one first. -/
def readLinesLoop : List (List String) → List Line → Except String (List Line)
  | [], soFar => pure soFar.reverse
  | ln :: rest, soFar => do
    let l ← readLine soFar ln
    readLinesLoop rest (l :: soFar)

/-- Reads the lines callA. There must be at least one, since the list has no default, and at most
twelve. Every line gives at least one expanded call, and fill admits at most twelve of these. The
lines are counted before they are read, because readLine compares each name with all names before
it. -/
def readLines (callsA : List (List String)) : Except String (List Line) := do
  refuseIf (callsA.length > 12) "policy-call-list-A"
  let lines ← readLinesLoop callsA []
  refuseIf lines.isEmpty "policy-call-list-A"
  pure lines

/-- A line as text: the word callA, the name, the kind of table and the kinds of segments, with one
blank between two words and a line feed at the end. -/
def Line.text (l : Line) : String :=
  let segs := String.join (l.segs.map fun s => " " ++ s.name)
  "callA " ++ l.name ++ " " ++ l.kind.name ++ segs ++ "\n"

/-- The digest of the call lines: the second hash function (OnBytes/Hash/SecondHashFunction.lean) under the
number 73, of the lines' text. The text is filled with zero bytes to whole words of four bytes. -/
def callsDigest (lines : List Line) : ByteArray :=
  secondHashFunction 73 (textWords (String.join (lines.map Line.text)).toUTF8)

/-- The number of calls that the lines stand for in a group of layers with the shifts sh. A line
whose table depends on the shift stands for one call for each value among the shifts. Any other line
stands for one call. -/
def expandedCalls (lines : List Line) (sh : Array Nat) : Nat :=
  let values := sh.toList.eraseDups.length
  lines.foldl (fun n l => n + (if l.kind.bySh then values else 1)) 0

/-! ## One group of layers

Widths. The numbers are natural numbers. The C++ program casts some of the parameter file's 32-bit
words to signed numbers. A word of 2^31 or more then becomes negative. Each such word is either
tested later against a lower and an upper limit under one name (lB, rx and kFD, in the function
shape), or limited before the cast: S, lmS and lmbA in this file; lt, ll, la and nmin by the layout
of the layer sub-proofs (Model.Layer.layout), which makes y. So the outcome is the same, if y and P,
the parameter file as read, come from one parameter file. The caller must make sure of this.
-/

/-- Fills the configuration of the attention sub-proof of group g. P: the parameter file as read.
y: the layout of the layer sub-proofs. s: the file of scales.
Refused: S of 32 or more, and more than twelve expanded calls. The caller has tested that lmh and
lmo are at most 24. Matrix 3 of the layout is qa, which holds queries, keys, values and outputs. -/
def fill (P : Model.PolScan) (y : Model.Layer.Lay) (s : Model.Layer.Scales) (lines : List Line)
    (g : Nat) : Except String Cfg := do
  let h := P.h
  refuseIf (h.Sx ≥ 32) "af-policy-wd"
  let sh := (Array.range y.Lam).map fun lam => s.klSh (g * y.Lam + lam)
  refuseIf (expandedCalls lines sh > 12) "policy-call-list-A"
  pure {
    lt := h.lt, lB := h.lB, H := h.H, lgk := Model.clog2 h.Gk, ldh := y.ldh, ll := h.ll,
    S := h.Sx, rx := h.rx, kFD := h.kFD, lmS := h.lmS, la := h.la, lmb := h.lmbA,
    nmin := h.nmin, NAs := h.NAs, wcH := 2 ^ h.lmh / y.T, wcO := 2 ^ h.lmo / y.T,
    wcQ := y.mrow.getD 3 0 / y.T, Ty := 2 ^ (1 + Model.lbz), lines := lines, sh := sh }

/-- What the plan of the attention sub-proof of group g gets in addition to its configuration.
hb: the target in bits (settings.hb, the line sec) minus the bits of work before a draw of
positions in a request's own rounds (settings.pow). The reader of the parameter file refuses work
that is not below sec (OnBytes/Params/File.lean, workLine; in the C++: blocks/frame/parameters.h),
so hb is at least 1.
midQ: the number that names the group's matrix qa (TMat.aId): 256 times the number of its owner, the
layer sub-proof, plus the matrix's index in the owner's list. The caller passes it.
gid: the attention sub-proofs are numbered after the layer sub-proofs, from 2 + NGr.
The owner's array holds only qa, from column 0, and has two users: the owner and this sub-proof. -/
def inOf (settings : Model.Settings) (y : Model.Layer.Lay) (midQ g : Nat) : In :=
  { hb := settings.hb - settings.pow, gid := 2 + y.NGr + g, ktO := y.kcol.getD 3 0, aO := 2,
    col0Q := 0, midQ := midQ }

/-- Makes the plan of the attention sub-proof of group g and checks it against the parameter file
and the layers' layout.
 - The line iotaA_0 is fixed by the other numbers: it must be 32 plus the depth of a tree of the
   lookup of this sub-proof's calls.
 - The plan and the layout must have the same numbers of features of qa.
 - The layer sub-proof owns qa and this sub-proof reads it. Each keeps its own records of where the
   queries (q), keys (kx), values (v) and outputs (o) are in qa, and reads qa through them. The
   records must be equal, and so must the sizes Lam, dq, dkv and ls. S2 = 2^ls, the number of
   features in a block, must divide dh, the features of a head: the reader adds a multiple of dh,
   then divides by S2.
 - A head and a feature within it number the features of a tensor one to one: q and o have H heads,
   kx and v have G. -/
def group (P : Model.PolScan) (y : Model.Layer.Lay) (s : Model.Layer.Scales) (midQ : Nat → Nat)
    (lines : List Line) (g : Nat) : Except String Plan := do
  let cf ← fill P y s lines g
  let X ← plan P.settings (inOf P.settings y (midQ g) g) cf
  refuseIf (P.h.iotaA0 != 32 + X.fs.dT) "policy-iotaA"
  let A := X.S
  refuseIf (A.fillQ != y.filled.getD 3 0 || A.featQ != y.feat.getD 3 0) "internal-qa-layout"
  Model.Layer.tensorsAgree ((y.ten.filter fun t => t.mat == 3).map fun t => (t.name, t.place))
    [("q", A.atQ), ("kx", A.atK), ("v", A.atV), ("o", A.atO)]
  refuseIf (A.Lam != y.Lam || A.dq != y.dq || A.dkv != y.dkv || A.ls != y.ls ||
    A.dh % y.S2 != 0) "plan-tensor-layout"
  refuseIf (A.atQ.J != A.cf.H * A.dh || A.atO.J != A.atQ.J || A.atK.J != A.G * A.dh ||
    A.atV.J != A.atK.J) "plan-tensor-layout"
  pure X

/-! ## All groups

Refusals. A function of this file, in any section, returns its result or the name of the test that
failed. The names and the order of the tests are those of the C++ program, by a reading of its
source (no theorem).

Both digests (steps 2 and 5 of the head) are words of the statement, which the proof's first chain
takes in as the value of its item named request. OnBytes/Proof/RequestItem.lean forms that value
from the files' lines. This file does not compare its digests with that value.
OnBytes/Model/VerifyStatement.lean does: it compares hCallsA with the item's words, and the item's
words for the table with the parameter file's lines, with which config has compared the table.

The table of exponentials. The function shape computes it in whole numbers, the C++ program in
floating point. The head of OnBytes/Model/AttentionExp.lean says what is known of their agreement.
For this file: if the parameter file gives the tables' digests, a table whose digest is not the
file's is refused, here as in the C++ program. So the two programs cannot both go on with different
tables, unless the hash collides. If the file gives none, no test here notices a difference.
-/

/-- The attention sub-proofs as far as public numbers fix them. -/
structure Config where
  /-- the plan of each group's attention sub-proof -/
  plans : Array Plan
  /-- the digest of the call lines, for the statement -/
  hCallsA : ByteArray

/-- Makes the plans of all attention sub-proofs. P: the parameter file as read. y: the layout of the
layer sub-proofs, made from the same parameter file. s: the file of scales. midQ: for each group,
the number that names its matrix qa. The tests come in the order of the C++ program. The table of
exponentials that is compared is the one in the first plan's shape. Each group's lookups read the
table in their own plan's shape; all groups have the same table, since it depends only on the lines
S and rx. The last case of the match cannot occur: the layout has already refused a model
without a group of layers, under the same name shape-L. -/
def config (P : Model.PolScan) (y : Model.Layer.Lay) (s : Model.Layer.Scales) (midQ : Nat → Nat) :
    Except String Config := do
  let h := P.h
  let lines ← readLines P.polCallsA
  refuseIf (h.Gk &&& (h.Gk - 1) != 0) "af-shape-heads"
  refuseIf (h.lmh < h.lt || h.lmh > 24 || h.lmo < h.lt || h.lmo > 24 || h.lmbA > 24 ||
    h.lmS > 24 || h.NAs == 0 || h.NAs > 64) "shape-request-matrix-A"
  let plans ← (List.range y.NGr).mapM (group P y s midQ lines)
  match plans with
  | X :: _ =>
    Model.tableHeld P .exp X.S.Tt
    pure { plans := plans.toArray, hCallsA := callsDigest lines }
  | [] => throw "shape-L"

/-- The names under which this file refuses. The refusal table-digest-exp is made by
Model.tableHeld (OnBytes/Model/Config.lean), and plan-tensor-layout also by
Model.Layer.tensorsAgree (OnBytes/Model/LayerLayout.lean). The names of the plan's own refusals are
listed in OnBytes/Model/AttentionPlan.lean. -/
def configNames : List String :=
  ["policy-call-list-A", "af-policy-wd", "policy-iotaA", "internal-qa-layout", "plan-tensor-layout",
   "af-shape-heads", "shape-request-matrix-A", "shape-L"]

end OnBytes.Attention
