-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/SzOfPublic.lean

The numbers that a shape or a place reads ("Sz", Johnson/HonestTrace/Places.lean), as a term of the
public part that the Lean verifier makes of the configuration files ("Model.Verify.Public",
OnBytes/Model/VerifyPublic.lean). Definitions alone. No theorem.

Why. "Sz.ofHdr" (Johnson/HonestTrace/PlacesTies.lean) makes an "Sz" of the parameter file's lines
and of three arguments that are no lines: the number u0 and, for each segment, kT and NC. The public
part holds all three.
* u0: the length of the table of exponentials: the field u0 of an attention plan's shape
  (OnBytes/Model/AttentionShape.lean). In a shape that "Attention.shape" returns it hangs on the
  file's lines S and rx, not on the group, by a reading of that file; here group 0's is taken, by
  "Hd.shapeA" (Johnson/Road/HeadL5Grp.lean).
* kT and NC: fields of the shape of a segment's lookup on calls (OnBytes/Model/Forest.lean): the
  layers' layout has one for all groups; each attention plan has its own; the head's layout has one.
  "lookNo" (Johnson/HonestTrace/PlacesTiesOK.lean) reads a number off the three.

Main definitions.
* "fsA X g": the shape of the lookup of attention's group g.
* "Sz.ofPublic X": "Sz.ofHdr" at X's lines and these three.
* "Sz.segs S": the segments of a proof with S.nGr groups at profile 4. "Sz.nums S": 36 numbers of S,
  then kT and NC at these segments: a list, for tests: "Sz" holds two functions on all segments, so
  two of its terms cannot be compared by evaluation.

Limits. Beyond the plans that X holds "fsA" is the default shape, whose kT and NC are 0: so at the
attention segment of a group for which X holds no plan "Sz.ofPublic" has 0 and 0. That X holds a
plan for just the groups below nGr is not shown here. Where X holds no attention plan (by the
comment at its field A: below profile 4) that is so at every attention segment, and u0 is that of
the default shape of attention, 0. Below profile 4 a proof has no attention segment, yet "Sz.segs",
"Seg.no" and "Sz.matAt" count one for each group: the numbers of segments are then not the proof's.
"Sz" is made for profile 4 alone. The fifteen other fields of P (shifts, normalisations, expRows,
sh) are the reference numbers', not those of X's scales: "Sz.ofPublic X" says nothing of X's scales.
The library has functions of the same text, but for "default" in the place of "{}": among them
"fsAt" (Johnson/HonestTrace/FullPlanes.lean) and "Meaning.Att.fsA"
(Johnson/Goal/Meaning/AttScope.lean). This file imports neither. That they are equal to "fsA" is not
shown here. "Sz.nums" leaves out the fields of P that "Flat.sizesOf" (Johnson/Flat/Instance.lean)
leaves at the reference numbers, and says nothing of kT and NC beyond the segments of the proof. A
segment has a second lookup, on digits: its numbers are not in "Sz". NOT SHOWN HERE: that
"Sz.ofPublic X" meets "Sz.OK" and "Sz.Fit" where "Model.Verify.publicOf" returns X. "fit_ofHdr",
"ok_ofHdr" and "planes_ofHdr" of PlacesTiesOK.lean ask that the layout functions return; that they
have returned with X's own fields is not shown here. Three steps of that road are not taken here,
and whether the library has them was not searched: that the number of groups of X's layout is the
lines' L / 2^ll; that the scales and the numbers of the matrices qa at which "Attention.config" and
"Attention.group" are known to have returned are the same; that the head's shape is made at X's own
layout. Nothing on the values of cells. Nothing on any property of the protocol.

-/
import Johnson.HonestTrace.PlacesTiesOK
import Johnson.Road.HeadL5Grp

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.HonestTrace

open Inst.Model
open OnBytes.Road
open OnBytes.Model (Forest.Shape)

/-- The shape of the lookup on calls of attention's group g in a public part; the default shape
where there is no such plan. -/
def fsA (X : Model.Verify.Public) (g : ℕ) : Forest.Shape := ((X.A[g]?).map (·.fs)).getD {}

/-- **The numbers at a public part**: "Sz.ofHdr" at its parameter file's lines, at the length of
group 0's table of exponentials, and at the kT and NC of the segments' own lookups on calls. -/
def Sz.ofPublic (X : Model.Verify.Public) : Sz :=
  Sz.ofHdr X.P.h (Hd.shapeA X 0).u0 (lookNo (·.kT) X.y (fsA X) X.HLy)
    (lookNo (·.NC) X.y (fsA X) X.HLy)

/-- The segments of a proof with S.nGr groups at profile 4: of each group the feed-forward and the
attention segment, then the head. -/
def Sz.segs (S : Sz) : List Seg := ((List.range S.nGr).flatMap fun g => [.ff g, .att g]) ++ [.head]

/-- **36 numbers of S, then kT and NC at the segments of the proof.** Of P the ten sizes that
"Flat.sizesOf" takes off the file's lines. -/
def Sz.nums (S : Sz) : List ℕ :=
  [S.P.T, S.P.V, S.P.layers, S.P.d, S.P.nq, S.P.nkv, S.P.ch, S.P.f, S.P.fe, S.P.nexp,
    S.lt, S.ll, S.nGr, S.lg, S.lB, S.ln, S.u0, S.la, S.wcaf, S.NAf, S.wcad, S.NAd, S.wcar, S.lmb,
    S.wcq, S.wcx, S.lmS, S.NAs, S.wch, S.wco, S.lmbA, S.wchf, S.NHf, S.wchd, S.wchr, S.lmbH] ++
    S.segs.flatMap fun σ => [S.kT σ, S.NC σ]

end OnBytes.HonestTrace
