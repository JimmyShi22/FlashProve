-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Entry/TestRecordToyValues.lean: the intermediate values of the check of the toy entry file
of OnBytes/Entry/RecordToyFiles.lean agree with the programs'.

The decision on an entry batches all its rows and makes its only checks of equations between field
elements in the last block of the proximity test. So its verdict alone only shows whether all its
parts agree. The programs therefore write 30 field elements that their verifier computes on its way
through the honest entry: blocks/frame/handover_files.cpp writes them beside the file, as
entry.targets.tsv, each with a name. Here they are compared, name by name and element by element, in
their order, with what the link's block notes in its run on the same bytes (Entry.notes,
OnBytes/Entry/File.lean). The first two are the targets of the two tables' records' first rows.

Every test is checked when the file compiles. The program does not import this file.

Not claimed. No theorem. One honest file. The values are noted by the block that decides; that a
value which is noted is the value on which the decision hangs is not shown. The like table for the
key file: OnBytes/Key/TestRecordToyValues.lean. Nothing on soundness, completeness or hiding.
-/
import OnBytes.Entry.TestRecordToy

namespace OnBytes.Entry.RecordToy

/-- What the link's block notes on the honest entry: each name with the element's coordinates. -/
def noted : Option (List (String × UInt64 × UInt64 × UInt64)) := do
  let p ← Params.Link.read entryParameters
  let t ← firstTable
  match Entry.read p t entryFile with
  | .ok r => some ((Entry.notes p r).toList.map fun x => (x.1, x.2.c0, x.2.c1, x.2.c2))
  | .error _ => none

/-- The programs' table. -/
def programsTable : List (String × UInt64 × UInt64 × UInt64) :=
  [("LINK: the target of the first table's record's first row",
    12451817362700966478, 17566924867645710912, 8987970788777825872),
  ("LINK: the target of the further table's record's first row",
    172405973160487439, 2830474031086248503, 9628177581264211128),
  ("FOLDEQ: (Col_1)'s target",
    10036124671206437307, 12257402897645374799, 7135473735814423370),
  ("FOLDEQ: (Col_1) on G_u<0>",
    11425605094511225233, 0, 0),
  ("FOLDEQ: (Col_1) on G_u<B>",
    1, 0, 0),
  ("FOLDEQ: (Col_1)'s target",
    1520013083677706218, 16690902151065025798, 11146671132606046338),
  ("FOLDEQ: (Col_1) on G_u<0>",
    11266300287204610180, 0, 0),
  ("FOLDEQ: (Col_1) on G_u<B>",
    1, 0, 0),
  ("LINK: the fold of the first table's column at its first draw",
    10036124671206437307, 12257402897645374799, 7135473735814423370),
  ("LINK: the fold of the further table's column at its first draw",
    1520013083677706218, 16690902151065025798, 11146671132606046338),
  ("LINK: the equality row's coefficient at entry 0 of the first table's folded row",
    8810061261301133068, 12561623797929830898, 13673316276929633619),
  ("BAT: target",
    16088027214915831077, 12813909004162019339, 5350834840869170619),
  ("FOLD: target",
    11132393095714533717, 5912122385223795915, 15773945321467608799),
  ("CS: y_main at the first draw",
    4610245033390277211, 6664403932986171133, 12247603799504024768),
  ("CS: y_0 at the first draw",
    0, 0, 0),
  ("CS: y_1 at the first draw",
    14125048641427789929, 1922361496424024680, 11605240001382012990),
  ("CS: target",
    11857331413464190347, 10148137663843871631, 7838769920666592942),
  ("CS: c'[0]",
    9651470133489905265, 14965268988429119906, 17414172732408540287),
  ("CS: d'[0]",
    10194113107742348736, 13086062848751095568, 16359575776647471769),
  ("CS: d's last entry",
    9774005183808390516, 13508313802088125029, 9849231886555142486),
  ("FOLD: target",
    905524903940864880, 124811699276151301, 3725190719515511119),
  ("CS: y_main at the first draw",
    4284784236584462279, 1476175966115212311, 9366850771529885294),
  ("CS: y_0 at the first draw",
    727582660214955838, 17624733631233861035, 11625242640159586577),
  ("CS: y_1 at the first draw",
    16952129146657534081, 8740561055074237515, 1329285473171455544),
  ("CS: target",
    8634268533135789985, 14265187556824736666, 6638633417759007347),
  ("CS: c'[0]",
    2786137736705121467, 16952225525088846693, 8061882748480471413),
  ("CS: d'[0]",
    598022037615883875, 3713096311223713386, 10304605848932957252),
  ("CS: d's last entry",
    15013182501093059411, 15605592176810410748, 7592966706986726534),
  ("BASE: left side of the linear check",
    12318237308676809937, 13051322481993539956, 10223099116115861010),
  ("BASE: right side of the linear check",
    12318237308676809937, 13051322481993539956, 10223099116115861010)]

#guard programsTable.length == 30
#guard noted == some programsTable

end OnBytes.Entry.RecordToy
