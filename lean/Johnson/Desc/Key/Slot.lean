-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Key/Slot.lean: the key file's piece for the verifier's text, as a value: the data of
the key file's rounds and the decision on a key file's three views, both made of the key file's
description (`descriptionFromPlan`, Johnson/Desc/Key/Desc.lean). Definitions only, all computable; nothing is
proved here.

Main names.
  keyInstanceOfOutOfDomainSample rec: a record's instance: the program's key written of it (`keyOf`,
    OnBytes/Slice/KeyOfRec.lean).
  KeyRun: the type of the decision: of a record and the three chains' views.
  KeyDataAndDecisionOrRefusal: the type of the piece: a refusal with words, or the data and the decision.
  keyDataAndDecisionOfDescription F: of a description F: it refuses, with the words of `planWord`, where F's own tests
    on the plan say no (`planOk`; `readsOk` is one of its clauses); where `wantedOk` or `owedOk`,
    which stand beside these, says no; and where F's own data cannot be made (`FileDescription.data`,
    Johnson/Desc/BlockSlot.lean); else it gives these data and the decision `(F.pull keyInstanceOfOutOfDomainSample).run`.
  keyDataAndDecisionOfPlannerAnswer X lay m: the same at `descriptionFromPlan m`, of the planner's answer and the sendings; behind
    it every test of the door `lawsAsk X lay m F D` (Johnson/Desc/Key/Asks.lean) is asked, and the
    piece refuses under the words of the first that says no.
  keyDataAndDecisionAtDigest X lay cfg: the same at what `madeAt X lay cfg` returns (Johnson/Desc/Key/Road.lean): of
    what the program has read of the public files, the layout file and a digest that is handed in.
  fixedDigest, keyDataAndDecisionAtFixedDigest X lay: a constant of 32 bytes (`fixedConfigurationDigest`), and `keyDataAndDecisionAtDigest` at it.
  laidOk, laidData, laidRun: a piece as three total letters: whether it is laid; its data, and
    where it refuses `emptyData`, the data of three empty lists; its decision, and where it refuses
    no, at every record and all views.

Limits.
THE FULL SIZE ALONE. `KeyRun` and `keyInstanceOfOutOfDomainSample` are typed at `RecFull`, the record of the full size's
table. At public files of another size the value may be made; the key written of a record then has
other sizes than that file's key. At the small stored set's honest file the decision says no
(evaluated); that it says no at every record is not shown.
THE DECISION IS ONE HALF. It is the run of the description on three views. That opened columns hang
under their roots, and how draws come of a hash function, is not here; the slot that takes the
decision tests the work, the draws, what is carried and the silent rounds.
THE HASH FUNCTION. The text of this file names no hash function. `keyDataAndDecisionAtDigest` takes what the program has
read of the public files, and a digest, as arguments: that they are what `publicOf` and
`configuration` return at the files is the caller's matter. Of what its term reaches through other
files this file says nothing. `keyDataAndDecisionAtFixedDigest` takes no digest at all. That it returns what
`keyDataAndDecisionAtDigest` returns at the files' own digest is Johnson/Desc/Key/NoCfgLive.lean's, under its premises:
one way; both ways where the files' own digest is not 32 zero bytes. WHOEVER LAYS `keyDataAndDecisionAtFixedDigest` DOES
NOT ASK THAT THE FILES' OWN DIGEST IS NOT 32 ZERO BYTES: nobody in the piece asks it then.
AT `keyDataAndDecisionAtFixedDigest` THE SOURCE's PARAMETER BYTES (`Given.bytes`, "as they are hashed") ARE SPELLED AT THE
FIXED DIGEST, NOT AT THE FILES' OWN: NOBODY MAY START A TRANSCRIPT FROM THEM. Whether the files' own
digest enters every query from which a challenge is drawn is what the goals' head asks of a reader
of the description (lean/Ladder.lean, head, 12): this piece does not bring it.
THE TWO TESTS BESIDE THE PLAN's. `wantedOk`: the blocks as they are laid stand at just the places,
with just the numbers of rounds, of a table that another file makes of the public values. `owedOk`:
at each place of a second such table stands a block that draws and that names, as fixed before it
draws, all that the table owes there. `wantedOk` is spent by
rounds_in_scope (Johnson/RunOne/Sound/KeyListsInScope.lean). `owedOk` stands as a premise in
statements (Johnson/Goal/Conditions/KeySoundOfOpen.lean); that a proof spends it is not traced.
THE DOOR. This file takes the list of Johnson/Desc/Key/Asks.lean as it stands: with a test more at
the list's end the piece refuses more and lays nothing else.
TWO LAYOUTS. `keyDataAndDecisionAtDigest` and `keyDataAndDecisionAtFixedDigest` take the layout file beside an X that was itself made of a
layout file: that the two are one file is the caller's matter.
WHAT IS IMPORTED. No file under Johnson/Desc/Sound, Johnson/RunOne/Sound or Johnson/RunOne/Law.
General facts on every description (Johnson/Desc/Block.lean, BlockSlot.lean) and on the planner's
parts are. No module under Johnson/RunOne/ lies beneath `descriptionFromSource`.
The planner sizes and plans all seven chains, also those that a key file has not. The decision asks
the tests on the plan again at every call. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Key.Road
import Johnson.Desc.BlockSlot
import Johnson.Desc.Key.Asks
import Johnson.Desc.TheCfg
import OnBytes.Slice.KeyOfRec
import OnBytes.Flat.EntryTerm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Key

/-! No namespace is opened, and every constant is written from the root: this file imports the door,
which may grow: a name that the door declares as it grows must not come to stand nearer than
one that is meant here. -/

/-- A record's instance: the program's key written of it. -/
def keyInstanceOfOutOfDomainSample (rec : _root_.OnBytes.Flat.RecFull) : _root_.VerifiableInference.Desc.Key.Xi :=
  ⟨_root_.OnBytes.Slice.keyOf (fun β : _root_.OnBytes.Slice.NZ => β.val) rec⟩

/-- The decision on a key file's three views: of a record and the views. -/
abbrev KeyRun : Type :=
  _root_.OnBytes.Flat.RecFull → _root_.Fmt.View → _root_.Fmt.View → _root_.Fmt.View → _root_.Bool

/-- The key file's piece: a refusal with words, or the data and the decision. -/
abbrev KeyDataAndDecisionOrRefusal : Type :=
  _root_.Except _root_.String
    (_root_.OnBytes.Maker.WholeD × _root_.VerifiableInference.Desc.Key.KeyRun)

/-- **The data and the decision of a description.** It refuses where the description's own tests on
the plan say no; where one of the two tests beside them says no; and where its own data cannot be
made. -/
def keyDataAndDecisionOfDescription
    (F : _root_.VerifiableInference.Desc.FileDescription _root_.VerifiableInference.Desc.Key.Xi) :
    _root_.VerifiableInference.Desc.Key.KeyDataAndDecisionOrRefusal :=
  match _root_.VerifiableInference.Desc.FileDescription.planWord F with
  | _root_.Option.some w => _root_.Except.error ("the key file's description: " ++ w)
  | _root_.Option.none =>
    if !_root_.VerifiableInference.Desc.FileDescription.wantedOk F then
      _root_.Except.error "the key file's description: its places are not the wanted ones"
    else if !_root_.VerifiableInference.Desc.FileDescription.owedOk F then
      _root_.Except.error "the key file's description: a drawing block does not name what is owed"
    else
      _root_.Except.map
        (fun D => (D, _root_.VerifiableInference.Desc.FileDescription.run
          (_root_.VerifiableInference.Desc.FileDescription.pull
            _root_.VerifiableInference.Desc.Key.keyInstanceOfOutOfDomainSample F)))
        (_root_.VerifiableInference.Desc.FileDescription.data F "key file")

/-- **The key file's piece**, of the planner's answer and the sendings; X and lay are handed to the
door. (m holds an X of its own; that the two are one is the caller's matter. At `keyDataAndDecisionAtDigest` they are:
`madeAt_public`, Johnson/Desc/Key/NoCfgLive.lean.) -/
def keyDataAndDecisionOfPlannerAnswer (X : _root_.OnBytes.Model.Verify.Public) (lay : _root_.ByteArray)
    (m : _root_.Johnson.G.OfPlan.Made) : _root_.VerifiableInference.Desc.Key.KeyDataAndDecisionOrRefusal :=
  _root_.Except.bind (_root_.VerifiableInference.Desc.Key.descriptionFromPlan m) fun F =>
    _root_.Except.bind (_root_.VerifiableInference.Desc.Key.keyDataAndDecisionOfDescription F) fun x =>
      match _root_.List.find? (fun t => !t.2)
          (_root_.VerifiableInference.Desc.Key.lawsAsk X lay m F x.1) with
      | _root_.Option.some t => _root_.Except.error ("the key file's description: " ++ t.1)
      | _root_.Option.none => _root_.Except.ok x

/-- **The key file's piece**, from what the program has read of the public files, the layout file
and a digest that is handed in. -/
def keyDataAndDecisionAtDigest (X : _root_.OnBytes.Model.Verify.Public) (lay cfg : _root_.ByteArray) :
    _root_.VerifiableInference.Desc.Key.KeyDataAndDecisionOrRefusal :=
  _root_.Except.bind (_root_.VerifiableInference.Desc.Key.madeAt X lay cfg)
    (_root_.VerifiableInference.Desc.Key.keyDataAndDecisionOfPlannerAnswer X lay)

/-- **The digest at which the key file's piece is laid for the verifier's text**: 32 bytes of 0x01:
`fixedConfigurationDigest` (Johnson/Desc/TheCfg.lean), the one constant that stands in the digest's place in all
three files' pieces. A CONSTANT, so that nothing beneath the slot forms a digest: the slot sits
where no digest is handed in. NOT 32 ZERO BYTES: these the description's test on the file refuses
(the clause "digest", Johnson/Desc/Key/FileOk.lean). At a constant the four clauses of that test
that read the digest hold the maker's own record against itself and against zero: nothing from
outside the maker reaches them. (That they then say yes at every record that the maker returns is
not shown.) -/
def fixedDigest : _root_.ByteArray := _root_.VerifiableInference.Desc.fixedConfigurationDigest

/-- **The key file's piece at the fixed digest**, from what the program has read of the public files
and the layout file. -/
def keyDataAndDecisionAtFixedDigest (X : _root_.OnBytes.Model.Verify.Public) (lay : _root_.ByteArray) :
    _root_.VerifiableInference.Desc.Key.KeyDataAndDecisionOrRefusal :=
  _root_.VerifiableInference.Desc.Key.keyDataAndDecisionAtDigest X lay _root_.VerifiableInference.Desc.Key.fixedDigest

/-- The data of three empty lists, at the full size's depth. -/
def emptyData : _root_.OnBytes.Maker.WholeD :=
  _root_.OnBytes.Maker.WholeD.of _root_.OnBytes.Slice.frS.P.T.a
    (_root_.OnBytes.Three.Whole.of [] [] [])

/-- Is the piece laid. -/
def laidOk (v : _root_.VerifiableInference.Desc.Key.KeyDataAndDecisionOrRefusal) : _root_.Bool := _root_.Except.isOk v

/-- The laid data; where the piece refuses: the data of three empty lists. THESE STAND AT THE FULL
SIZE's DEPTH: a test on the data's depth does not tell them from laid data: whoever wants to know
whether the piece is laid asks `laidOk` by name. -/
def laidData (v : _root_.VerifiableInference.Desc.Key.KeyDataAndDecisionOrRefusal) : _root_.OnBytes.Maker.WholeD :=
  match v with
  | _root_.Except.ok x => x.1
  | _root_.Except.error _ => _root_.VerifiableInference.Desc.Key.emptyData

/-- The laid decision; where the piece refuses: no, at every record and all views. -/
def laidRun (v : _root_.VerifiableInference.Desc.Key.KeyDataAndDecisionOrRefusal) :
    _root_.VerifiableInference.Desc.Key.KeyRun :=
  match v with
  | _root_.Except.ok x => x.2
  | _root_.Except.error _ => fun _ _ _ _ => _root_.Bool.false

end VerifiableInference.Desc.Key
