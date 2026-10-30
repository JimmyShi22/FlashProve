-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/KeyAsked.lean: the asking half of a key file's typing: the twin of the program's reading
of a key file's three chains, with every hash asked of the oracle; then any plain map.

The key file's like of OnBytes/Tie/EntryAsked.lean (the entry file's) and of
OnBytes/Tie/ProofAsked.lean (the proof file's), whose names and order it follows. The program's
reading of a key file calls the hash: in the three chains' queries, in the openings' leaves and
vertices, in the binding tree, in the table's key. OnBytes/ChecksWithHashAsArgument/M/Key/File.lean holds that
reading written once more over a monad in which the hash is asked (`M.Key.readKey`). Here it is run
from the empty record of vertices, a refusal's name is dropped, and a plain map is laid behind it,
so that it has the type that a reading in front of the key file's arm has.

Main names:
  `askedKAt O k table file j`: what the twin reads at a function O in the place of the hash: plain.
  `typedKR asm k table file j`: THE READING: the twin at the asking hash, as a tree over the family
    with one oracle; then the plain map asm.
  `typedKR_det`: its value at every family g is `askedKAt` at the function that g induces, then asm.
    No hypothesis. `typedKR_noCoin`: no coin. No hypothesis.
  `typedKR_asks`: at most (2 N1 + tailN … N2 N3) · 2 questions, under the three premises of
    `readKey_asks` (OnBytes/ChecksWithHashAsArgument/M/AtPort/Asks.lean). `typedKR_asks1`
    (OnBytes/KeyLink/KeyCountOne.lean) has a number under no premise.
  `askedKAt_oBits`: at the oracle on bit strings made from the format's hash the value is that at
    the format's own oracle.
  `typedKR_twin`: where the twin at the hash over the format's oracle returns r, the reading, at the
    oracle made from the format's hash, makes asm r.
  `KeyTwinAtO k table file j`: THE NAMED PREMISE: what the program's own reading of this file
    returns from the empty record of vertices, the twin's reading at the hash over the format's
    oracle returns too.
  `askedKAt_program`, `typedKR_program`: under it, where the program's `Key.readKey` returns r: the
    value at the format's oracle is r, and the reading, at the oracle made from the format's hash,
    makes asm r.

Limits: values and a count alone: nothing on which strings are asked. `KeyTwinAtO` is a premise
here: the two hashes agree on the hash's domain alone. The three premises on numbers are not paid
here. No decision is taken on what was read. The table and the place j are letters: the head of the
file is read by the caller. The program does not call any function of this file. Nothing on
soundness.
Terms: lean/GLOSSARY.md.

-/
import OnBytes.ChecksWithHashAsArgument.M.AtPort.Lands
import OnBytes.ChecksWithHashAsArgument.M.AtPort.Asks
import OnBytes.Tie.LinkPlain
import OnBytes.Tie.AskX

set_option autoImplicit false

namespace OnBytes.Tie

open OnBytes.TwoPort
open OnBytes.Params (TableName KeyChains)
open OnBytes.Proof (TailRead)

/-- What is kept of a run of the reading: what was read; a refusal's name is dropped. -/
def keptK (e : Except String (TailRead × Session)) : Option TailRead :=
  match e with
  | .error _ => none
  | .ok r => some r.1

/-- What the twin reads at a function O in the place of the hash: plain. -/
def askedKAt (O : ByteArray → ByteArray) (k : KeyChains) (table : TableName) (file : ByteArray)
    (j : Nat) : Option TailRead :=
  keptK (M.Key.readKey (m := Id) (Fmt.HO O) k table file j Session.start).run

/-- **THE READING**: the twin at the asking hash, then a plain map asm from what was read to a typed
value. All questions are the twin's. The program does not call it. -/
def typedKR {Out : Type} (asm : TailRead → Option Out) (k : KeyChains) (table : TableName)
    (file : ByteArray) (j : Nat) : Rom.OComp (Rom.rom 256) (Option Out) :=
  (Rom.toRom (M.Key.readKey (Fmt.HM Run.askB) k table file j Session.start).run).bind fun e =>
    .pure ((keptK e).bind asm)

variable {Out : Type} (asm : TailRead → Option Out) (k : KeyChains) (table : TableName)
  (file : ByteArray) (j : Nat)

/-- **Its value at every family of oracle functions.** NO HYPOTHESIS. -/
theorem typedKR_det (g : Rom.Fam (Rom.rom 256)) :
    (typedKR asm k table file j).det g = (askedKAt (Run.oB (g ())) k table file j).bind asm := by
  unfold typedKR askedKAt
  rw [Rom.OComp.det_bind, ZKCP.OComp.det_toRom, M.Lands.readKey_det]
  rfl

/-- It tosses no coin. NO HYPOTHESIS. -/
theorem typedKR_noCoin : (typedKR asm k table file j).NoCoin :=
  Rom.OComp.NoCoin.bind (noCoin_toRom _ (M.Lands.readKey_noCoin k table file j Session.start))
    fun _ => trivial

open OnBytes.TwoPort.M.Asks in
/-- The twin's number. The three premises are those of `readKey_asks`. -/
theorem typedKR_asks {N1 N2 N3 : Nat} (h1 : OneTimeBelow k table N1)
    (h2 : SharedBelow (OnBytes.Key.tailPublic k table) N2)
    (h3 : ∀ x first, (OnBytes.Key.oneTime k.oneTime).dryRun (OnBytes.Key.startOf k.oneTime) =
      some x → SecondBelow (OnBytes.Key.tailPublic k table) x.2 first N3) :
    (typedKR asm k table file j).QueryBound
      ((2 * N1 + tailN (OnBytes.Key.tailPublic k table) N2 N3) * 2) := by
  have e := (M.AsksLands.readKey_asks k table file j Session.start h1 h2 h3).2
  have b : (typedKR asm k table file j).QueryBound
      ((2 * N1 + tailN (OnBytes.Key.tailPublic k table) N2 N3) * 2 + 0) :=
    Rom.OComp.QueryBound.bind ((Rom.queryBound_toRom _ _).2 e) fun _ => trivial
  exact b

/-- At the oracle on bit strings made from the format's hash the value is that at the format's own
oracle. -/
theorem askedKAt_oBits : askedKAt (Run.oB (Run.oBits ())) = askedKAt Fmt.oracle := by
  funext k table file j
  unfold askedKAt
  rw [HO_oBits]

/-- **THE NAMED PREMISE**: what the program's own reading of this key file returns from the empty
record of vertices, the twin's reading at the hash over the format's oracle returns too. One
direction, at one file, on readers alone. -/
def KeyTwinAtO (k : KeyChains) (table : TableName) (file : ByteArray) (j : Nat) : Prop :=
  ∀ r, (OnBytes.Key.readKey k table file j).fromStart = .ok r →
    (M.Key.readKey (m := Id) (Fmt.HO Fmt.oracle) k table file j).fromStart = .ok r

/-- The value at a function O, by the twin's run from the empty record. -/
theorem askedKAt_fromStart (O : ByteArray → ByteArray) :
    askedKAt O k table file j =
      match (M.Key.readKey (m := Id) (Fmt.HO O) k table file j).fromStart with
      | .error _ => none
      | .ok r => some r := by
  unfold askedKAt keptK M.Proof.Reading.fromStart
  cases (M.Key.readKey (m := Id) (Fmt.HO O) k table file j Session.start).run <;> rfl

/-- **Where the twin at the hash over the format's oracle returns r, the reading, at the oracle on
bit strings made from the format's hash, makes asm r.** -/
theorem typedKR_twin (r : TailRead)
    (h : (M.Key.readKey (m := Id) (Fmt.HO Fmt.oracle) k table file j).fromStart = .ok r) :
    (typedKR asm k table file j).det Run.oBits = asm r := by
  rw [typedKR_det, askedKAt_oBits, askedKAt_fromStart, h]
  rfl

/-- Under the named premise: where the program's own reading returns r, the value at the format's
oracle is r. -/
theorem askedKAt_program (h : KeyTwinAtO k table file j) (r : TailRead)
    (hr : (OnBytes.Key.readKey k table file j).fromStart = .ok r) :
    askedKAt Fmt.oracle k table file j = some r := by
  rw [askedKAt_fromStart, h r hr]

/-- **So at the oracle on bit strings made from the format's hash the reading makes asm of what the
program has read.** -/
theorem typedKR_program (h : KeyTwinAtO k table file j) (r : TailRead)
    (hr : (OnBytes.Key.readKey k table file j).fromStart = .ok r) :
    (typedKR asm k table file j).det Run.oBits = asm r := by
  rw [typedKR_det, askedKAt_oBits, askedKAt_program k table file j h r hr]
  rfl

end OnBytes.Tie
