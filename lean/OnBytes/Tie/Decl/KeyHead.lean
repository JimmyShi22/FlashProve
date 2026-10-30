-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Decl/KeyHead.lean: the reading of a key file's head in front of the arms of the compiled
verifier: from the key file's bytes, at public digests d, to the table's root and the record: the
table by a plain parse, the record's seeds asked of the oracle.

A bound that takes a key's reading in front of the arms [`three_arms_keyRead_joint`,
Johnson/TypedOracleCompiler/RecCompile/ThreeArmsKeyRead.lean: not in this library] takes it as a letter PreK : D →
UK → a tree over the one oracle that returns a root with a record or nothing, and asks three things
of it at every d and uK: no coin; no public string; at most cK questions, cK one number. Here is
such a term at the program's own steps, with these three laws under no hypothesis, its value at
every family, and its value at the oracle made from the format's hash.

Letters: D, with `cfgOf` (the digest of the public files in d) and `tab` (the table at d by which
queries at public strings are answered); Pt, the public strings, a decidable property; f, the
field; sh, the tables' shape: NO PLANNER STANDS IN THE TERM; mk, from the table and the seeds to
what is returned (at use: the root as a digest, and the record of the seeds and the table's
answers).

Main names:
  `preK`: THE TERM. `Key.readTable sh` at d's digest; a refusal returns nothing and asks nothing;
    else the text of `recordSeeds` at the asking hash (`seedsBy Run.askB`,
    OnBytes/Tie/EntryAskM.lean) at the table's name under d's digest, with the queries at public
    strings answered by the table (`pinP`, PinPred.lean); then mk.
  `preK_noCoin`, `preK_off`, `preK_asks`: no coin; it asks no public string; at most
    2 `seedCalls sh.cubeBits sh.answers` + 1 questions: a number of the shape alone. NO HYPOTHESIS.
  `preK_none`, `preK_det`: its value at every family.
  `preK_program`: at the oracle made from the format's hash, if the table holds that oracle's own
    values at the public strings and the table's root has 32 bytes: the program's own seeds at the
    table's name (`recordSeeds`), then mk.

Limits. The three laws hold of every such term, whatever it reads: the reading is trusted for
nothing, and a term that always refuses has them too: they have force only beside `preK_program`.
WHAT THE PIN DOES NOT GIVE: that the seeds' text asks no public string. By its text it asks calls
with the numbers 160 and 162 alone, so where the public strings are calls with the number 169 the
pin never fires; that is no theorem here (`seedsAt_pinned`, OnBytes/Tie/EntryAtRec.lean, says the
like for one pinned string). That the strings asked code no leaf and no vertex under a coding is not
said: the own-log form `three_arms_keyRead` asks it as a fourth premise (hKt), so this term is not
shown to fit that form. That the key file's three chains fit the table is another reading's matter
(KeyPre.lean): it parses the head once more, at the planner's own shape and digest, where this term
parses at sh and d's digest: that the two parses agree is not said here. Nothing on soundness.
Terms: lean/GLOSSARY.md.

-/
import OnBytes.Tie.Decl.PinPred
import OnBytes.Tie.EntryAskedCost
import OnBytes.Tie.LinkPlain
import OnBytes.Tie.AskX
import OnBytes.Slice.SeedsCost
import OnBytes.Slice.SeedsAtOracle
import OnBytes.Key.Table

set_option autoImplicit false

namespace OnBytes.Tie

open OnBytes.Params (TableName IndexShape)
open _root_.Iop (Dig)
open _root_.Run (digToBytes)

variable {D Out : Type} (Pt : List Bool → Prop) [DecidablePred Pt] (tab : D → List Bool → Dig 256)
  (cfgOf : D → Dig 256) (f : Fmt.Fld) (sh : IndexShape)
  (mk : TableName → List (List E × E) → Out)

/-- The seeds of the table t under the digest c, asked; then mk. -/
def seedsKR (c : ByteArray) (t : TableName) : Rom.OComp (Rom.rom 256) (Option Out) :=
  (Rom.toRom (seedsBy Run.askB f (Key.nameOf sh c t) sh.cubeBits sh.answers)).bind fun l =>
    .pure (l.map (mk t))

/-- **THE TERM.** -/
def preK (d : D) (uK : ByteArray) : Rom.OComp (Rom.rom 256) (Option Out) :=
  match Key.readTable sh (digToBytes (cfgOf d)) uK with
  | .error _ => .pure none
  | .ok x => pinP Pt (tab d) (seedsKR f sh mk (digToBytes (cfgOf d)) x.1)

theorem seedsKR_noCoin (c : ByteArray) (t : TableName) : (seedsKR f sh mk c t).NoCoin :=
  Rom.OComp.NoCoin.bind (noCoin_toRom _ (Slice.recordSeedsW_asks Run.askB qp_askB f _ _ _).1)
    fun _ => trivial

theorem seedsKR_asks (c : ByteArray) (t : TableName) :
    (seedsKR f sh mk c t).QueryBound (2 * Slice.seedCalls sh.cubeBits sh.answers + 1) := by
  have b : (seedsKR f sh mk c t).QueryBound (2 * Slice.seedCalls sh.cubeBits sh.answers + 1 + 0) :=
    Rom.OComp.QueryBound.bind
      ((Rom.queryBound_toRom _ _).2 (Slice.recordSeedsW_asks Run.askB qp_askB f _ _ _).2)
      fun _ => trivial
  exact b

theorem seedsKR_det (g : Rom.Fam (Rom.rom 256)) (c : ByteArray) (t : TableName) :
    (seedsKR f sh mk c t).det g =
      (seedsAt (Run.oB (g ())) f (Key.nameOf sh c t) sh.cubeBits sh.answers).map (mk t) := by
  unfold seedsKR
  rw [Rom.OComp.det_bind, ZKCP.OComp.det_toRom,
    seedsBy_det (g ()) Run.askB (Run.oB (g ())) (fun _ => rfl)]
  rfl

/-- **It tosses no coin.** NO HYPOTHESIS. -/
theorem preK_noCoin (d : D) (uK : ByteArray) : (preK Pt tab cfgOf f sh mk d uK).NoCoin := by
  unfold preK
  cases Key.readTable sh (digToBytes (cfgOf d)) uK with
  | error e => trivial
  | ok x => exact noCoin_pinP _ _ _ (seedsKR_noCoin f sh mk _ _)

/-- **It asks no public string.** NO HYPOTHESIS. -/
theorem preK_off (d : D) (uK : ByteArray) :
    (preK Pt tab cfgOf f sh mk d uK).AsksIn fun _ (s : List Bool) => ¬ Pt s := by
  unfold preK
  cases Key.readTable sh (digToBytes (cfgOf d)) uK with
  | error e => trivial
  | ok x => exact asksIn_pinP _ _ _

/-- **One number at every d and every file**: of the shape alone. NO HYPOTHESIS. -/
theorem preK_asks (d : D) (uK : ByteArray) :
    (preK Pt tab cfgOf f sh mk d uK).QueryBound
      (2 * Slice.seedCalls sh.cubeBits sh.answers + 1) := by
  unfold preK
  cases Key.readTable sh (digToBytes (cfgOf d)) uK with
  | error e => trivial
  | ok x => exact queryBound_pinP _ _ _ _ (seedsKR_asks f sh mk _ _)

/-- Where the parse refuses it asks nothing. -/
theorem preK_none (d : D) (uK : ByteArray) {e : Refusal}
    (h : Key.readTable sh (digToBytes (cfgOf d)) uK = .error e) :
    preK Pt tab cfgOf f sh mk d uK = .pure none := by
  unfold preK
  rw [h]

/-- Its value at every family. -/
theorem preK_det (g : Rom.Fam (Rom.rom 256)) (d : D) (uK : ByteArray) {t : TableName} {j : Nat}
    (h : Key.readTable sh (digToBytes (cfgOf d)) uK = .ok (t, j)) :
    (preK Pt tab cfgOf f sh mk d uK).det g =
      (seedsAt (Run.oB (overP Pt (tab d) g ())) f (Key.nameOf sh (digToBytes (cfgOf d)) t)
        sh.cubeBits sh.answers).map (mk t) := by
  unfold preK
  rw [h]
  show (pinP _ _ _).det g = _
  rw [det_pinP, seedsKR_det]

/-- **The tie's half.** At the oracle made from the format's hash: the table holds that oracle's own
values at every public string (hT); the table's root has 32 bytes. -/
theorem preK_program (d : D) (uK : ByteArray) {t : TableName} {j : Nat}
    (h : Key.readTable sh (digToBytes (cfgOf d)) uK = .ok (t, j))
    (hT : ∀ x, Pt x → tab d x = Run.oBits () x) (hr : t.root.size = 32) :
    (preK Pt tab cfgOf f sh mk d uK).det Run.oBits =
      (recordSeeds f (Key.nameOf sh (digToBytes (cfgOf d)) t) sh.cubeBits sh.answers).map
        (mk t) := by
  unfold preK
  rw [h]
  show (pinP _ _ _).det Run.oBits = _
  rw [det_pinP_of_eq _ _ _ hT, seedsKR_det, seedsAt_oBits]
  exact congrArg (Option.map (mk t))
    (Slice.recordSeedsW_oracle_table _ t.root _ hr (Run.size_digToBytes _) _ _ _ _ _ _ _ _)

end OnBytes.Tie
