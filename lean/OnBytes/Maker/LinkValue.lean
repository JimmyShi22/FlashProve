-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/LinkValue.lean: the link as data (OnBytes/Maker/Link.lean, `iorLink`) at the rounds
that the chain's parameter bytes give. Definitions alone; the laws are in
OnBytes/Maker/LinkValueLaws.lean.

The verifier program reads an entry file's chain under a description and judges it by a block
(`Tie.entrySpec`, OnBytes/Tie/EntryFile.lean). Both are made of the parameter bytes as read
(`Params.Link`) and of the two tables' names. A protocol as data has one shape for all instances. So
what gives the shape must not depend on the tables. `iorLink` leaves the rounds to its caller.

What the file contains.
  `linkRounds`: the rounds that the dry run of the link's block states at keys of zeros
    (`Params.entryRoundsAny`, OnBytes/Params/EntryRoundsRecord.lean); the empty list if the dry run
    fails.
  `linkSpec`: the description made of these rounds and the empty statement. `linkData p (linkRounds
    p)` is its form in the library.
  `linkDepth`: the depth of the first stored table that the description lists (0 if none); nothing
    says here that the others have it.
  `linkOk`: the test that the dry run at keys of zeros succeeds.
  `linkDecide`: the decision of the link's block at an instance, and a refusal where `linkOk` fails.
  `linkValue`: the reduction at these rounds and that decision. Where `linkOk` holds it is `iorLink`
    at `linkRounds`; where it fails it refuses everything (both in
    OnBytes/Maker/LinkValueLaws.lean). The tables' depth a is the caller's letter, as in `iorLink`;
    the program's own is `linkDepth p`.

What is not claimed. No law is stated here. Nothing says here that the dry run succeeds.
`linkDepth p` is 0 if the description opens no stored table; nothing says here that it is the depth
of the tables of any other file.


-/
import OnBytes.Maker.Link
import OnBytes.Params.EntryRoundsRecord

set_option autoImplicit false

namespace OnBytes.Maker

open Iop _root_.Run _root_.Run.PQ

/-- The rounds of an entry's chain, each with the stored trees that it opens: what the dry run of
the link's block states at keys of zeros. The empty list if that dry run fails. -/
def linkRounds (p : Params.Link) : Params.Rounds := (Params.entryRoundsAny p).getD []

/-- The description of an entry's chain with these rounds and the empty statement. -/
def linkSpec (p : Params.Link) : Fmt.SpecX := Params.entrySpecOf p (linkRounds p) ByteArray.empty

/-- The depth of the first stored table that the description lists (0 if none); nothing says here
that the others have it. -/
def linkDepth (p : Params.Link) : ℕ := (linkData p (linkRounds p)).a

/-- The dry run at keys of zeros succeeds. -/
def linkOk (p : Params.Link) : Bool := (Params.entryRoundsAny p).isSome

/-- The decision at a pair of records: that of the link's block; a refusal if the dry run at keys of
zeros fails. -/
def linkDecide {R : Type} (key : R → TableKey) (p : Params.Link) (rr : R × R) (v : View) : Bool :=
  linkOk p && (linkBlock key p rr).decides (Entry.start p) v

/-- **The link as data, at the rounds that the parameter bytes give.** C: the choice of the types of
verifier messages; a: the depth of the stored tables; R: the type of records; key: how a record is
written as the program's key of a table. -/
@[reducible] def linkValue {R : Type} (C : CK) (a : ℕ) (key : R → TableKey) (p : Params.Link) :
    IOR (R × R) (twoExternalStrings (2 ^ a) SgX) Unit extNone :=
  iorX C (linkData p (linkRounds p)).ds a (linkData p (linkRounds p)).xs (linkDecide key p)

end OnBytes.Maker
