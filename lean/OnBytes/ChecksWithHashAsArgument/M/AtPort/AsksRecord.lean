-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/ChecksWithHashAsArgument/M/AtPort/AsksRecord.lean: how many strings the twin's reading of an entry file asks,
as a closed expression of the description, and AS A NUMBER at the parameter bytes typed for the
full-size files of the setting "record with work".
The rounds of the link's block are the same at all keys that fit the shape and name the same items
(`linkDryBySizes`), so every description that the reading can make has the number of the
rounds at keys of zeros. These rounds hang on the link's shape and on the block's start alone
(`entryRoundsAny_congr`), and the start reads the plan's rounds and samples and the codes, not the
digest of the public files. The forms with `Rom.toRom` are those that a typing's two clauses ask.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.ChecksWithHashAsArgument.M.AtPort.Asks
import OnBytes.ChecksWithHashAsArgument.M.AtPort.Lands
import OnBytes.Params.EntryDescRecord
import OnBytes.Tie.AskX

set_option autoImplicit false

namespace OnBytes.TwoPort.M.AsksRecord

open _root_.Run
open OnBytes.Tie.CostX
open OnBytes.TwoPort.M.Asks
open OnBytes.Params (TableName)

/-- At all parameter bytes of a link's chain: if the dry run at keys of zeros states the rounds
r0, every description that the reading of an entry file can make has the number 3 + r0's. -/
theorem specsBelowFit_of_zero (p : Params.Link) (first : TableName) (r0 : Params.Rounds)
    (h0 : Params.entryRoundsAny p = some r0) : SpecsBelowFit p first (3 + roundsNX r0) := by
  intro further k0 k1 spec f0 f1 i0 i1 e
  obtain ⟨r, hr, hd⟩ := Option.bind_eq_some_iff.1 e
  have hsame := Params.linkDryBySizes p.link (OnBytes.Entry.start p) k0
    (Params.zeroKey p.link.table 0) k1 (Params.zeroKey p.link.table 1) f0
    (Params.zeroKey_fits _ _) f1 (Params.zeroKey_fits _ _) i0 i1
  have hr0 : r = r0 := by
    rw [hsame] at hr
    exact Option.some.inj (hr.symm.trans h0)
  subst hr0
  rw [fileNX_describeWith hd]

/-- The rounds at keys of zeros hang on the link's shape and on the block's start alone. -/
theorem entryRoundsAny_congr {p p' : Params.Link} (hl : p.link = p'.link)
    (hs : OnBytes.Entry.start p = OnBytes.Entry.start p') :
    Params.entryRoundsAny p = Params.entryRoundsAny p' := by
  unfold Params.entryRoundsAny
  rw [hl, hs]

/-- The strings that the reading of an entry file asks at most: a function of the tables' shape
and of the rounds alone. The factor 2 before the rounds' number is the second pass over a refused
chain; the last factor 2: one call of the hash asks at most two strings. -/
def entryT (s : Params.IndexShape) (r0 : Params.Rounds) : Nat :=
  (2 * RoadCost.keyN s + 2 * (3 + roundsNX r0)) * 2

/-- No coin, and at most `entryT` strings: at every first table and every file. -/
theorem entryRead_asks_zero (p : Params.Link) (first : TableName) (file : ByteArray)
    (r0 : Params.Rounds) (h0 : Params.entryRoundsAny p = some r0) :
    (M.Entry.read (Fmt.HM askB) p first file).NoCoin ∧
      (M.Entry.read (Fmt.HM askB) p first file).QueryBound (entryT p.link.table r0) :=
  AsksLands.entryRead_asksFit p first file _ (specsBelowFit_of_zero p first r0 h0)

/-- The same of the reading as a tree in the library's generic language. -/
theorem entryRead_rom (p : Params.Link) (first : TableName) (file : ByteArray)
    (r0 : Params.Rounds) (h0 : Params.entryRoundsAny p = some r0) :
    (Rom.toRom (M.Entry.read (Fmt.HM askB) p first file)).NoCoin ∧
      (Rom.toRom (M.Entry.read (Fmt.HM askB) p first file)).QueryBound
        (entryT p.link.table r0) :=
  Tie.toRom_out _ _ (entryRead_asks_zero p first file r0 h0)

/-- Its value at a family g with one oracle is the twin's at the identity monad and the hash that
g's function induces. -/
theorem entryRead_rom_det (g : Rom.Fam (Rom.rom 256)) (p : Params.Link) (first : TableName)
    (file : ByteArray) :
    (Rom.toRom (M.Entry.read (Fmt.HM askB) p first file)).det g =
      M.Entry.read (m := Id) (Fmt.HO (oB (g ()))) p first file := by
  rw [_root_.ZKCP.OComp.det_toRom, Lands.entryRead_det]

/-! ## The numbers at the full size -/

/-- The rounds' number at the full size. -/
theorem record_roundsNX : roundsNX Params.recordRounds = 10259 := by decide +kernel

/-- A key's number at the full size. -/
theorem record_keyN : RoadCost.keyN Params.recordRead.link.table = 72 := by decide +kernel

/-- At the full size: 41,336 strings. -/
theorem record_entryT : entryT Params.recordRead.link.table Params.recordRounds = 41336 := by
  unfold entryT
  rw [record_roundsNX, record_keyN]

/-- At the parameter bytes typed for the full size, at every first table and every file: no coin,
and at most 41,336 strings. -/
theorem record_entryRead_rom (first : TableName) (file : ByteArray) :
    (Rom.toRom (M.Entry.read (Fmt.HM askB) Params.recordRead first file)).NoCoin ∧
      (Rom.toRom (M.Entry.read (Fmt.HM askB) Params.recordRead first file)).QueryBound 41336 := by
  have e := entryRead_rom Params.recordRead first file Params.recordRounds Params.record_rounds
  rw [record_entryT] at e
  exact e

/-- The same at all parameter bytes with the typed ones' shape and start: so at every digest of the
public files. -/
theorem record_entryRead_rom_at (p : Params.Link) (hl : p.link = Params.recordRead.link)
    (hs : OnBytes.Entry.start p = OnBytes.Entry.start Params.recordRead) (first : TableName)
    (file : ByteArray) :
    (Rom.toRom (M.Entry.read (Fmt.HM askB) p first file)).NoCoin ∧
      (Rom.toRom (M.Entry.read (Fmt.HM askB) p first file)).QueryBound 41336 := by
  have e := entryRead_rom p first file Params.recordRounds
    ((entryRoundsAny_congr hl hs).trans Params.record_rounds)
  rw [hl, record_entryT] at e
  exact e

end OnBytes.TwoPort.M.AsksRecord
